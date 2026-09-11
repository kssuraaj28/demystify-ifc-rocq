From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Syntax Lattice4pt Attacker TypeSystem FullLattice.
Import Tacs Util VarValStore Lattice4pt Attacker TypeSystem FullLattice Tacs.Cook Nmif.Syntax. (* TODO: Why fully qualified? *)

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.


#[local] Notation Label := (FullLattice.Label).

(* An assignment from variables to labels *)
Class VarFullLblPrm `{!VarPrm, !PrincipalLatticePrm} := fvar_lbl : Vars -> Label.

Section ts.
  Context `{!VarPrm, !ValPrm, !PrincipalLatticePrm, !VarFullLblPrm}.
  Import FullLattice.Notations.

  Notation FullWellFormedProg' FullWellFormedCmd pclbl prog :=
    (Forall (FullWellFormedCmd pclbl) prog) (only parsing).

  Unset Elimination Schemes.
  Inductive FullWellFormedCmd : Label -> Cmd -> Prop :=
  | wff_output :
     forall pc out,
       pc ⊑ fvar_lbl out ->
       FullWellFormedCmd pc (output out)

  | wff_endorse :
     forall pc from to,
       conf (fvar_lbl from) = conf (fvar_lbl to) ->
       integ (fvar_lbl to) ≽ integ (fvar_lbl from) ->
       pc ⊑ fvar_lbl to ->
       uncompromised (fjoin (fvar_lbl from) pc) ->
       FullWellFormedCmd pc (assign (endorse from to))

  | wff_declassify :
     forall pc from to,
       integ (fvar_lbl from) = integ (fvar_lbl to) ->
       conf (fvar_lbl from) ≽ conf (fvar_lbl to) ->
       pc ⊑ fvar_lbl to ->
       uncompromised (fjoin (fvar_lbl from) pc) ->
       FullWellFormedCmd pc (assign (declassify from to))

  | wff_assign :
     forall dst src1 src2 comp pc,
       fvar_lbl src1 ⊑ fvar_lbl dst -> fvar_lbl src2 ⊑ fvar_lbl dst -> pc ⊑ fvar_lbl dst ->
       FullWellFormedCmd pc (assign (exp_assign (src1, src2, comp) dst))

  | wff_cond :
     forall gvar comp pc b1 b2,
       let: newpc := fvar_lbl gvar ⊔ pc in
       FullWellFormedProg' FullWellFormedCmd newpc b1 ->
       FullWellFormedProg' FullWellFormedCmd newpc b2 ->
       FullWellFormedCmd pc (cond (gvar, comp) b1 b2)

  | wff_while :
     forall gvar comp pc wbody,
       let: newpc := fvar_lbl gvar ⊔ pc in
       FullWellFormedProg' FullWellFormedCmd newpc wbody ->
       FullWellFormedCmd pc (while (gvar, comp) wbody).
  Set Elimination Schemes.

  Definition FullWellFormedProg pc prog := FullWellFormedProg' FullWellFormedCmd pc prog.

  Section ind.
    Variable Pr : Label -> Cmd -> Prop.

    Hypothesis hyp_output :
      forall pc v, (* A little more restrictive then necessary  *)
        pc ⊑ fvar_lbl v ->
        Pr pc (output v).

    Hypothesis hyp_endorse :
      forall pc from to,
        conf (fvar_lbl from) = conf (fvar_lbl to) ->
        integ (fvar_lbl to) ≽ integ (fvar_lbl from) ->
        pc ⊑ fvar_lbl to ->
        uncompromised (fjoin (fvar_lbl from) pc) ->
        Pr pc (assign (endorse from to)).

    Hypothesis hyp_declassify :
      forall pc from to,
        integ (fvar_lbl from) = integ (fvar_lbl to) ->
        conf (fvar_lbl from) ≽ conf (fvar_lbl to) ->
        pc ⊑ fvar_lbl to ->
        uncompromised (fjoin (fvar_lbl from) pc) ->
        Pr pc (assign (declassify from to)).

    Hypothesis hyp_assign :
      forall dst src1 src2 comp pc,
        fvar_lbl src1 ⊑ fvar_lbl dst -> fvar_lbl src2 ⊑ fvar_lbl dst -> pc ⊑ fvar_lbl dst ->
        Pr pc (assign (exp_assign (src1, src2, comp) dst)).

    Hypothesis hyp_cond :
      forall gvar comp pc b1 b2,
        let: newpc := fvar_lbl gvar ⊔ pc in
        Forall (FullWellFormedCmd newpc) b1 -> Forall (Pr newpc) b1 ->
        Forall (FullWellFormedCmd newpc) b2 -> Forall (Pr newpc) b2 ->
        Pr pc (cond (gvar, comp) b1 b2).

    Hypothesis hyp_while :
      forall gvar comp pc wbody,
        let: newpc := fvar_lbl gvar ⊔ pc in
        Forall (FullWellFormedCmd newpc) wbody -> Forall (Pr newpc) wbody ->
        Pr pc (while (gvar, comp) wbody).

    Fixpoint FullWellFormedCmd_ind:
      forall p c, (FullWellFormedCmd p c) -> Pr p c.
    Proof.
      move=> > []; [apply:hyp_output|apply:hyp_endorse|apply:hyp_declassify|apply:hyp_assign|..]=> *.
      1-2: (apply: hyp_cond; clear hyp_cond) || (apply: hyp_while; clear hyp_while)=>//.
      1-3: lazymatch goal with
             H: Forall _ ?b |- Forall _ ?b => elim: H=> // *
            end.
      1-3: constructor; auto; fail.
    Qed.
  End ind.

  Definition FullWellFormedOptCmd (pc : Label) (ocmd : option Cmd) : Prop :=
    if ocmd isn't Some cmd then True else FullWellFormedCmd pc cmd.

  Lemma fflows_to_subtype_cmd l1 c :
    FullWellFormedCmd l1 c -> forall l2, l2 ⊑ l1 -> FullWellFormedCmd l2 c.
  Proof.
    elim=> *; constructor; 
    try (apply:Forall_impl; [|eassumption]); 
    eauto using fjoin_mono_r, fflows_to_trans, uncompromised_anti; fail.
  Qed.

  (* The 4-point variable labelling induced by an attacker. *)
  Definition proj_adv (A : AttackerLabel) : AdvLvlPrm := fun v => to4pt A (fvar_lbl v).

  Lemma proj_adv_var (A : AttackerLabel) v : @var_lbl _ (proj_adv A) v = to4pt A (fvar_lbl v).
  Proof. done. Qed.

  (* A full typing derivation projects to a 4-point derivation for any attacker. *)
  Lemma full_to_4pt_cmd (A : AttackerLabel) pc c :
    FullWellFormedCmd pc c ->
    @WellFormedCmd _ _ (proj_adv A) (to4pt A pc) c.
  Proof.
    elim.
     1: move=> *;constructor; eauto using to4pt_mono.
     4,5: move=>*; constructor; apply: flows_to_subtype_prog; eauto using to4pt_join_le; fail.
     3: move=>*; constructor; rewrite /asgn_src_lbl /asgn_dst_lbl ?proj_adv_var ?join_flow; (apply/andP + idtac); eauto using to4pt_mono; fail.
     
    - (* endorse *)
      move=> pc' from to Hce _ Hpcto Hunc.
      case Hfl: ([elaborate flows_to (to4pt A (fvar_lbl from)) (to4pt A (fvar_lbl to))]).
        { constructor; eauto using to4pt_mono. }
      move: (to4pt_endorse_canonical A (fvar_lbl from) (fvar_lbl to) Hce
               (uncompromised_join_l _ _ Hunc) (negbT Hfl)) => [Hfrom4 Hto4].
      pattern_eq [to4pt _ _] with ptlbl=> [|->]; eauto using flows_to_pt,to4pt_mono with trickbag.
      constructor; done.
    - (* declassify *)
      move=> pc' from to Hie _ Hpcto Hunc.
      case Hfl: ([elaborate flows_to (to4pt A (fvar_lbl from)) (to4pt A (fvar_lbl to))]).
        { constructor; eauto using to4pt_mono. }
      move: (to4pt_declassify_canonical A (fvar_lbl from) (fvar_lbl to) Hie
               (uncompromised_join_l _ _ Hunc) (negbT Hfl)) => [Hfrom4 Hto4].
      pattern_eq [to4pt _ _] with ptlbl=> [|->]; eauto using flows_to_pt,to4pt_mono with trickbag.
      constructor; done.
  Qed.

  Lemma full_to_4pt_prog (A : AttackerLabel) pc p :
    FullWellFormedProg pc p -> @WellFormedProg _ _ (proj_adv A) (to4pt A pc) p.
  Proof. apply: Forall_impl. exact: full_to_4pt_cmd. Qed.


  Definition full_public_trusted := (topP , botP).

  Lemma fullpt_is_pt A:
    to4pt A full_public_trusted = ptlbl.
  Proof.
    rewrite/to4pt /= leqP_top. Util.local_cook.
    apply/negP=> /leqreverse [].
      { rewrite leqP_bot //. }
    apply: atk_notop; eauto.
  Qed.

End ts.
