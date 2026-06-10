From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Syntax Lattice4pt Attacker TypeSystem FullLattice.
Import Tacs Util VarValStore Lattice4pt Attacker TypeSystem FullLattice Tacs.Cook.
(* Qualified: requiring TypeSystem transitively loads a Stdlib module named
   Syntax, which otherwise shadows the short name and hides Cmd. *)
Import Nmif.Syntax.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

(* Each variable carries a full label (c, i) ∈ P × P; attacker-independent. *)
Class VarFullLblPrm `{!VarPrm, !PrincipalLatticePrm} := fvar_lbl : Vars -> FLabel.

Section ts.
  Context `{!VarPrm, !ValPrm, !PrincipalLatticePrm, !VarFullLblPrm}.
  Import FullLattice.Notations.

  Notation FullWellFormedProg' FullWellFormedCmd pclbl prog :=
    (Forall (FullWellFormedCmd pclbl) prog) (only parsing).

  (* Information-flow type system over the full lattice. Downgrade rules are
     attacker-independent: endorse keeps confidentiality and raises integrity,
     declassify keeps integrity and lowers confidentiality, and both require the
     source-with-pc join to be uncompromised (robust). The pc is general. *)
  Unset Elimination Schemes.
  Inductive FullWellFormedCmd : FLabel -> Cmd -> Prop :=
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
    Variable Pr : FLabel -> Cmd -> Prop.

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

    Fixpoint FullWellFormedCmd_ind p c (H : FullWellFormedCmd p c) {struct H} : Pr p c.
    Proof.
      case: H.
      - exact: hyp_endorse.
      - exact: hyp_declassify.
      - exact: hyp_assign.
      - move=> gvar comp pc b1 b2 H1 H2.
        apply: hyp_cond.
        + exact: H1.
        + elim: H1 => // *; constructor 2 => //; auto.
        + exact: H2.
        + elim: H2 => // *; constructor 2 => //; auto.
      - move=> gvar comp pc wbody H1.
        apply: hyp_while.
        + exact: H1.
        + elim: H1 => // *; constructor 2 => //; auto.
    Qed.
  End ind.

  Definition FullWellFormedOptCmd (pc : FLabel) (ocmd : option Cmd) : Prop :=
    if ocmd isn't Some cmd then True else FullWellFormedCmd pc cmd.

  (* Subtyping: a lower pc is always safe. *)
  Lemma fflows_to_subtype_cmd l1 c :
    FullWellFormedCmd l1 c -> forall l2, l2 ⊑ l1 -> FullWellFormedCmd l2 c.
  Proof.
    move=> H; elim/FullWellFormedCmd_ind: H.
    - move=> pc from to Hce Hi Hpcto Hu l2 Hl2.
      apply: wff_endorse;
        [exact: Hce | exact: Hi | exact: (fflows_to_trans _ _ _ Hl2 Hpcto)
        | exact: (uncompromised_anti _ _ _ Hl2 Hu)].
    - move=> pc from to Hie Hcl Hpcto Hu l2 Hl2.
      apply: wff_declassify;
        [exact: Hie | exact: Hcl | exact: (fflows_to_trans _ _ _ Hl2 Hpcto)
        | exact: (uncompromised_anti _ _ _ Hl2 Hu)].
    - move=> dst src1 src2 comp pc Hs1 Hs2 Hpc l2 Hl2.
      apply: wff_assign; [exact: Hs1 | exact: Hs2 | exact: (fflows_to_trans _ _ _ Hl2 Hpc)].
    - move=> gvar comp pc b1 b2 _ IH1 _ IH2 l2 Hl2. apply: wff_cond.
      + move: IH1; apply/Forall_impl => co Hco. exact: (Hco _ (fjoin_mono_r _ _ _ Hl2)).
      + move: IH2; apply/Forall_impl => co Hco. exact: (Hco _ (fjoin_mono_r _ _ _ Hl2)).
    - move=> gvar comp pc wbody _ IH l2 Hl2. apply: wff_while.
      + move: IH; apply/Forall_impl => co Hco. exact: (Hco _ (fjoin_mono_r _ _ _ Hl2)).
  Qed.

  (* The 4-point variable labelling induced by an attacker. *)
  Definition proj_adv (A : AttackerLabel) : AdvLvlPrm := fun v => to4pt A (fvar_lbl v).

  Lemma proj_adv_var (A : AttackerLabel) v : @var_lbl _ (proj_adv A) v = to4pt A (fvar_lbl v).
  Proof. exact: erefl. Qed.

  (* A full typing derivation projects to a 4-point derivation for any attacker. *)
  Theorem full_to_4pt_cmd (A : AttackerLabel) pc c :
    FullWellFormedCmd pc c ->
    @WellFormedCmd _ _ (proj_adv A) (to4pt A pc) c.
  Proof.
    move=> H; elim/FullWellFormedCmd_ind: H.
    - (* endorse *)
      move=> pc' from to Hce _ Hpcto Hunc.
      case Hfl: ([elaborate flows_to (to4pt A (fvar_lbl from)) (to4pt A (fvar_lbl to))]).
      + (* harmless: from ⊑ to in the projection, an ordinary assignment flow *)
        apply: wf_assign; rewrite /asgn_src_lbl /asgn_dst_lbl /=;
          [exact: Hfl | exact: (to4pt_mono _ _ _ Hpcto)].
      + (* canonical PU→PT, pc forced to PT *)
        move: (to4pt_endorse_canonical A (fvar_lbl from) (fvar_lbl to) Hce
                 (uncompromised_join_l _ _ Hunc) (negbT Hfl)) => [Hfrom4 Hto4].
        have Hpc4 : to4pt A pc' = mk_lbl false true.
        { apply: flows_to_pt. rewrite -Hto4. exact: (to4pt_mono _ _ _ Hpcto). }
        rewrite Hpc4. apply: wf_endorse; rewrite proj_adv_var; [exact: Hfrom4 | exact: Hto4].
    - (* declassify *)
      move=> pc' from to Hie _ Hpcto Hunc.
      case Hfl: ([elaborate flows_to (to4pt A (fvar_lbl from)) (to4pt A (fvar_lbl to))]).
      + (* harmless: an ordinary assignment flow *)
        apply: wf_assign; rewrite /asgn_src_lbl /asgn_dst_lbl /=;
          [exact: Hfl | exact: (to4pt_mono _ _ _ Hpcto)].
      + (* canonical ST→PT, pc forced to PT *)
        move: (to4pt_declassify_canonical A (fvar_lbl from) (fvar_lbl to) Hie
                 (uncompromised_join_l _ _ Hunc) (negbT Hfl)) => [Hfrom4 Hto4].
        have Hpc4 : to4pt A pc' = mk_lbl false true.
        { apply: flows_to_pt. rewrite -Hto4. exact: (to4pt_mono _ _ _ Hpcto). }
        rewrite Hpc4. apply: wf_declassify; rewrite proj_adv_var; [exact: Hfrom4 | exact: Hto4].
    - (* assign: the generalized wf_assign splits into a source-join flow and a pc flow *)
      move=> dst src1 src2 comp pc' Hs1 Hs2 Hpc.
      apply: wf_assign.
      + rewrite /asgn_src_lbl /asgn_dst_lbl !proj_adv_var join_flow; apply/andP; split;
          [exact: (to4pt_mono _ _ _ Hs1) | exact: (to4pt_mono _ _ _ Hs2)].
      + rewrite /asgn_dst_lbl !proj_adv_var; exact: (to4pt_mono _ _ _ Hpc).
    - (* cond *)
      move=> gvar comp pc' b1 b2 _ IH1 _ IH2.
      apply: wf_cond.
      + apply: (flows_to_subtype_prog _ _ _ (to4pt_join_le A (fvar_lbl gvar) pc')); exact: IH1.
      + apply: (flows_to_subtype_prog _ _ _ (to4pt_join_le A (fvar_lbl gvar) pc')); exact: IH2.
    - (* while *)
      move=> gvar comp pc' wbody _ IH.
      apply: wf_while.
      apply: (flows_to_subtype_prog _ _ _ (to4pt_join_le A (fvar_lbl gvar) pc')); exact: IH.
  Qed.

  Theorem full_to_4pt_prog (A : AttackerLabel) pc p :
    FullWellFormedProg pc p ->
    @WellFormedProg _ _ (proj_adv A) (to4pt A pc) p.
  Proof.
    rewrite /FullWellFormedProg /WellFormedProg.
    apply/Forall_impl => c. exact: (full_to_4pt_cmd A pc c).
  Qed.

  Theorem full_to_4pt_optcmd (A : AttackerLabel) pc oc :
    FullWellFormedOptCmd pc oc ->
    @WellFormedOptCmd _ _ (proj_adv A) (to4pt A pc) oc.
  Proof.
    rewrite /FullWellFormedOptCmd /WellFormedOptCmd.
    case: oc => [c|] //=. exact: (full_to_4pt_cmd A pc c).
  Qed.
End ts.

