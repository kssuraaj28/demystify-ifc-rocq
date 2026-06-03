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


(* A small modus-ponens combinator over Forall, used to push the per-element
   translation through a list. *)
(* TODO: I think that there is a stdlib thing for this *)
Lemma Forall_modus {X} {f g : X -> Prop} {l} :
  Forall (fun x => f x -> g x) l -> Forall f l -> Forall g l.
Proof.
  move=> Hfg Hf; elim: Hfg Hf => [|x xs Hxfg Hrest IH] Hf.
  - constructor.
  - constructor.
    + exact: Hxfg (Forall_inv Hf).
    + exact: IH (Forall_inv_tail Hf).
Qed.

(* Each variable carries a full label (c, i) ∈ P × P; attacker-independent. *)
(* TODO: This name is wrong. Should be VarFullLblPrm *)
Class FullAdvLvlPrm `{!VarPrm, !PrincipalLatticePrm} := fvar_lbl : Vars -> FLabel.

Section ts.
  Context `{!VarPrm, !ValPrm, !PrincipalLatticePrm, !FullAdvLvlPrm}.
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
       leqP (integ (fvar_lbl to)) (integ (fvar_lbl from)) ->
       uncompromised (fjoin (fvar_lbl from) pc) ->
       FullWellFormedCmd pc (assign (endorse from to))

  | wff_declassify :
     forall pc from to,
       integ (fvar_lbl from) = integ (fvar_lbl to) ->
       leqP (conf (fvar_lbl from)) (conf (fvar_lbl to)) ->
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
        leqP (integ (fvar_lbl to)) (integ (fvar_lbl from)) ->
        uncompromised (fjoin (fvar_lbl from) pc) ->
        Pr pc (assign (endorse from to)).

    Hypothesis hyp_declassify :
      forall pc from to,
        integ (fvar_lbl from) = integ (fvar_lbl to) ->
        leqP (conf (fvar_lbl from)) (conf (fvar_lbl to)) ->
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
    - move=> pc from to Hce Hi Hu l2 Hl2.
      apply: wff_endorse; [exact: Hce | exact: Hi | exact: (uncompromised_anti _ _ _ Hl2 Hu)].
    - move=> pc from to Hie Hcl Hu l2 Hl2.
      apply: wff_declassify; [exact: Hie | exact: Hcl | exact: (uncompromised_anti _ _ _ Hl2 Hu)].
    - move=> dst src1 src2 comp pc Hs1 Hs2 Hpc l2 Hl2.
      apply: wff_assign; [exact: Hs1 | exact: Hs2 | exact: (fflows_to_trans _ _ _ Hl2 Hpc)].
    - move=> gvar comp pc b1 b2 _ IH1 _ IH2 l2 Hl2. apply: wff_cond.
      + move: IH1; apply/Forall_impl => co Hco. exact: (Hco _ (fjoin_mono_r _ _ _ Hl2)).
      + move: IH2; apply/Forall_impl => co Hco. exact: (Hco _ (fjoin_mono_r _ _ _ Hl2)).
    - move=> gvar comp pc wbody _ IH l2 Hl2. apply: wff_while.
      + move: IH; apply/Forall_impl => co Hco. exact: (Hco _ (fjoin_mono_r _ _ _ Hl2)).
  Qed.

(* TODO: Not used anywhere *)
  Lemma fflows_to_subtype_prog p l1 l2 :
    l2 ⊑ l1 -> FullWellFormedProg l1 p -> FullWellFormedProg l2 p.
  Proof.
    rewrite /FullWellFormedProg => Hl2. apply/Forall_impl => co Hco.
    exact: (fflows_to_subtype_cmd _ _ Hco _ Hl2).
  Qed.

  (* TODO: This does not look like what we want.   I have no idea what this means  *)
  (* Per-attacker compatibility: the side conditions needed so that the
     projection of a full derivation lands on valid 4-point points. Indexed by
     pc, threaded like the type system. *)
  Inductive AtkCompat (A : Attacker) : FLabel -> Cmd -> Prop :=
  | compat_endorse :
     forall pc from to,
       to4pt A pc = mk_lbl false true ->
       leqP (atk_c A) (conf (fvar_lbl from)) ->
       leqP (atk_i A) (integ (fvar_lbl from)) ->
       ~~ leqP (atk_i A) (integ (fvar_lbl to)) ->
       AtkCompat A pc (assign (endorse from to))
  | compat_declassify :
     forall pc from to,
       to4pt A pc = mk_lbl false true ->
       ~~ leqP (atk_c A) (conf (fvar_lbl from)) ->
       ~~ leqP (atk_i A) (integ (fvar_lbl from)) ->
       leqP (atk_c A) (conf (fvar_lbl to)) ->
       AtkCompat A pc (assign (declassify from to))
  | compat_exp :
     forall pc e d, AtkCompat A pc (assign (exp_assign e d))
  | compat_cond :
     forall pc gvar comp b1 b2,
       let: newpc := fjoin (fvar_lbl gvar) pc in
       Forall (AtkCompat A newpc) b1 -> Forall (AtkCompat A newpc) b2 ->
       AtkCompat A pc (cond (gvar, comp) b1 b2)
  | compat_while :
     forall pc gvar comp wbody,
       let: newpc := fjoin (fvar_lbl gvar) pc in
       Forall (AtkCompat A newpc) wbody ->
       AtkCompat A pc (while (gvar, comp) wbody).

  Lemma AtkCompat_endorse_inv A pc from to :
    AtkCompat A pc (assign (endorse from to)) ->
    to4pt A pc = mk_lbl false true /\
    leqP (atk_c A) (conf (fvar_lbl from)) /\
    leqP (atk_i A) (integ (fvar_lbl from)) /\
    ~~ leqP (atk_i A) (integ (fvar_lbl to)).
  Proof. inversion 1; subst; tauto. Qed.

  Lemma AtkCompat_declassify_inv A pc from to :
    AtkCompat A pc (assign (declassify from to)) ->
    to4pt A pc = mk_lbl false true /\
    ~~ leqP (atk_c A) (conf (fvar_lbl from)) /\
    ~~ leqP (atk_i A) (integ (fvar_lbl from)) /\
    leqP (atk_c A) (conf (fvar_lbl to)).
  Proof. inversion 1; subst; tauto. Qed.

  Lemma AtkCompat_cond_inv A pc gvar comp b1 b2 :
    AtkCompat A pc (cond (gvar, comp) b1 b2) ->
    Forall (AtkCompat A (fjoin (fvar_lbl gvar) pc)) b1 /\
    Forall (AtkCompat A (fjoin (fvar_lbl gvar) pc)) b2.
  Proof. inversion 1; subst; tauto. Qed.

  Lemma AtkCompat_while_inv A pc gvar comp wbody :
    AtkCompat A pc (while (gvar, comp) wbody) ->
    Forall (AtkCompat A (fjoin (fvar_lbl gvar) pc)) wbody.
  Proof. inversion 1; subst; tauto. Qed.

  (* The 4-point variable labelling induced by an attacker. *)
  Definition proj_adv (A : Attacker) : AdvLvlPrm := fun v => to4pt A (fvar_lbl v).

  Lemma proj_adv_var (A : Attacker) v : @var_lbl _ (proj_adv A) v = to4pt A (fvar_lbl v).
  Proof. exact: erefl. Qed.

  (* Headline result: a full typing derivation, for any compatible attacker,
     projects to a 4-point derivation. *)
  Theorem full_to_4pt_cmd (A : Attacker) pc c :
    FullWellFormedCmd pc c -> AtkCompat A pc c ->
    @WellFormedCmd _ _ (proj_adv A) (to4pt A pc) c.
  Proof.
    move=> H; elim/FullWellFormedCmd_ind: H.
    - (* endorse *)
      move=> pc' from to Hce _ _ /AtkCompat_endorse_inv [Hpc [Hfpub [Hfuntr Htotr]]].
      rewrite Hpc. apply: wf_endorse.
      + rewrite proj_adv_var /to4pt Hfuntr Hfpub //.
      + rewrite proj_adv_var /to4pt (negbTE Htotr) -Hce Hfpub //.
    - (* declassify *)
      move=> pc' from to Hie _ _ /AtkCompat_declassify_inv [Hpc [Hfsec [Hftr Htopub]]].
      rewrite Hpc. apply: wf_declassify.
      + rewrite proj_adv_var /to4pt (negbTE Hftr) (negbTE Hfsec) //.
      + rewrite proj_adv_var /to4pt -Hie (negbTE Hftr) Htopub //.
    - (* assign *)
      move=> dst src1 src2 comp pc' Hs1 Hs2 Hpc _.
      apply: wf_assign; rewrite !proj_adv_var.
      + exact: (to4pt_mono _ _ _ Hs1).
      + exact: (to4pt_mono _ _ _ Hs2).
      + exact: (to4pt_mono _ _ _ Hpc).
    - (* cond *)
      move=> gvar comp pc' b1 b2 _ IH1 _ IH2 /AtkCompat_cond_inv [C1 C2].
      apply: wf_cond.
      + apply: (flows_to_subtype_prog _ _ _ (to4pt_join_le A (fvar_lbl gvar) pc')).
        exact: (Forall_modus IH1 C1).
      + apply: (flows_to_subtype_prog _ _ _ (to4pt_join_le A (fvar_lbl gvar) pc')).
        exact: (Forall_modus IH2 C2).
    - (* while *)
      move=> gvar comp pc' wbody _ IH /AtkCompat_while_inv C.
      apply: wf_while.
      apply: (flows_to_subtype_prog _ _ _ (to4pt_join_le A (fvar_lbl gvar) pc')).
      exact: (Forall_modus IH C).
  Qed.

  Theorem full_to_4pt_prog (A : Attacker) pc p :
    FullWellFormedProg pc p -> Forall (AtkCompat A pc) p ->
    @WellFormedProg _ _ (proj_adv A) (to4pt A pc) p.
  Proof.
    rewrite /FullWellFormedProg /WellFormedProg => Hwf Hc.
    apply: (Forall_modus _ Hc).
    apply/Forall_impl; [| exact: Hwf].
    move=> c Hc'. exact: (full_to_4pt_cmd A pc c Hc').
  Qed.

  Theorem full_to_4pt_optcmd (A : Attacker) pc oc :
    FullWellFormedOptCmd pc oc -> (if oc is Some c then AtkCompat A pc c else True) ->
    @WellFormedOptCmd _ _ (proj_adv A) (to4pt A pc) oc.
  Proof.
    rewrite /FullWellFormedOptCmd /WellFormedOptCmd.
    case: oc => [c|] //=. exact: (full_to_4pt_cmd A pc c).
  Qed.
End ts.

