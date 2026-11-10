From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Syntax FullLattice FullTypeSystem.
Import Util VarValStore FullLattice FullTypeSystem Nmif.Syntax.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Notation Label := (FullLattice.Label).

Section tc.
  Context `{!VarPrm, !ValPrm, !PrincipalLatticePrm, !VarFullLblPrm}.
  Import FullLattice.Notations Util.List.

  Definition full_tc_downgrade (pc : Label) (from to : Vars) : bool :=
    (pc ⊑ fvar_lbl to) && uncompromised (fjoin (fvar_lbl from) pc).

  Fixpoint full_tc_cmd (pc : Label) (c : Cmd) : bool :=
    match c with
    | output out => pc ⊑ fvar_lbl out
    | assign (endorse from to) =>
        eqP (conf (fvar_lbl from)) (conf (fvar_lbl to)) &&
        (integ (fvar_lbl to) ≽ integ (fvar_lbl from)) &&
        full_tc_downgrade pc from to
    | assign (declassify from to) =>
        eqP (integ (fvar_lbl from)) (integ (fvar_lbl to)) &&
        (conf (fvar_lbl from) ≽ conf (fvar_lbl to)) &&
        full_tc_downgrade pc from to
    | assign (exp_assign (src1, src2, _) dst) =>
        (fvar_lbl src1 ⊑ fvar_lbl dst) && (fvar_lbl src2 ⊑ fvar_lbl dst) &&
        (pc ⊑ fvar_lbl dst)
    | cond (gvar, _) b1 b2 =>
        let newpc := fvar_lbl gvar ⊔ pc in
        forallb (full_tc_cmd newpc) b1 && forallb (full_tc_cmd newpc) b2
    | while (gvar, _) b =>
        let newpc := fvar_lbl gvar ⊔ pc in
        forallb (full_tc_cmd newpc) b
    end.


  Definition full_tc_prog (pc : Label) (p : Prog) : bool :=
    forallb (full_tc_cmd pc) p.

  Lemma full_tc_cmd_iff c pc : full_tc_cmd pc c <-> FullWellFormedCmd pc c.
  Proof.
    elim: c pc=> [v | a | b1 b2 [g cmp] IH1 IH2 | b [g cmp] IH] pc /=.
    - split=> [|Hw]; [constructor; done|inversion Hw; done].
    - case: a=> [from to | from to | [[s1 s2] cmp] dst];
      rewrite /full_tc_downgrade; split.
      + move=> /andP[/andP[/eqPP ? ?] /andP[? ?]]; constructor; done.
      + move=> Hw; inversion Hw; subst; apply/andP; split;
           [apply/andP; split; [apply/eqPP|]|apply/andP; split]; done.
      + move=> /andP[/andP[/eqPP ? ?] /andP[? ?]]; constructor; done.
      + move=> Hw; inversion Hw; subst; apply/andP; split;
           [apply/andP; split; [apply/eqPP|]|apply/andP; split]; done.
      + move=> /andP[/andP[? ?] ?]; constructor; done.
      + move=> Hw; inversion Hw; subst; apply/andP; split; [apply/andP; split|]; done.
    - split.
      + move=> /andP[/forallbP Hb1 /forallbP Hb2].
        constructor; [move: (Forall_and IH1 Hb1)|move: (Forall_and IH2 Hb2)];
        apply: Forall_impl=> c [/(_ (fvar_lbl g ⊔ pc)) H ?]; exact/H.
      + move=> Hw; inversion_clear Hw as [| | | |? ? ? ? ? Hb1 Hb2|].
        apply/andP; split; Util.List.local_cook;
        [move: (Forall_and IH1 Hb1)|move: (Forall_and IH2 Hb2)];
        apply: Forall_impl=> c [/(_ (fvar_lbl g ⊔ pc)) H ?]; exact/H.
    - split.
      + move=> /forallbP Hb.
        constructor; move: (Forall_and IH Hb).
        apply: Forall_impl=> c [/(_ (fvar_lbl g ⊔ pc)) H ?]; exact/H.
      + move=> Hw; inversion_clear Hw as [| | | | |? ? ? ? Hb].
        Util.List.local_cook; move: (Forall_and IH Hb).
        apply: Forall_impl=> c [/(_ (fvar_lbl g ⊔ pc)) H ?]; exact/H.
  Qed.

  Lemma full_tc_cmdP pc c : reflect (FullWellFormedCmd pc c) (full_tc_cmd pc c).
  Proof. apply: (iffP idP)=> H; apply/full_tc_cmd_iff; exact: H. Qed.

  Lemma full_tc_progP pc p : reflect (FullWellFormedProg pc p) (full_tc_prog pc p).
  Proof.
    rewrite /full_tc_prog /FullWellFormedProg.
    apply: (iffP idP)=> [/forallbP|H]; [|apply/forallbP; move: H];
    apply: Forall_impl=> c /full_tc_cmd_iff //.
  Qed.

  Corollary full_tc_prog_sound pc p : full_tc_prog pc p -> FullWellFormedProg pc p.
  Proof. move/full_tc_progP; done. Qed.

  Corollary full_tc_prog_complete pc p : FullWellFormedProg pc p -> full_tc_prog pc p.
  Proof. move/full_tc_progP; done. Qed.
End tc.
