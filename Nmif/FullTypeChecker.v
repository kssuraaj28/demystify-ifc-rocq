From Stdlib Require List ssreflect ssrfun ssrbool Strings.String.
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
    - split; [constructor | move=> x; inversion x]; done.
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
        apply: Forall_impl=> c  [/(_ (fvar_lbl g ⊔ pc)) H ?]; exact/H.
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

Module AuctionExample.

  (* The principals *)
  Variant Prin := auctioneer | alice | bob | any.

  Definition prin_leq (x y : Prin) : bool :=
    match x, y with
    | auctioneer, _ => true
    | _, any => true
    | alice, alice | bob, bob => true
    | _, _ => false
    end.

  Definition prin_meet (x y : Prin) : Prin :=
    match x, y with
    | any, z | z, any => z
    | alice, alice => alice
    | bob, bob => bob
    | _, _ => auctioneer
    end.

  Definition prin_join (x y : Prin) : Prin :=
    match x, y with
    | auctioneer, z | z, auctioneer => z
    | alice, alice => alice
    | bob, bob => bob
    | _, _ => any
    end.

  #[refine, local] Instance auction_plat : PrincipalLatticePrm :=
    {| P := Prin; leqP := prin_leq; meetP := prin_meet; joinP := prin_join;
       topP := any; botP := auctioneer |}.
  Proof.
    1-7: do ! (move=> // []).
  Defined.

  Variant Var := alice_bid | bob_bid | alice_c | bob_c | ret | ret_pub.

  #[refine, local] Instance auction_vars : VarPrm := {| Vars := Var |}.
  Proof. constructor; rewrite /decidable; decide equality. Defined.

  Import Stdlib.Strings.String.
  #[local] Open Scope string_scope.

  Variant Val := num (_ : nat) | str (_ : string).

  #[local] Instance auction_vals : ValPrm := {| Vals := Val; val_ne := num 0 |}.

  Definition decide_winner (abid bbid : Val) : Val :=
    str (match abid, bbid  with
    | num a, num b =>
        match Nat.compare a b with
        | Gt => "Alice wins"
        | Lt => "Bob wins"
        | Eq => "Tie"
        end
    | _, _ => "Invalid bids"
    end).

  Definition auction : Prog :=
    [ assign (endorse alice_bid alice_c);
      assign (endorse bob_bid bob_c);
      assign (exp_assign (alice_c, bob_c, decide_winner) ret);
      assign (declassify ret ret_pub);
      output ret_pub ].

  (* Labels as (confidentiality, integrity). *)
  Section secure.
    Instance secure_lbling : VarFullLblPrm := fun v =>
      match v with
      | alice_bid => (alice, alice)
      | bob_bid   => (bob, bob)
      | alice_c   => (alice, auctioneer)
      | bob_c     => (bob, auctioneer)
      | ret       => (auctioneer, auctioneer)
      | ret_pub   => (any, auctioneer)
      end.

    Example secure_typechecks :
      full_tc_prog full_public_trusted auction = true.
    Proof. done. Qed.
  End secure.

  Section insecure.
    Instance insecure_lbling : VarFullLblPrm := fun v =>
      match v with
      | alice_bid => (auctioneer, alice)
      | alice_c   => (auctioneer, auctioneer)
      | _ => secure_lbling v
      end.

    Example insecure_fails :
      full_tc_prog full_public_trusted auction = false.
    Proof. done. Qed.
  End insecure.
End AuctionExample.
