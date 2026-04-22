From Stdlib Require List ssreflect.
Import List ListNotations ssreflect.

Require VarValStore Tacs.
Import VarValStore.

Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section syntax.
  Context `{!VarPrm, !ValPrm}.

  Definition ValExp : Type := 
    Vars * Vars * (Vals -> Vals -> Vals).

  Definition BoolExp : Type := 
    Vars * (Vals -> bool).

  Section cmd.
    Notation Prog' Cmd := (list Cmd) (only parsing).

    Unset Elimination Schemes.
    Inductive Cmd :=
      | assign (dst : Vars) (exp: ValExp)
      | cond (exp: BoolExp) (b1 b2: Prog' Cmd)
      | while (exp: BoolExp) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

    Hypothesis hyp_assign : 
      `(P (assign dst exp)).

    Hypothesis hyp_cond : 
      `(Forall P b1 ->
        Forall P b2 ->
        P (cond exp b1 b2)).

    Hypothesis hyp_while : 
      `(Forall P b ->
        P (while exp b)).


    Fixpoint Cmd_ind : forall c, P c. 
    Proof.
      case=> >.
      all:  apply: hyp_assign || apply: hyp_while || apply: hyp_cond.
      all:  lazymatch goal with |- Forall _ ?l => elim: l end.
      all:  auto.
    Qed.
  End cmd_ind.
End syntax.
