From Stdlib Require List ssreflect.
Import List ListNotations ssreflect.

Require VarValStore Tacs.
Import VarValStore.

Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section syntax.
  Context `{!VarPrm, !ValPrm}.

  Section cmd.
    Notation Prog' Cmd := (list Cmd) (only parsing).

    Unset Elimination Schemes. 
    Inductive Cmd :=
      | assign (comp : Store -> Store)
      | cond (tst: Store -> bool) (b1 b2: Prog' Cmd)
      | while (tst: Store -> bool) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

    Hypothesis hyp_skip : 
      `(P (skip)).

    Hypothesis hyp_assign : 
      `(P (assign comp)).

    Hypothesis hyp_cond : 
      `(Forall P b1 ->
        Forall P b2 ->
        P (cond tst b1 b2)).

    Hypothesis hyp_while : 
      `(Forall P b ->
        P (while tst b)).


    Fixpoint Cmd_ind : forall c, P c. 
    Proof.
      case=> >;
        apply: hyp_skip + apply: hyp_assign + apply: hyp_cond + apply: hyp_while;
        lazymatch goal with |- Forall _ ?l => elim: l end;
        auto.
    Qed.
  End cmd_ind.
End syntax.
