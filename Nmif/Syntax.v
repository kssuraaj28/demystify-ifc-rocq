From Stdlib Require List ssreflect ssrbool ssrfun.
Import List ListNotations ssreflect ssrbool ssrfun.

From Ltac2 Require Import Ltac2.
Require VarValStore Tacs.
Import VarValStore Tacs Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section syntax.
  Context `{!VarPrm, !ValPrm}.

  Definition ValExp : Type := 
    Vars * Vars * (Vals -> Vals -> Vals).

  Definition BoolExp : Type := 
    Vars * (Vals -> bool).
  
  Variant Assignment :=
  | endorse (src dst : Vars)
  | declassify (src dst : Vars)
  | exp_assign (exp: ValExp) (dst : Vars).


  Section cmd.
    Notation Prog' Cmd := (list Cmd) (only parsing).

    Unset Elimination Schemes.
    Inductive Cmd :=
      | output (v: Vars)
      | assign (_ : Assignment)
      | cond (exp: BoolExp) (b1 b2: Prog' Cmd)
      | while (exp: BoolExp) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

    Hypothesis hyp_output : 
      `(P (output v)).

    Hypothesis hyp_assign : 
      `(P (assign ass)).

    Hypothesis hyp_cond : 
      `(Forall P b1 ->
        Forall P b2 ->
        P (cond exp b1 b2)).

    Hypothesis hyp_while : 
      `(Forall P b ->
        P (while exp b)).


    Fixpoint Cmd_ind : forall c, P c. 
    Proof.
      case=> >; [apply: hyp_output| apply: hyp_assign| apply: hyp_cond | apply: hyp_while].
      1-3:  lazymatch goal with |- Forall _ ?l => elim: l end; auto.
    Qed.
  End cmd_ind.

End syntax.

Ltac2 this_cookbook () := this_cookbook_ ().

