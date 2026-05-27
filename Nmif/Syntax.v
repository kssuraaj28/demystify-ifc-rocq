From Stdlib Require List ssreflect ssrbool ssrfun.
Import List ListNotations ssreflect ssrbool ssrfun.

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
      | endorse (from to: Vars)
      | declassify (from to: Vars)
      | assign (dst : Vars) (exp: ValExp)
      | cond (exp: BoolExp) (b1 b2: Prog' Cmd)
      | while (exp: BoolExp) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

    Hypothesis hyp_endorse : 
      `(P (endorse v1 v2)).

    Hypothesis hyp_declassify : 
      `(P (declassify v1 v2)).

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
      case=> >; [apply: hyp_endorse| apply: hyp_declassify| apply: hyp_assign | apply: hyp_cond | apply: hyp_while].
      1-3:  lazymatch goal with |- Forall _ ?l => elim: l end; auto.
    Qed.
  End cmd_ind.

  Definition is_endorse (c : Cmd) : bool :=
    match c with endorse _ _ => true | _ => false end.

  Definition is_declassify (c : Cmd) : bool :=
    match c with declassify _ _ => true | _ => false end.

  Lemma is_endorse_declassify c:
    is_endorse c \/ is_declassify c \/ (~~ is_endorse c /\ ~~ is_declassify c).
  Proof. case: c=> /= *; intuition. Qed.

  Lemma is_endorse_declassify_opt oc:
    oapp is_endorse false oc \/ oapp is_declassify false oc
    \/ (~~ oapp is_endorse false oc /\ ~~ oapp is_declassify false oc).
  Proof. case: oc=> [c | ] /=; [exact: is_endorse_declassify | intuition]. Qed.

End syntax.
