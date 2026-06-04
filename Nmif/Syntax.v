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
      | assign (_ : Assignment)
      | cond (exp: BoolExp) (b1 b2: Prog' Cmd)
      | while (exp: BoolExp) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

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
      case=> >; [apply: hyp_assign| apply: hyp_cond | apply: hyp_while].
      1-3:  lazymatch goal with |- Forall _ ?l => elim: l end; auto.
    Qed.
  End cmd_ind.

(*
(* TODO: Should go elsewhere *)
  Definition is_endorse (c : Cmd) : bool :=
    match c with assign (endorse _ _) => true | _ => false end.

  Definition is_declassify (c : Cmd) : bool :=
    match c with assign (declassify _ _) => true | _ => false end.

  Lemma is_endorse_inv c: is_endorse c -> exists from to, c = assign (endorse from to).
  Proof. case: c=> [[]| |] //= *; eauto. Qed.

  Lemma is_declassify_inv c: is_declassify c -> exists from to, c = assign (declassify from to).
  Proof. case: c=> [[]| |] //= *; eauto. Qed.

  Lemma is_endorse_inv_opt oc:
    oapp is_endorse false oc -> exists from to, oc = Some (assign (endorse from to)).
  Proof. case: oc=> //= c /is_endorse_inv [from [to ->]]; eauto. Qed.

  Lemma is_declassify_inv_opt oc:
    oapp is_declassify false oc -> exists from to, oc = Some (assign (declassify from to)).
  Proof. case: oc=> //= c /is_declassify_inv [from [to ->]]; eauto. Qed.

  Lemma is_endorse_declassify c:
    is_endorse c \/ is_declassify c \/ (~~ is_endorse c /\ ~~ is_declassify c).
  Proof. case: c=> [[]| |] /= *; intuition. Qed.

  Lemma is_endorse_declassify_opt oc:
    oapp is_endorse false oc \/ oapp is_declassify false oc
    \/ (~~ oapp is_endorse false oc /\ ~~ oapp is_declassify false oc).
  Proof. case: oc=> [c | ] /=; [exact: is_endorse_declassify | intuition]. Qed.
*)
End syntax.

(*
Ltac2 Set this_cookbook_ as old :=
  add_cookstep
    ltac1:(match goal with
     |  noend : is_true (~~ oapp is_endorse false ?c), c : option Cmd |- _ =>
           let P := fresh in  let b := fresh in
           pattern_focus [match c with | Some (assign (endorse _ _)) => _ | _  => _ end]=> P;
           set b := (X in match _ with Some (assign (endorse _ _)) => _ | _ => X end);
           suff: P b;  [move: P b noend; clear; case: c=> //=; case=> //=; case=> //=| subst P b;cbv beta]
         end) "noend" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep
    ltac1:(match goal with
     |  nodecl : is_true (~~ oapp is_declassify false ?c), c : option Cmd |- _ =>
           let P := fresh in  let b := fresh in
           pattern_focus [match c with | Some (assign (declassify _ _)) => _ | _  => _ end]=> P;
           set b := (X in match _ with Some (assign (declassify _ _)) => _ | _ => X end);
           suff: P b;  [move: P b nodecl; clear; case: c=> //=; case=> //=; case=> //=| subst P b;cbv beta]
         end) "nodecl" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep
    ltac1:(match goal with
     |  noend : is_true (~~ is_endorse ?a), c : Cmd |- _ =>
           let P := fresh in  let b := fresh in
           pattern_focus [match c with | assign (endorse _ _) => _ | _  => _ end]=> P;
           set b := (X in match _ with assign (endorse _ _) => _ | _ => X end);
           suff: P b; [move: P b noend; clear; case: c=> [[]| |] //= |subst P b; cbv beta]
         end) "no_endorse" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep
    ltac1:(match goal with
     |  nodecl : is_true (~~ is_declassify ?a), c : Cmd |- _ =>
           let P := fresh in  let b := fresh in
           pattern_focus [match c with | assign (declassify _ _) => _ | _  => _ end]=> P;
           set b := (X in match _ with assign (declassify _ _) => _ | _ => X end);
           suff: P b; [move: P b nodecl; clear; case: c=> [[]| |] //= |subst P b; cbv beta]
         end) "no_declassify" old.
*)

Ltac2 this_cookbook () := this_cookbook_ ().

(*
Section test.
  Context `{!VarPrm, !ValPrm}.
  Ltac cook := ltac2:(cook this_cookbook).

  Goal forall (c: option Cmd) (X Y: nat),
    ~~ oapp is_endorse false c ->
    match c with Some (assign (endorse _ _)) => X | _ => Y end = Y.
  Proof. move=> c X Y noend. cook. Abort.

  Goal forall (c: option Cmd) (X Y: nat),
    ~~ oapp is_declassify false c ->
    match c with Some (assign (declassify _ _)) => X | _ => Y end = Y.
  Proof. move=> c X Y nodecl. cook. Abort.

  Goal forall (c: option Cmd) (X Y: nat),
    match c with Some (assign (endorse _ _)) => X | _ => Y end = Y.
  Proof. move=> c X Y. Fail cook. Abort.

  Goal forall (c: Cmd) (X Y: nat),
    ~~ is_endorse c ->
    match c with assign (endorse _ _) => X | _ => Y end = Y.
  Proof. move=> c X Y noend. cook. Abort.

  Goal forall (c: Cmd) (X Y: nat),
    ~~ is_declassify c ->
    match c with assign (declassify _ _) => X | _ => Y end = Y.
  Proof. move=> c X Y nodecl. cook. Abort.
End test. *)
