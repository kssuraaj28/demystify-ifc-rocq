From Stdlib Require Program ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore Util Noninterference Lattice4pt Tacs.
Import VarValStore Noninterference VarValStore.Notations Lattice4pt Tacs Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Class AdvLeakPrm := LeakVals : Type.

Class AdvLvlPrm `{!VarPrm} :=  var_lbl : Vars -> Lattice4pt.Label.

Section defs.
  Import Lattice4pt.
  Context `{!VarPrm, !AdvLvlPrm}.
  Definition is_public v := public (var_lbl v).
  Definition is_untrusted v := untrusted (var_lbl v).
  Definition is_secret v := ~~ is_public v.
  Definition is_trusted v := ~~ is_untrusted v.
End defs.



(* Instead, we could do uniform unfold. cbn.  *)
Ltac2 Set this_cookbook_ as old :=
  add_cookstep
    ltac1:(match goal with
      | H: var_lbl ?x = mk_lbl _ _ |- _ =>
        lazymatch goal with
        | |- is_true (is_public x)       => rewrite/is_public
        | |- is_true (~~ is_public x)    => rewrite/is_public
        | |- is_true (is_secret x)       => rewrite/is_secret /is_public
        | |- is_true (~~ is_secret x)    => rewrite/is_secret /is_public
        | |- is_true (is_trusted x)      => rewrite/is_trusted /is_untrusted
        | |- is_true (~~ is_trusted x)   => rewrite/is_trusted /is_untrusted
        | |- is_true (is_untrusted x)    => rewrite/is_untrusted
        | |- is_true (~~ is_untrusted x) => rewrite/is_untrusted
        end; rewrite H; reflexivity; fail
    end) "label_unfold" old.

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac local_cook := ltac2:(cook this_cookbook).
Ltac2 Eval print_cookbook this_cookbook.

Section test.
  Context `{!VarPrm,!ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Generalizable All Variables.
  Ltac cook := ltac2:(cook this_cookbook).

  Goal forall x, var_lbl x = mk_lbl true true -> is_public x.
  Proof. move=> x H. cook. Abort.

  Goal forall x, var_lbl x = mk_lbl false false -> is_secret x.
  Proof. move=> x H. cook. Abort.

  Goal forall x, var_lbl x = mk_lbl false true -> is_trusted x.
  Proof. move=> x H. cook. Abort.

  Goal forall x, var_lbl x = mk_lbl true false -> is_untrusted x.
  Proof. move=> x H. cook. Abort.

  Goal forall x y, var_lbl x = mk_lbl true false -> var_lbl y = mk_lbl false true -> is_public y.
  Proof. move=> x y Hx Hy. cook. Abort.

  Goal forall x, var_lbl x = mk_lbl true true -> is_secret x -> False.
  Proof. move=> x H. Fail cook. Abort.

  Goal forall x, var_lbl x = mk_lbl true false -> ~~ is_public x.
  Proof. move=> x H. cook. Abort.

  Goal forall x, var_lbl x = mk_lbl true true -> ~~ is_trusted x.
  Proof. move=> x H. cook. Abort.

  Goal forall x, var_lbl x = mk_lbl false false -> ~~ is_untrusted x.
  Proof. move=> x H. cook. Abort.

  Goal forall x, var_lbl x = mk_lbl false true -> ~~ is_secret x.
  Proof. move=> x H. cook. Abort.
End test.

(* 
  TODO
  You need to eventually corrupt store,
  Learn from store etc 
*)
(* 
  The attacker is sandwiched between the normal code... 
  corrupt ; cmd;  learn ; leak || substeps

  Another thing we could do is something where
  you also get access to pc?  TODO

  Prm naming scheme? TODO
*)


Section adv.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Definition AdvEvent := option LeakVals.
  (*
  Record AdvInit {AtkStates} :=  {
    init_fn :  _;
  }.*)

(* Previously this record also carried
     init_state : StoreView -> AtkStates
   (the attacker only sees the untrusted view) together with a TODO for an
   init_state well-formedness obligation. Dropped during the rename to
   AdvNextStep — initial-state construction now lives outside this record. *)
  Record AdvNextStep := {
      (* Corruption *)
      pre_cmd_action: AtkStates -> Store -> Store;
      pre_cmd_event: AtkStates -> AdvEvent;
      post_cmd_action: AtkStates -> Store -> (AtkStates * nat); (* New state and substeps *)
  
      pre_cmd_wf_int: 
        forall ast, 
          let: ast_corr := pre_cmd_action ast in
          let: tr_view := (store_to_view is_trusted) in
          (forall st, tr_view (ast_corr st) = (tr_view st));  (* The adversary does not touch trusted computation. This is a little bit ugly *)
  
      pre_cmd_wf_conf: 
        forall ast, 
          let: ast_corr := pre_cmd_action ast in
          let: pub_view := (store_to_view is_public) in 
          Noninterfering pub_view ast_corr pub_view; (* public outputs don't chnage if public inputs don't *)
  
  
      post_cmd_wf:
        forall ast,
          let: ast_lrn := post_cmd_action ast in
          let: pub_view := store_to_view is_public in
          Noninterfering pub_view ast_lrn id;
  
    }.
End adv.

Arguments AdvNextStep: clear implicits.
Arguments AdvNextStep {_ _ _ _} AtkStates.



