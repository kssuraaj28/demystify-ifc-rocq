From Stdlib Require Program ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore Util Noninterference Lattice4pt Tacs. 
Import VarValStore Noninterference VarValStore.Notations Tacs Tacs.Cook. 

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

Definition AdvEvent `{!AdvLeakPrm} := option LeakVals.

Record AdvStateMachine `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} 
    {AtkStates : Type} := {
    init_state: StoreView -> AtkStates; (* You only get untrusted*)
    (* TODO: There needs to be an init_state well-formed also *)
    corruptor: AtkStates -> Store -> Store;
 
    corruptor_wf_int: 
      forall ast, 
        let: ast_corr := corruptor ast in
        let: tr_view := (store_to_view is_trusted) in
        (forall st, tr_view (ast_corr st) = (tr_view st));  (* The adversary does not touch trusted computation. This is a little bit ugly *)

    corruptor_wf_conf: 
      forall ast, 
        let: ast_corr := corruptor ast in
        let: pub_view := (store_to_view is_public) in 
        Noninterfering pub_view ast_corr pub_view; (* public outputs don't chnage if public inputs don't *)


    learner : AtkStates -> Store -> AtkStates;

    learner_wf:
      forall ast,
        let: ast_lrn := learner ast in
        let: pub_view := store_to_view is_public in
        Noninterfering pub_view ast_lrn id;

    curr_event : AtkStates -> AdvEvent;
    substeps : AtkStates -> nat;
  }.

Arguments AdvStateMachine: clear implicits.
Arguments AdvStateMachine {_ _ _ _} AtkStates.

Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite ->corruptor_wf_int in * ) "corruptor_wf_int" old.
Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1 ltac1:(unshelve erewrite corruptor_wf_conf;[|reflexivity|]) "corruptor_wf_conf" old. 
  (* TODO: I think maybe apply is better? TODO *)

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac2 Eval print_cookbook this_cookbook.

Section test.
  Context `{!VarPrm,!ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Generalizable All Variables.
  Ltac2 Set curr_cookbook := this_cookbook. 

  Goal `(forall P, P ⟨ corruptor (AtkStates := A) adv ast st  | is_trusted ⟩).
  Proof.   move=> *.  cook.  Abort.
End test.
