From Stdlib Require Program ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore Util Noninterference Lattice4pt Tacs. 
Import VarValStore Noninterference VarValStore.Notations Tacs Tacs.Dominate. 

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable dom_list_ () : dominate_taclist := []. (* TODO: Create empty dom_list function*)

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

Ltac corr_int_gl_dstep := assert_goals 1 (idtac; rewrite corruptor_wf_int).
Ltac2 Set dom_list_ as old := 
  append_tac ltac1:(corr_int_gl_dstep) "corr_int_gl_dstep" old.

Ltac corr_conf_gl_dstep := (* TODO: ensure_goals? *)
  assert_goals 1 (idtac; unshelve erewrite corruptor_wf_conf;[|reflexivity|]).
Ltac2 Set dom_list_ as old := 
  append_tac ltac1:(corr_conf_gl_dstep) "corr_conf_gl_dstep" old.

Ltac2 dom_list () := dom_list_ ().
Ltac2 Eval print_domlist dom_list.

Section test.
  Context `{!VarPrm,!ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Generalizable All Variables.
  Ltac2 Set curr_dom_list := dom_list. 

  Goal `(forall P, P ⟨ corruptor (AtkStates := A) adv ast st  | is_trusted ⟩).
  Proof. 
  Set Printing All.
  move=> *.  dominate.
  Abort.


End test.
