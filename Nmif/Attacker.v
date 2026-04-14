From Stdlib Require Program ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore Util Noninterference. 
Import VarValStore Noninterference.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Class AdvLeakPrm := LeakVals : Type.

Class AdvLvlPrm  `{!VarPrm} := {
  is_untrusted : pred Vars ;
  is_public : pred Vars
}.

Section opposite.
  Context `{!VarPrm, !AdvLvlPrm}.
  Definition is_secret v := ~~ is_public v.
  Definition is_trusted v := ~~ is_untrusted v.
End opposite.



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

Record AdvStateMachine `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} 
    {AtkStates : Type} := {
    init_state: StoreView -> AtkStates; (* You only get untrusted*)
    init_substeps: AtkStates -> nat; (* We allow atkstates because this can depend on the public store *)
    corruptor: AtkStates -> Store -> Store;

    corruptor_wf: 
      forall ast, 
        let: ast_corr := corruptor ast in
        let: tr_view := (store_to_view is_trusted) in
        let: pub_view := (store_to_view is_public) in 
        (forall st, tr_view (ast_corr st) = (tr_view st)) /\  (* The adversary does not touch trusted computation. This is a little bit ugly *)
        Noninterfering pub_view ast_corr pub_view; (* public outputs don't chnage if public inputs don't *)


    learner : AtkStates -> Store -> AtkStates;

    learner_wf:
      forall ast,
        let: ast_lrn := learner ast in
        let: pub_view := store_to_view is_public in
        Noninterfering pub_view ast_lrn id;

    leaker : AtkStates -> option LeakVals;
    substeps : AtkStates -> nat;
  }.

Arguments AdvStateMachine: clear implicits.
Arguments AdvStateMachine {_ _ _ _} AtkStates.
