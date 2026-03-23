From Stdlib Require ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore Util Noninterference. 
Import VarValStore Noninterference.

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
Import VarValStore.Notations.
Record AdvStateMachine `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} 
    {AtkStates : Type} := {
    init_state: StoreView -> AtkStates; (* You only get untrusted*)
    init_substeps: AtkStates -> nat;
    corruptor: AtkStates -> Store -> Store;

    corruptor_ni: 
      forall ast, 
        let: ast_corr := corruptor ast in
        let: tr_view := (fun s => ⟨ s | is_trusted ⟩) in
        let: pub_view := (fun s => ⟨ s | is_public ⟩) in
        Noninterfering tr_view ast_corr tr_view /\ (* trusted outputs don't change if trusted inputs don't *)
        Noninterfering pub_view ast_corr pub_view; (* public outputs don't chnage if public inputs don't *)


    learner : AtkStates -> Store -> AtkStates;

    learner_confni:
      forall ast,
        let: ast_lrn := learner ast in
        let: pub_view := (fun s =>  ⟨ s | is_public ⟩) in
        Noninterfering pub_view ast_lrn id;

    leaker : AtkStates -> LeakVals;
    substeps : AtkStates -> nat;
  }.

Arguments AdvStateMachine: clear implicits.
Arguments AdvStateMachine {_ _ _ _} AtkStates.
