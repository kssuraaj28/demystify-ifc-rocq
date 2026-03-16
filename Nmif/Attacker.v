From Stdlib Require ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore.
Import VarValStore.

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
    init_state: (StoreView is_public) -> AtkStates;
    init_substeps: AtkStates -> nat;
    corruptor: AtkStates -> (StoreView is_untrusted) -> (StoreView is_untrusted);
    learner : AtkStates -> (StoreView is_public) -> AtkStates;
    leaker : AtkStates -> LeakVals;
    substeps : AtkStates -> nat;
  }.

Arguments AdvStateMachine: clear implicits.
Arguments AdvStateMachine {_ _ _ _} (AtkStates).
