From Stdlib Require ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore Util.
Import VarValStore Util.BoolPred.

Class AdvLeakPrm := LeakVals : Type.

Class AdvLvlPrm  `{!VarPrm} := {
  is_untrusted : pred Vars ;
  is_public : pred Vars
}.

Section opposite.
  Context `{!VarPrm, !AdvLvlPrm}.
  Definition is_secret := inverse is_public.
  Definition is_trusted := inverse is_untrusted.
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
    init_substeps: AtkStates -> nat;
    corruptor: AtkStates -> StoreView -> StoreView;
    corruptor_wf: forall ast sv var, is_trusted var ->
                      corruptor ast sv var = None;
    learner : AtkStates -> StoreView -> AtkStates;
    leaker : AtkStates -> LeakVals;
    substeps : AtkStates -> nat;
  }.

Arguments AdvStateMachine: clear implicits.
Arguments AdvStateMachine {_ _ _ _} AtkStates.
