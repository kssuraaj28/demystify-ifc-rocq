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
Check Noninterfering.
Import VarValStore.Notations.
Record AdvStateMachine `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} 
    {AtkStates : Type} := {
    init_state: StoreView -> AtkStates; (* You only get untrusted*)
    init_substeps: AtkStates -> nat;
    corruptor: (AtkStates * Store) -> Store;

    (* I don't know whether this is correct. TODO *)
    corruptor_wf: 
      Noninterfering corruptor 
      (fun '(a, s) => (a, ⟨s | is_trusted ⟩))
      (fun s => ⟨s | is_trusted⟩);

    learner : (AtkStates * Store) -> AtkStates;

    learner_wf:
      Noninterfering learner
      (fun '(a, s) => (a, ⟨ s | is_secret ⟩)) (* TODO: I need to think about this *)
      (fun s => s);

    leaker : AtkStates -> LeakVals;
    substeps : AtkStates -> nat;
  }.

Arguments AdvStateMachine: clear implicits.
Arguments AdvStateMachine {_ _ _ _} AtkStates.
