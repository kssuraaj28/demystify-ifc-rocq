From Stdlib Require List ssreflect ssrbool.
Import List ListNotations ssreflect ssrbool.

Require VarValStore Tacs.
Import VarValStore.



Section xxx.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variable (adv : AdvStateMachine).

            




  (*
    The idea would be to have a static analysis.
    Then we show that endorse and declassify points are enough to enforce whatever we want..
  *)

  (* Maybe make something Cfg *)
  (* What is 'state'? *)
  (* This is disgusting. TODO *)
  Definition cfg_step 
                (c: Continuation) (s: Store) (ast: AtkStates) : 
                (Continuation * Store * AtkStates) := 
                if c isn't cmd :: rest then ([], s, ast) else
                let: (s', ast', cont') := step_w_atk cmd s ast in
                (cont' ++ rest ,s', ast').
End step.
