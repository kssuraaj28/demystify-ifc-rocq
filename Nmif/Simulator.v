From Stdlib Require List ssreflect ssrfun ssrbool. 
Import List ListNotations ssreflect ssrfun ssrbool.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

(* How is the simulator constructed? *)

Section sim_st.
  Context `{!VarPrm, !ValPrm} {AtkStates: Type}.

  Record SimStates  := mk_simstate {
      ast : AtkStates;
      sim_st : Store; 
      program : list ((option Cmd) * bool);
      (* You need to have a list of pending activations. 
      In an activation, you can have:
        - command
        - whether the attacker is running
      *)
    }.

    (* Maybe having a sim_stepping relation *)

End sim_st.



Section sim_constr.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Notation SimStates := (SimStates (AtkStates:=AtkStates)).
  Notation SimStateMachine := (AdvStateMachine SimStates).


  Variables (atk: AdvStateMachine AtkStates) (prog: Prog).

  #[refine] Definition sim_step (simst: SimStates): SimStates :=
    let: mk_simstate ast sim_st program_mem := simst in 
    if program_mem isn't ((ocmd, isatk) :: rest) then simst else

    let: sim_st' :=  sim_st in 
    let: sim_st' := if isatk is true then (corruptor atk ast sim_st) else sim_st' in 
    let: sim_st' := optcmd_stp_store ocmd sim_st' in


    (* Here, I think that you need to do big brain *)


    mk_simstate (learner atk ast sim_st') sim_st' (_ ++ rest).
    Proof. 
    Check (corruptor atk ast sim_st).

    kall: cycle 1.

  
  #[refine] Definition construct_simulator : SimStateMachine := 
    {| 
      init_state sv :=  
        (mk_simstate _ _ _) ;

      learner :=  _ ;

      corruptor _ st :=  st ;  (* Ideal corruptor is weak *)
      curr_event simst := 
        let: mk_simstate ast _ _ := simst in
        curr_event atk ast;
      substeps simst := 
        let: mk_simstate ast _ _ := simst in
        substeps atk ast; (* This is not correct! *)
    |}.
  econstructor.
  (* How does one construct simulator? I  *)

End sim_constr.






















Ltac2 this_cookbook () := this_cookbook_ ().
