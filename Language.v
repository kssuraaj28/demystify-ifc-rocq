From Stdlib Require Import List.
From Stdlib Require Import Basics. 

(* You `Require` library files, and import modules *)
From NMIF Require Import Common Store Syntax.
Import Syntax.LangSyntax Common.Notations LangSyntax.Notations.




(* I think that I might have to show that things are deterministic. 
Assignment  
Attacker execution 
*)

Section opsem.
  Context {p: PartOrderParam} 
          {vars : VarParam} 
          {vals : ValueParam}
          {atkprm : AtkLblParam}
          {atkmem : AtkMemParam}.

  Record Configuration := {
    prog : AttackedProgram;
    store : Store ;
    atk_mem : AttackerMem
  }.


  Inductive TransitionRel : 
    Configuration ->  (*Starting state*)
    Event ->          (* Event, if any *)
    Configuration ->  (* Resulting state *)
    Prop := 
    | atk_step: 
        forall atk_snip remaining store amem,
        let cfg := ({| prog := (atk atk_snip) :: remaining ; store := store ; atk_mem := amem |}) in

        forall store' amem' leak,
        AtkSnipEval atk_snip store store' amem amem' leak ->
        let cfg' := ({| prog := remaining ; store := store' ; atk_mem := amem' |}) in

        _ cfg (adv_leak leak) cfg'

    | prg_step:  
        forall cmd remaining store amem,
        let cfg := ({| prog := (code cmd) :: remaining ; store := store ; atk_mem := amem |}) in

        forall event store',
        LangCmdEval store cmd event store' ->
        let cfg' := ({| prog := remaining ; store := store' ; atk_mem := amem |}) in

        _ cfg event cfg'.

  (* I'd like to define what NMIF means semantically. 
  - Single attack nmif. There are multiple choices here. 
      The attacker that does not touch SU. The attacker that sets them to 0, etc.
      Are all these definitions equivalent?
  - Lifting this to multiple attacks. 
  - How to define confidentiality? We need to change the model a little bit. I feel like we might need to change the system model.
    -- I have thoughts on how to do this correctly also
  *)

End opsem.
