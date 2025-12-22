From Stdlib Require Import List. 
Check _ :: _. (* I thought I can to import list notations for this *)

From NMIF Require Import Common Store Lang Atk.


(* Combined syntax *)
Module Syntax.
  Section cmd.

    Import Lang.Syntax Atk.Syntax.

    Context {p: PartOrderParam} 
            {vars : VarParam} 
            {vals : ValueParam}
            {atkprm : AtkLblParam}
            {atkmem : AtkMemParam}.

    (* TODO: Perhaps I can do some coercion into this type? *)
    Inductive AttackedLanguageCommand : Type :=  
    |  code (c : LanguageCommand)
    |  atk (a : AttackSnippet). 

  Definition AttackedProgram := list AttackedLanguageCommand.

  End cmd.
End Syntax.


Module Semantics.
  Section ev.
    Context {vals : ValueParam}. (* Is there a way do flag unnecessary things in contexts? *)

    Inductive Event :=
      | lang_ev (e : Lang.Semantics.Event)
      | atk_ev (e : Atk.Semantics.Event).
  End ev.

  Section opsem.

    (* 
      Can I import and rename? 
      I don't get the point of locality in definitions..
    *)
    Import Syntax(atk, code, AttackedProgram)
           Atk.Syntax(AttackerMem, AtkLblParam, AtkMemParam) (* I wonder if I could do selective import and change names *)
           Atk.Semantics(AtkSnipEval)
           Lang.Semantics(LangCmdEval).

    Context {p: PartOrderParam} 
            {vars : VarParam} 
            {vals : ValueParam}
            {atkprm : AtkLblParam} (* Maybe Import? TODO: What does Local do?*)
            {atkmem : AtkMemParam}.


    Record Configuration := {
      prog : AttackedProgram;
      store : Store ;
      atk_mem : AttackerMem
    }.


    Inductive TransitionRel : 
      Configuration ->  (*Starting state*)
      Configuration ->  (* Resulting state *)
      Event ->          (* Event, if any *)
      Prop := 
      | atk_step: 
          forall atk_snip remaining store amem,
          let cfg := ({| prog := (atk atk_snip) :: remaining ; store := store ; atk_mem := amem |}) in

          forall store' amem' adv_ev,
          AtkSnipEval atk_snip store store' amem amem' adv_ev ->
          let cfg' := ({| prog := remaining ; store := store' ; atk_mem := amem' |}) in

           _ cfg cfg' (atk_ev adv_ev)

      | prg_step:  
          forall cmd remaining store amem,
          let cfg := ({| prog := (code cmd) :: remaining ; store := store ; atk_mem := amem |}) in

          forall lng_ev store',
          LangCmdEval cmd store store' lng_ev ->
          let cfg' := ({| prog := remaining ; store := store' ; atk_mem := amem |}) in

          _ cfg cfg' (lang_ev lng_ev).

  End opsem.
End Semantics.
