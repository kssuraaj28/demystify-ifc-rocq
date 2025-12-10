From Stdlib Require Import List.
From Stdlib Require Import Basics. 

(* You `Require` library files, and import modules *)
From NMIF Require Import Common Store LangSyntax.
Import CommonNotations LangSyntaxNotations.


Section atklvl.
  Context {p : PartOrderParam}. 
  Class AtkLblParam := {attack_level : Label}. (* TODO: Is there an implicit coerction into this? *)
End atklvl.

Section defs.
  Context {p : PartOrderParam} {atkprm : AtkLblParam}.
  Let attack_conf :=  (conf attack_level).
  Let attack_int :=  (int attack_level).

  Section defs.
    Variable element_label : Label. 
    Let element_conf := (conf element_label).
    Let element_int := (int element_label).

    Definition Public : Prop := element_conf ≼c attack_conf. 
    Definition Secret : Prop := ~Public.  
    Definition Untrusted : Prop := element_int ≼i attack_int.
    Definition Trusted   : Prop := ~Untrusted.
  End defs.
End defs.


(* Attackers have private memory. *)
Class AtkMemParam : Type := {AttackerMem : Type}.

Section atk_code.
  Context {p : PartOrderParam} 
          {vars : VarParam} 
          {vals : ValueParam} 
          {atkprm : AtkLblParam} 
          {atkmem : AtkMemParam}.

  Let AllPred : VarPred := fun _ => 
    True.

  Let PubPred : VarPred := fun x => 
    Public (var_lbl x).

  Let PUPred : VarPred := fun x => 
    let x_lbl := var_lbl x in
    Public x_lbl /\ Untrusted x_lbl.

  Let SUPred : VarPred := fun x => 
    let x_lbl := var_lbl x in
    Secret x_lbl /\ Trusted x_lbl.

  Definition FullStore := Storeview AllPred.
  Definition PubStore := Storeview PubPred.
  Definition PUStore := Storeview PUPred.
  Definition SUStore := Storeview SUPred.

  (* Can I make this a class (temporarily)? TODO.. *)
  Record AttackSnippet := {
   (* How do the secret untrusted values get transformed? *)
    su_trans_code : AttackerMem -> FullStore -> SUStore;

   (* How do the public untrusted values get transformed? *)
    pu_trans_code : AttackerMem -> PubStore -> PUStore;

   (* How is the attacker memory changed? *)
    mem_code : AttackerMem -> PubStore -> AttackerMem; 

   (* What information is the attacker learning for themselves? *)
    leak_code : AttackerMem -> PubStore -> list Value; 
  }.

  Inductive AttackedLanguageCommand : Type :=  
  |  code (c : LanguageCommand)
  |  atk (a : AttackSnippet). 
  (* Could I coerce LanguageCommand into AttackedLanguageCommand
    Coercion code : LanguageCommand >-> AttackedLanguageCommand.
    This needs to be exported, and things..
  *)

  Definition AttackedProgram := list AttackedLanguageCommand.

End atk_code.

Section event. (* This should be a module eventually? *)
  (* I feel like there are many more pieces before this.. *)
  Context {p : PartOrderParam} 
          {vals : ValueParam}.

  Inductive Event : Type := 
    | inp_ev (v : Value)
    | out_ev (v : Value)
    | epsilon 
    | adv_leak (lv : list Value).
End event.

Section langeval.
  Context {p : PartOrderParam} 
          {vars : VarParam} 
          {vals : ValueParam}.

  Inductive LangCmdEval : 
    Store -> (* Input store *)
    LanguageCommand ->  (* Command to run *)
    Event ->  (* Resulting event *)
    Store ->  (* Resulting store *)
    Prop := 

    (* For Inductive things where I will actually do -> I _, I will forall *)
    | assignment_eval: 
        forall (dest : AssignableVars),
        let var := proj1_sig dest in

        forall (store : Store) (comp_fn : ComputeFn),
        let new_val := comp_fn (extract_storeview store _) in (* The type of comp_fn is enough *)

        forall (store' : Store),
        UpdatedStoreVal store store' var new_val ->

        _ store (dest ← comp_fn) epsilon store'

    | input_eval: 
        forall (dest : InputVars),
        let var := proj1_sig dest in

        forall (store new_store : Store) (val : Value),
        UpdatedStoreVal store new_store var val ->

        _ store (? dest) (inp_ev val) new_store

    | output_eval:
        forall (store : Store) (src : OutputVars),
        let var := proj1_sig src in
        let val := store var in

        _ store (! src) (out_ev val) store.

End langeval.

Section atkeval. 
  Context {p: PartOrderParam} 
          {vars : VarParam} 
          {vals : ValueParam}
          {atkprm : AtkLblParam}
          {atkmem : AtkMemParam}.

  Inductive AtkSnipEval (atk_code : AttackSnippet) :
                Store -> (* Input store *)
                Store -> (* Output store *)     
                AttackerMem -> (* Input attacker memory *)
                AttackerMem -> (* Output attacker memory *)
                list Value -> (* Leaked information *)
                Prop := 

      atk_snip_eval : 
          forall (store : Store) (amem : AttackerMem),
          (* TODO: Can I refactor this? Notation? *)
          let sustore' := su_trans_code atk_code amem (extract_storeview store _) in 
          let pustore' := pu_trans_code atk_code amem (extract_storeview store _) in
          let amem' := mem_code atk_code amem (extract_storeview store _) in 
          let leak := leak_code atk_code amem (extract_storeview store _) in 

          forall (supustore' : _), 
          CombinedStoreView sustore' pustore' supustore' ->

          forall (store' : _), (* Here, you might want to show that this is deterministic. *)
          UpdatedStore store supustore' store' ->

          _ _ store store' amem amem' leak.

  Print atk_snip_eval.
End atkeval.

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

