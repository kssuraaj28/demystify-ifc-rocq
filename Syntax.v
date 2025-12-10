From Stdlib Require Import Basics. 
From NMIF Require Import Common Store.

Import Common.Notations.

Module LangSyntax.
  Section cmd.
    Context {p : PartOrderParam} {vars : VarParam} {vals : ValueParam}.


    Check Storeview.
    Section types.
      Let IsInpVar : VarPred := fun v => var_kind v = inp_var.
      Let IsOutVar : VarPred := fun v => var_kind v = out_var.
      Let IsInternalVar : VarPred := fun v => var_kind v = internal_var.

      Open Scope program_scope.

      Definition InputVars := VarSubset (IsInpVar).
      Definition OutputVars := VarSubset (IsInpVar).
      Definition AssignableVars := VarSubset (not ∘ IsInpVar). (* When you are done w computation, you cannot assign to input variables *)
      Definition AccessibleStore := Storeview (not ∘ IsOutVar). (* When you are doing computation, you don't read from output variables *)
      Definition ComputeFn := AccessibleStore -> Value.
    End types.


    (*  
      You want some gap between output and the effect, so that you give attacker
      time to influence. This is a modeling hack, because I am so good.
    *)

    Inductive LanguageCommand : Type :=
      | input (v : InputVars)
      | assignment (v : AssignableVars) (comp_fn : ComputeFn)
        (* Mixing syntax and semantics like a pro *) 
      | output (v : OutputVars). 
    (* There is some nice duality to this nonsense. *)

    Definition LanguageProgram := list LanguageCommand. (* Only straightline code for now *)
  End cmd.


  Module Notations.
    (* TODO: What do notation attributes do? *)
    Notation " x ← f " := (assignment x f) (at level 50).
    Notation " ? x  " := (input x) (at level 50).
    Notation " ! x  " := (output x) (at level 50).
  End Notations.

End LangSyntax.

Module AtkSyntax.
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
  End atk_code.
End AtkSyntax.


(* Combined syntax *)
Section atk_code.
  Import AtkSyntax LangSyntax.
  Context {p : PartOrderParam} 
          {vars : VarParam} 
          {vals : ValueParam} 
          {atkprm : AtkLblParam} 
          {atkmem : AtkMemParam}.



  Inductive AttackedLanguageCommand : Type :=  
  |  code (c : LanguageCommand)
  |  atk (a : AttackSnippet). 
  (* Could I coerce LanguageCommand into AttackedLanguageCommand
    Coercion code : LanguageCommand >-> AttackedLanguageCommand.
    This needs to be exported, and things..
  *)

  Definition AttackedProgram := list AttackedLanguageCommand.

End atk_code.
