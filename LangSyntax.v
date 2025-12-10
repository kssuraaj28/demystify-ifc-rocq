From Stdlib Require Import Basics. 

From NMIF Require Import Common Store.

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


Module LangSyntaxNotations.
  (* TODO: What do notation attributes do? *)
  Notation " x ← f " := (assignment x f) (at level 50).
  Notation " ? x  " := (input x) (at level 50).
  Notation " ! x  " := (output x) (at level 50).
End LangSyntaxNotations.
