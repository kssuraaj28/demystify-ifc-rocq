From Stdlib Require Import Basics. 

From NMIF Require Import Common Store.

Module Syntax.
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

End Syntax.

Module Semantics.
  Import Syntax Syntax.Notations. (* I wonder if you should also export it. *)

  Section ev.
    Context {vals : ValueParam}.
    Inductive Event : Type := 
      | inp_ev (v : Value)
      | out_ev (v : Value)
      | epsilon.
  End ev.

  Section langeval.
    Context {p : PartOrderParam} 
            {vars : VarParam} 
            {vals : ValueParam}.



    Inductive LangCmdEval: 
      LanguageCommand -> (* Command *) (* I wonder if I can make this parametric *)
      Store -> (* Input store *)
      Store ->  (* Resulting store *)
      Event ->  (* Resulting event *)
      Prop := 

      (* For Inductive things where I will actually do -> I _, I will forall *)
      | assignment_eval: 
          forall (dest : AssignableVars),
          let var := proj1_sig dest in

          forall (store : Store) (comp_fn : ComputeFn),
          let new_val := comp_fn (extract_storeview store _) in (* The type of comp_fn is enough *)

          forall (store' : Store),
          UpdatedStoreVal store store' var new_val ->

          _ (dest ← comp_fn) store store' epsilon 

      | input_eval: 
          forall (dest : InputVars),
          let var := proj1_sig dest in

          forall (store new_store : Store) (val : Value),
          UpdatedStoreVal store new_store var val ->

          _ (? dest) store new_store (inp_ev val)

      | output_eval:
          forall (store : Store) (src : OutputVars),
          let var := proj1_sig src in
          let val := store var in

          _ (! src) store store (out_ev val).
  End langeval.
End Semantics.
