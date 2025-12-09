From Stdlib Require Import List.
From Stdlib Require Import Basics. (* TODO: How to go to this library file? *)


From NMIF Require Import PartialOrder.


(* I think that this is probably the better way? *)
Class PartOrderParam : Type := {
  conf_po : PartialOrder;
  int_po : PartialOrder;
 }.

Section label. 
  Context {params : PartOrderParam}. 

  Definition ConfCarrier := Carrier (data conf_po).
  Definition ConfOrder := Ordering (data conf_po).

  Definition IntCarrier := Carrier (data int_po).
  Definition IntOrder := Ordering (data int_po).

  Record Label : Type := { 
    conf : ConfCarrier;
    int : IntCarrier
    }.
End label.

(* Whenever I am defining a notation, I am happy to define a definition that corresponds to it... *)
(* I don't know whether this is the right place to put this? Should I do export? TODO *)
#[local] Notation "x '≼c' y" := (ConfOrder x y)(at level 70).
Check _ ≼c _. (* Is there a useful place where we'd want to have notations but the check will fail? *)

#[local] Notation "x '≼i' y" := (IntOrder x y)(at level 70).
Check _ ≼i _.

#[local] Notation "⟨ l1 , l2 ⟩" := {| conf := l1 ; int := l2 |}.

Section test.
  Check ⟨ _ , _ ⟩.
  Context {p : PartOrderParam}.
  Check ⟨ _ , _ ⟩.
  Variables (root : ConfCarrier) (alice : IntCarrier).
  Check ⟨ root , alice ⟩ : Label.
End test.

Class ValueParam : Type := {
  Value : Type ;
  val_eq_dec : forall v v' : Value, {v = v'} + {v <> v'} ;
  }.


(* Is this a good name? *)
Inductive VarKind : Type := inp_var | out_var | internal_var.
Definition varkind_eq_dec : forall k k' : VarKind, {k = k'} + {k <> k'}. Proof.  decide equality. Defined.

Section varname.
  Context {p : PartOrderParam}. (* TODO:  What happens when this is not an implicit parameter? What about `  *)

  Class VarParam : Type := {
    VarName : Type ;
    var_lbl : VarName -> Label ; 
    var_kind : VarName -> VarKind ; 
    var_eq_dec : forall v v' : VarName, {v = v'} + {v <> v'} ; (* Do I need this actually? *)
    }.

End varname.

Section varsubset.
  Context {p: PartOrderParam} {vars: VarParam}. 
  Definition VarPred := VarName -> Prop.

  Definition VarSubset (P : VarPred) := {v : VarName | P v}.
End varsubset.


Section var_kind_preds.
  Context {p : PartOrderParam} {vars : VarParam}.

  Variable (v : VarName).
  Let v_kind := var_kind v.

  Definition IsInpVar := v_kind = inp_var.

  Definition IsOutVar := v_kind = out_var.

  Definition IsInternalVar := v_kind = internal_var.
End var_kind_preds.

Section test.
  Open Scope program_scope. (* Does this belong here? *)
  Check not ∘ IsInpVar. (* In general, I'd like to be able to lift more.. For instance, I want to lift \/ *)
End test.

Section store.
  Context {p : PartOrderParam} {vars : VarParam} {vals : ValueParam}. (* Typeclasses just cook this.. *)

  Definition Store := VarName -> Value. 

  Section storeview.
    Variable VarPred : VarName -> Prop.
    Let FilteredVars := 
      VarSubset VarPred.
      (*
      {x : VarName | VarPred x}.
      *)
     
    Definition Storeview := FilteredVars -> Value.
  End storeview.


  Definition extract_storeview (s : Store) (Pred : VarName -> Prop) : Storeview Pred :=
    fun c => 
      match c with 
        exist _ idx _ => (s idx)
      end.

  About extract_storeview.

  (* 
  Why can I not get the computation of this to not go through? 
  If that were the case, we'd need to 'test' the input against the predicate,
  Not all predicates are computationally testable :)
  *)
  (* I don't know what kind of implicit I should use.. 
  For now, I'll just use maximally inserted implcits
  *)
  Definition UpdatedStore (oldstore : Store) {P} (update : Storeview P) (newstore : Store) : Prop :=
    forall (var : VarName), 
      ~(P var) -> newstore var = oldstore var /\
      forall (prf : P var), newstore var = update (exist _ var prf). 
      (* Interestingly, if change prf to _, this is like 'clear'. I lose information. 
         This makes sense I guess..
         Can I get the system to automatically generate binder names?

         The best proof would have that generated, and, I could just use `assumption`
       *)  


  (* 
     Helper when the update is just for a single value. 
     I am a little bit sad that this is not a function.
  *)
  Section updatedstoreval.
    Variables (oldstore newstore : Store)
              (var : VarName)
              (val : Value).

    Let VarSelPred (v' : VarName) :=  v' = var.
    Let storeslice : Storeview VarSelPred := fun inp => val.

    Definition UpdatedStoreVal : Prop := UpdatedStore oldstore storeslice newstore.
  End updatedstoreval.


    (* What does it mean to combine two store views*)
    (* I also don't know whether this works. I would like to have an example to check. Moreover, I think that this is not deterministic*)
    (* I wonder if an inductive definition is clearer *)
    (* TODO: Can I use Ltac for this? *)
    Definition CombinedStoreView {P1} {P2} (sv1 : Storeview P1) (sv2 : Storeview P2) (sres : Storeview (fun var => P1 var \/ P2 var)) : Prop :=
      forall var, 
        forall (prf : P1 var), 
          let val := sv1 (exist _ var prf) in 
          let resval := sres (exist _ var (or_introl prf)) in (* TODO: Why is it that I can (or_introl _ prf) also?*)
          resval = val
      \/
        forall (prf : P2 var), 
          let val := sv2 (exist _ var prf) in 
          let resval := sres (exist _ var (or_intror prf)) in 
          resval = val.

    (* TODO: Test this. Test the nondeterminism, etc. *)
End store.

Section example.
  Variable admit : forall {T}, T. (* Wow, I'm soo good *)

  Context {po : PartOrderParam}.

  (* I was using Coercions before. But I think that this is better. *)
  Instance vars : VarParam := {|
    VarName := nat;
    var_lbl := admit;
    var_kind := admit;
    var_eq_dec := admit;
 |}. Existing Instance vars.

  Let vals : ValueParam := {|
    Value := nat;
    val_eq_dec := admit;
 |}. Existing Instance vals.

  Compute Store.

  Notation "v == v'" := (PeanoNat.Nat.eq v v')(at level 10).
  Check _ == _.

  Print Notation "_ == _".

  Let ex1 : Store := fun _ => 5.

  Let ex2 : Store := fun v => 
    match v with 
    | 2 => 4 
    | 4 => 49
    | 1 => 98 
    | 0 => 4 
    | _ => 0
    end.

  Compute ex2 5.
  Compute ex2 4.

End example.
Fail Print Notation "_ == _".


Section cmd.
  Context {p : PartOrderParam} {vars : VarParam} {vals : ValueParam}.



  Section var_subsets.
    Open Scope program_scope.
    (* This should go somewhere else. I don't know where though. *)
    Definition InputVars := VarSubset (IsInpVar).
    Definition OutputVars := VarSubset (IsInpVar).
    Definition AssignableVars := VarSubset (not ∘ IsInpVar). (* When you are done w computation, you cannot assign to input variables *)
    Definition AccessibleStore := Storeview (not ∘ IsOutVar). (* When you are doing computation, you don't read from output variables *)
    Definition ComputeFn := AccessibleStore -> Value.
  End var_subsets.

  (*  
    You want some gap between output and the effect, so that you give attacker time to influence. This is a modeling hack. However, I think that it is okay
(* The point is that  the attacker should be able to read and modify (if necessary) the output.  *)
  *)

  Inductive LanguageCommand : Type :=
    | input (v : InputVars)
    | assignment (v : AssignableVars) (comp_fn : ComputeFn)
      (* Mixing syntax and semantics like a pro *) 
    | output (v : OutputVars). 
  (* There is some nice duality to this nonsense. *)

  Definition LanguageProgram := list LanguageCommand. (* Only straightline code for now *)

End cmd.



(* TODO: What is the visibility of these notations.. 
I would like these to be local to the current compilation unit (Library file), but it should be possible to import these to other modules eventually?
Maybe the right solution is to have this be in a module, but it can be used locally in the file. TODO: Test this...
*)
#[local] Notation " x ← f " := (assignment x f) (at level 50).
#[local] Notation " ? x  " := (input x) (at level 50).
#[local] Notation " ! x  " := (output x) (at level 50).


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

    (* Is there a CT way of doing whatever I just did. 
    f : A -> B
    f_lift : (X -> A) -> (X -> B)

    f : (A x B) -> C
    f_lift : ((X -> A) x (X -> B)) -> (X -> C))
    *)
    Definition PublicTrusted   : Prop := Public /\ Trusted. 
    Definition SecretTrusted   : Prop := Secret /\ Trusted.
    Definition PublicUntrusted : Prop := Public /\ Untrusted.
    Definition SecretUntrusted : Prop := Secret /\ Untrusted.
  End defs.
End defs.

Section pred_egs.
  Context {p : PartOrderParam} {v :VarParam} {atkprm : AtkLblParam}.

  Variable x : VarName.
  (* TODO: Should these be Let. *)
  Definition AllPred := let _ := x in True.
  Definition PubPred := Public (var_lbl x).
  Definition PUPred := PublicTrusted (var_lbl x).
  Definition SUPred := SecretUntrusted (var_lbl x).
End pred_egs.

(* Attackers have private memory. *)
Class AtkMemParam : Type := {AttackerMem : Type}.

(* TODO: Have input vars, etc. *)
Section atk_code.
  Context {p : PartOrderParam} 
          {vars : VarParam} 
          {vals : ValueParam} 
          {atkprm : AtkLblParam} 
          {atkmem : AtkMemParam}.

  Let FullStore := Storeview AllPred.
  Let PubStore := Storeview PubPred.
  Let PUStore := Storeview PUPred.
  Let SUStore := Storeview SUPred.

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

Search sig.

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

    | assignment_eval (store new_store : Store) (dest : AssignableVars)  (comp_fn : ComputeFn) : 
        let var := proj1_sig dest in
        let new_val := comp_fn (extract_storeview store _) in
        UpdatedStoreVal store new_store var new_val ->
        _ store (dest ← comp_fn) epsilon new_store

    | input_eval (store new_store : Store) (dest : InputVars) (val : Value) : 
        let var := proj1_sig dest in
        UpdatedStoreVal store new_store var val ->
        _ store (? dest) (inp_ev val) new_store

    | output_eval (store : Store) (src : OutputVars):
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
          
                AttackerMem -> (* Output attacker memory *)
                list Value -> (* Leaked information *)
                Prop := 
      atk_snip_eval (store store' amem : _) : 
          let allstore := extract_storeview store AllPred in
          let pubstore := extract_storeview store PubPred in

          (* Perhaps it is better to do match? *)
          (* Maybe a co-let or something? *)
          let sustore' := su_trans_code atk_code amem allstore in 
          let pustore' := pu_trans_code atk_code amem pubstore in
          let amem' := mem_code atk_code amem pubstore in 
          let leak := leak_code atk_code amem pubstore in 
          _ _ store store' amem amem' leak.
End atkeval.

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
    | atk_step (atk_snip store store' amem amem' leak remaining : _) :
        let cfg := ({| prog := (atk atk_snip) :: remaining ; store := store ; atk_mem := amem |}) in
        let cfg' := ({| prog := remaining ; store := store' ; atk_mem := amem' |}) in
        AtkSnipEval atk_snip store store' amem amem' leak ->
        TransitionRel cfg (adv_leak leak) cfg'

    | prg_step  (cmd store store' amem event remaining : _) :
        let cfg := ({| prog := (code cmd) :: remaining ; store := store ; atk_mem := amem |}) in
        let cfg' := ({| prog := remaining ; store := store' ; atk_mem := amem |}) in
        LangCmdEval store cmd event store' ->
        TransitionRel cfg event cfg'.

  (* I'd like to define what NMIF means semantically. 
  - Single attack nmif. There are multiple choices here. 
      The attacker that does not touch SU. The attacker that sets them to 0, etc.
      Are all these definitions equivalent?
  - Lifting this to multiple attacks. 
  - How to define confidentiality? We need to change the model a little bit. I feel like we might need to change the system model.
    -- I have thoughts on how to do this correctly also
  *)

End opsem.
