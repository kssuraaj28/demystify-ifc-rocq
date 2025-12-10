From NMIF Require Import Common.

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Classical_Prop.

Section store.
  Context {p : PartOrderParam} {vars : VarParam} {vals : ValueParam}. (* Typeclasses just cook this.. *)

  Definition Store := VarName -> Value. 

  Section storeview.
    Variable VarPred : VarName -> Prop.
    Let FilteredVars := VarSubset VarPred.
     
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
      (~(P var) -> newstore var = oldstore var) /\ (* Should this be \/ *)
      forall (prf : P var), newstore var = update (exist _ var prf). 
      (* Interestingly, if change prf to _, this is like 'clear'. I lose information. 
         This makes sense I guess..
         Can I get the system to automatically generate binder names?

         The best proof would have that generated, and, I could just use `assumption`
       *)  

  Theorem updatedstore_deterministic : forall store {P} (update : Storeview P), forall store' store'',
    UpdatedStore store update store' ->
    UpdatedStore store update store'' ->
    store' = store''.
  Proof. 
    repeat (intuition; match goal with
           | [ H : _ , H' : _ |- _ ] =>  specialize (H H')
           | [ |- _ = _] =>  apply functional_extensionality || congruence
           | [ P : _, x : _ |- _ ] =>  destruct (classic (P x))  
               (* This is a little bit garbage. The order of branches matters *)
    end).
  Qed.


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
