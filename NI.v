(* In my math, these hold obviously *)
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ClassicalFacts.

Section constant.
  Context {A B : Type}.
  Variable f : A -> B.

  Notation A_has_element := (exists a : A, True). (* Note how we just 'transported' A to Prop. In some sense, this is just A. Is this impredicativity? *)

  Definition constant : Prop := forall a a', f a = f a'. 
  Definition constant' : Prop := exists b, forall a, f a = b. 
End constant.

Definition example (x : Empty_set) : Empty_set :=  match x with end. 
Goal constant example. Proof. cbv; intuition. Qed. 
Goal ~ constant' example. Proof. cbv; inversion 1; intuition. Qed.



(* The many different ways to define Noninterference *)
Parameter SecretVal : Set.
Parameter PublicVal : Set.

Record State : Set := {secret : SecretVal ; public : PublicVal}.
Notation "⟨ s | p ⟩" := {| secret := s ; public := p |} (at level 5). (* Can I do this without | *)

Definition Computation : Set := State -> State.

Section ni_defs.
  Variable f : Computation.

  (* When if f noninterfering? *)
  Definition ni_0 : Prop :=
    forall p, forall s1 s2, 
      let inp1 := ⟨ s1 | p⟩ in
      let inp2 := ⟨ s2 | p ⟩ in
      public (f inp1) = public (f inp2).

  Definition ni_1 : Prop :=
    forall p, let f := (fun s => public (f ⟨ s | p ⟩)) in
          constant f.

  Goal ni_1 <-> ni_0. Proof. firstorder. Qed. 
  (* TODO: Is there a definition where we need to assume function existentionality? *)
  (* There is probably a version where we need to use exists *)




  (* 
    This is a garbage definition!
    It is essentially always true!
  *)
  Definition garbage (s : SecretVal) : Prop :=
    exists pub_trans,
      (* TODO: forall s used to be here before. Does that make a difference?*)
      pub_trans = fun p => public (f ⟨ s | p ⟩).


  Goal forall s, garbage s.
  Proof.
    eexists; reflexivity.
  Qed.

  (* Something using exists *)
  Definition ni_2 : Prop := exists pub_trans, forall s, pub_trans = fun p => public (f ⟨ s | p ⟩).

  Axiom temp : inhabited SecretVal \/ ~inhabited (SecretVal). (* This is nothing really special *)

  Goal ni_1 <->  ni_2.
  Proof.
    unfold ni_1; unfold ni_2; split; intros; cycle 1.
    - red; intros. destruct H. 
      generalize (H a).
      generalize (H a').
      clear H.
      intros; subst.
      assert (forall A B (f1 f2 : A -> B) , f1 = f2 -> forall x, f1 x = f2 x); [ congruence | idtac ].
      specialize (H _ _ _ _ H0 p).
      auto. (* What the hell.. This should be much easier. This is a disgusting proof. *)

    - destruct temp as [[s] |  y].
      --  exists (fun p => public (f ⟨ s | p ⟩)). (* This does make me a little sad. Is there a version with no axioms? *)
          intros. 
          apply functional_extensionality.
          firstorder.
      -- eexists (fun x => x). (* This seems arbitrary too... *)
         intros; exfalso; auto.
  Qed.
End ni_defs.
