(* The many different ways to define Noninterference *)
From Stdlib Require Import Logic.FunctionalExtensionality.
Definition Val := nat.

Record State : Set := {trusted : Val ; untrusted : Val}.
Notation "⟨ t | u ⟩" := {| trusted := t ; untrusted := u |} (at level 5). (* Can I do this without | *)

Definition Computation : Set := State -> State.


Section constant.
  Context {A B : Type}.
  Variable f : A -> B.

  Notation A_has_element := (exists a : A, True). (* Note how we just 'transported' A to Prop. In some sense, this is just A. Is this impredicativity? *)

  Definition constant : Prop := forall a a', f a = f a'. 

  Definition constant' : Prop := exists b, forall a, f a = b. 
  

  (* Is there a function that satisified constant', but not constant? *)
  Goal constant <-> constant'. 
  Proof.
    unfold constant; unfold constant'; intuition.
    - admit. (* This does not hold actually.. *)
    - firstorder; generalize (H a'); generalize (H a); intros; subst; auto. (* This is garbage *)
  Abort.

End constant.

Definition example (x : Empty_set) : Empty_set :=  match x with end.

Goal constant example. Proof. cbv; intuition. Qed.
Goal ~ constant' example. Proof. cbv; inversion 1; intuition. Qed.


Section ni_defs.
  Variable f : Computation.

  (* When if f noninterfering? *)
  Definition ni_0 : Prop :=
    forall t, forall u1 u2, 
      let inp1 := ⟨ t | u1⟩ in
      let inp2 := ⟨ t | u2 ⟩ in
      trusted (f inp1) = trusted (f inp2).

  Definition ni_1 : Prop :=
    forall t, let f := (fun u => trusted (f ⟨ t | u ⟩)) in
          constant f.

  Goal ni_1 <-> ni_0. Proof. firstorder. Qed. 
  (* TODO: Is there a definition where we need to assume function existentionality? *)
  (* There is probably a version where we need to use exists *)


  Goal forall {A} {B} (f1 f2 : A -> B) , f1 = f2 -> forall x, f1 x = f2 x.
  Proof.
    congruence.
  Save temp.


  Definition ni_2 : Prop :=
    exists tr_trans,
      forall u,
      tr_trans = fun t => trusted (f ⟨ t | u ⟩).

  Goal ni_1 <->  ni_2.
  Proof.
    split; red in *; intros; simpl in *; cycle 1.
    - destruct H; subst f0; red; intros.
      generalize (H a).
      generalize (H a').
      intros; subst.
      specialize (temp _ _ H1 t).
      clear H1 H.
      auto. (* What the hell.. This should be much easier *)

    - exists (fun t => trusted (f ⟨ t | 0 ⟩)). (* The fact that there is a zero makes this a little sad *)
      intros.
      apply functional_extensionality.
      firstorder.
  Qed.
End ni_defs.
