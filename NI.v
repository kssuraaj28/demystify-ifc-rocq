(*
In my math, these hold obviously 

From Stdlib Require Import Logic.ClassicalFacts.

*)
From Stdlib Require Import Logic.FunctionalExtensionality.

(* This is function composition *)
Notation "x ;; y" := (fun i => y(x(i))) (at level 10).

Section constant.
  Context {A B : Type}.
  Variable f : A -> B.

  Definition constant : Prop := forall a a', f a = f a'. 
  Definition constant' : Prop := exists b, forall a, f a = b.  (* This really is an experiment that should not be visible outside other things *)
End constant.

Definition example (x : Empty_set) : Empty_set :=  match x with end. 
Goal constant example. Proof. cbv; intuition. Qed. 
Goal ~ constant' example. Proof. cbv; inversion 1; intuition. Qed.



(* The many different ways to define Noninterference *)
(* First, we consider two nonempty sets. 
TODO: Parameterize them later..
*)

(* TODO: Do we need these nonempty axioms? *)
Parameter SecretVal : Set.
Axiom SecretNonempty : inhabited SecretVal : Prop.

Parameter PublicVal : Set.
Axiom PublicNonempty : inhabited PublicVal : Prop.

Record State : Set := {secret : SecretVal ; public : PublicVal}.
Notation "⟨ s | p ⟩" := {| secret := s ; public := p |} (at level 5). (* Can I do this without | *)

Definition Computation : Set := State -> State.

(* Given a computation, you partially apply a value *)
Definition fix_secret (comp : Computation) (secret : SecretVal) : PublicVal -> State := 
  fun public => 
    let inp := ⟨ secret | public ⟩ in
    comp inp.

Definition fix_public (comp : Computation) (public : PublicVal) : SecretVal -> State := 
  fun secret => 
    let inp := ⟨ secret | public ⟩ in
    comp inp.

Section ni_defs.
  Variable comp : Computation.

  (* The secrets do not affect the public part, for p_inp*)
  Definition ni_for_p (pub_inp : _) :=
    let p_comp := fix_public comp pub_inp in
      constant (p_comp ;; public).

  Definition ni_1 : Prop :=
    forall pub_inp, ni_for_p pub_inp.

  Definition ni_2 : Prop := 
    forall s1 s2,
      let s1_comp := fix_secret comp s1 in
      let s2_comp := fix_secret comp s2 in
      s1_comp ;; public = s2_comp ;; public.

  (* This is a 'parameterized' definition. In some sense, it is a family of definitions *)
  Definition ni_3 (tested_secret : SecretVal) : Prop := 
    let ts_comp := fix_secret comp tested_secret in
    forall secret,
      let s_comp := fix_secret comp secret in
      ts_comp ;; public = s_comp ;; public.


  (* Maybe, this is the right use case for ltac2... *)

  (* This is garbage *)
  Ltac unfold_these := 
    unfold ni_1 in *; intuition; 
    unfold ni_2 in *; intuition;
    unfold ni_3 in *; intuition;
    unfold ni_for_p in *; intuition; 
    unfold constant in *; intuition; (* This really needs to be refactored into a custom tactic. *)
    unfold fix_secret in *; intuition;
    unfold fix_public in *; intuition.

  Goal ni_1 -> ni_2.
  Proof.
    unfold_these. (* Here, I think that I actually disagree a little bit with Adam Chlipala *)
    auto using functional_extensionality.
  Qed.

  Goal ni_2 -> ni_1.
  Proof.
    unfold_these.
    specialize H with (s1 := a) (s2 := a').  (* This is not a good tactic invocation*)
    apply (equal_f H). (* This is garbage *)
  Qed.
 


  Section ni23.
    Variable s : SecretVal.
    Notation ni_3 := (ni_3 s).
    Goal ni_3 -> ni_2.
    Proof.
      unfold_these.
      generalize (H s1); generalize (H s2); clear H; intros.
      rewrite <- H; rewrite <- H0; auto. (* This really needs to be automatic*)
    Qed.

    Goal ni_2 -> ni_3.
    Proof.
      unfold_these.
    Qed.
  End ni23.



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




  Theorem ni_12 : forall s, (ni_2 s <-> ni_1). (* (forall s, ni_2 s) also equal?  *)
  Proof.
    cbv; split; intros; simpl in *.
    - generalize (H a).
      generalize (H a').
      clear H.
      intros.
      rewrite  H in H0.
      match goal with 
        [ H : ?f = ?g |- _ ] => specialize (equal_f H); clear H; intros 
      end; firstorder. (* This is kinda disgusting *)

    - apply functional_extensionality; intros;
      match goal with 
        [H : forall a b c, _ , a: _ , b: _ , c: _ |- _] => specialize (H a b c)
      end; auto.
  Qed.


  Goal forall ts, (ni_2 ts -> (forall s, ni_2 s)).
  Proof.
    (* Note how this really depends on the definition of ni_2 *)
    unfold ni_2; simpl; intros.
    (* This pattern can be a really cool tactic *)
    generalize (H s).
    generalize (H secret0).
    clear H.
    intros.
    rewrite <- H.
    rewrite <- H0.
    auto.
    (* Woah, we can actually even prove this with coq's garbage = *)
  Qed.


  (* The other direction is obvious *)
  Goal forall (T : Type) (P : T -> Prop) x, ((forall x', P x') -> P x).
  Proof.
    firstorder.
  Qed.

  (* Can I prove this from previous? This seems a little stupid. I don't know whether I am proving something harder or easier. *)
  Goal (forall s, ni_2 s) <-> ni_1.
  Proof.
    split.
    - admit.
    - intros. rewrite temp. auto.
    cbv; split; intros; simpl in *.
    - generalize (H a a'). 
      clear H.
      intros.
      match goal with 
        [ H : ?f = ?g |- _ ] => specialize (equal_f H); clear H; intros 
      end; firstorder. (* This is kinda disgusting *)
    - apply functional_extensionality;
      firstorder.
  Qed.



  (* Something using exists *)
  Definition ni_3 : Prop := exists pub_trans, forall s, pub_trans = fun p => public (f ⟨ s | p ⟩).

  Axiom temp : inhabited SecretVal \/ ~inhabited (SecretVal). (* This is nothing really special *)

  Goal ni_1 <->  ni_3.
  Proof.
    unfold ni_1; unfold ni_3; split; intros; cycle 1.
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
