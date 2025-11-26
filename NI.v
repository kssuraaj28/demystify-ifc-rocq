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

Definition set_secret (secret : SecretVal) : PublicVal -> State := 
  fun public =>  ⟨ secret | public ⟩.

Definition set_public (public : PublicVal) : SecretVal -> State := 
  fun secret => ⟨ secret | public ⟩.

Definition Computation : Set := State -> State.

Section ni_defs.
  Variable comp : Computation.

  Definition ni_for_p (pub_inp : _) :=
     constant ((set_public pub_inp ;; comp ;; public) : SecretVal -> PublicVal).

  Definition ni_1 : Prop :=
    forall pub_inp, ni_for_p pub_inp.

  (* This is really the 'real' definition of NI... *)
  Definition ni_2 : Prop := 
    forall s1 s2,
      set_secret s1 ;; comp ;; public = set_secret s2 ;; comp ;; public.

  Notation "f || g" := (fun i => ⟨ f i | g i ⟩). (* Parallel composition  *)

  (* More like a 'UMP style' *)
  Definition ni_3 : Prop :=
    forall (A : Type) (sinp1 sinp2: A -> _) (pinp : A -> _), 
        (sinp1 || pinp)  ;; comp ;; public = (sinp2 || pinp) ;; comp ;; public. (* TODO: Why can A not be declared implicit? *)



  (* This is a 'parameterized' definition. In some sense, it is a family of definitions *)
  Definition ni_4 (tested_secret : SecretVal) : Prop := 
    forall secret,
      set_secret tested_secret ;; comp ;; public = set_secret secret ;; comp ;; public.



  (* Maybe, this is the right use case for ltac2... *)

  (* This is garbage *)
  Ltac unfold_these := 
    unfold ni_1 in *; intuition; 
    unfold ni_2 in *; intuition;
    unfold ni_3 in *; intuition;
    unfold ni_for_p in *; intuition; 
    unfold constant in *; intuition; (* This really needs to be refactored into a custom tactic. *)
    unfold set_secret in *; intuition;
    unfold set_secret in *; intuition.

  Goal ni_3 -> ni_2.
  Proof.
    unfold_these.
  Qed.

  Goal ni_2 -> ni_3.
  Proof.
    unfold_these.
    apply functional_extensionality.
    intros.
    generalize (sinp1 x).
    generalize (sinp2 x).
    intuition.
    specialize (H s s0).

    Restart.
    unfold_these.
    apply functional_extensionality.
    intros.
    specialize (H (sinp1 x) (sinp2 x)).
    apply (equal_f H). (* This is kinda garbage.. *)
  Qed.

  Goal ni_1 -> ni_2.
  Proof.
    unfold_these. (* Here, I think that I actually disagree a little bit with Adam Chlipala *)
    apply functional_extensionality. (* I think that we actually need function extensionality, because the statement literally reduces to that *)
    firstorder.
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
      generalize (H s1); generalize (H s2); clear H; intros. (*The same forall being quantified multiple ways *)
      rewrite <- H; rewrite <- H0; auto. (* This really needs to be automatic*)
    Qed.

    Goal ni_2 -> ni_3.
    Proof.
      unfold_these.
    Qed.
  End ni23.

  (* What do I need to do? 
  f ;; public = clean (f) ;; public?
  The clean thing?
  Compositon and clean thing..
  Section composition and clean.

  There is the input UMP.
  There are also output UMPs.


  *)




  (* There is probably a version where we need to use exists *)


  (* 
    This is a garbage definition!
    It is essentially always true!
  *)
  Definition garbage (s : SecretVal) : Prop :=
    exists pub_trans,
      (* TODO: forall s used to be here before. Does that make a difference?*)
      pub_trans = fun p => public (comp ⟨ s | p ⟩).


  Goal forall s, garbage s. Proof. eexists; reflexivity. Qed.


  (* Something using exists. Can there be anything else? *)
  Definition ni_4 : Prop := exists pub_trans, forall s, pub_trans = fun p => public (comp ⟨ s | p ⟩).

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
