
Set Implicit Arguments.
(* 
https://stackoverflow.com/questions/71143362/best-practices-for-parametrized-coq-libraries
 *)

(* My styling convention is just this
If Check _ : myid ??_ _ _?? typechecks, then I will write MyId
*)

(* Too many nested sections seem bad.. 
*)
Section po.

  (* I don't know whether this should be a Class.. *)
  Record PartialOrderData : Type := {
    Carrier : Type;
    Ordering (e e' : Carrier) : Prop
  }.

  Section prf.
    Variable data : PartialOrderData.
    Notation "x ≼ y"  := (Ordering data x y) (at level 70). (* Can we do this without spliting? *)
    Check _ ≼ _.

    Record PartialOrderProof  : Prop := {
      refl : forall x, x ≼ x ;
      antisym : forall x y, x ≼ y -> y ≼ x -> x = y ;
      trans : forall x y z, x ≼ y -> y ≼ z -> x ≼ z ;
    }.
  End prf.

  (* TODO: Generalizable varibles *)
  (* TODO: I think that this eventually has to become a typeclass... *)
  Record PartialOrder : Type := {
    data : PartialOrderData; (* What happens when you use :> *)
    prf : PartialOrderProof data
    }.
End po.




(* I wish there was a way to define Local Inductive. 
   Apparently, there is no way to do this.
*)
Module Throw.
  (* It is quite sad that Coq does not have local inductive definitions. Seems very 'client-side modules' *)
  (* TODO: Maybe work with FiniteSets?
  Another thing that can be done is to raise the level of abstraction, and have an Inductive 'set former', which seems fine also
  *)
  Inductive M3Car : Set :=  root | alice | bob | chuck | any.

  Reserved Notation "x ≼ y" (at level 70).
  Inductive M3Ord : M3Car -> M3Car -> Prop :=
    | root_top (e : _) : e ≼ root
    | any_bot (e : _) : any ≼ e
    | refl (e : _) : e ≼ e
  where "x ≼ y" :=  (M3Ord x y). 

  Definition M3Data := 
    {|Carrier := M3Car; Ordering := M3Ord |}.

  Lemma M3prf : PartialOrderProof M3Data.  (* This should be Instance? *)
  Proof.
    firstorder; unfold Ordering, Carrier in *; simpl in *;
    repeat match goal with [ H : _ ≼ _ |- _] => inversion H; clear H; subst end; 
    congruence || constructor.
  Qed.


  (* Questions: 
  - Best way to do this with typeclasses?
  - Controlling opaqueness for a part of the proof? Is it possible?
    Does it matter?
  *)
  Definition M3 : PartialOrder := {| data := M3Data ; prf := M3prf|}.


  Section example.
    Hint Constructors M3Ord : core.
    Hint Extern 10 => match goal with [ H : _ ≼ _ |- _ ] => inversion H end : core.

    Goal root ≼ root. Proof. auto. Qed.
    Goal any ≼ root. Proof. auto. Qed.
    Goal alice ≼ root. Proof. auto. Qed.
    Goal any ≼ bob. Proof. auto. Qed.
    Goal any ≼ bob. Proof. auto. Qed.
    Goal ~ alice ≼ bob. Proof. auto.  Qed.
    Goal ~ bob ≼ alice. Proof. auto. Qed.
    Goal ~ chuck ≼ alice. Proof. auto. Qed.
    Goal forall x, x ≼ x. Proof. auto. Qed.
    Goal forall x y z, x ≼ y -> y ≼ z -> x ≼ z. Proof. auto. Qed.
  End example.
End Throw.
