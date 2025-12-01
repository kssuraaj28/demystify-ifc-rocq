Module Type PartialOrder.
  Parameter Carrier : Set.
  Parameter Ordering : Carrier -> Carrier -> Set.
  Axiom Refl : forall x, Ordering x x. (* Can I use notations? TODO *)
  Axiom Antisym : forall x y, Ordering x y
                              -> Ordering y x
                              -> x = y.
  Axiom Trans : forall x y z, Ordering x y
                              -> Ordering y z
                              -> Ordering x z.
End PartialOrder.


(* TODO: How to have local testing examples? *)
Module  Examples.
  (* I don't actually like this module approach. Seems second class *)
  (* I might want to use typeclasses instead.. *)
  Module M3 : PartialOrder. (* I don't know when we should use <: vs :. I also don't like this stupid highlighing in vim *)

    Inductive Carrier' : Set :=
      | root
      | alice
      | bob
      | chuck
      | any.


    Definition Carrier := Carrier'.

    Reserved Notation "x ≼ y" (at level 20).

    (* I don't like this renaming nonsense *)
    Inductive Ordering' : Carrier -> Carrier -> Prop :=
      | root_top (e : _) : e ≼ root
      | any_bot (e : _) : any ≼ e
      | refl (e : _) : e ≼ e
    where "x ≼ y" :=  (Ordering' x y). 

    Definition Ordering := Ordering'.

    (* I would like to not restate the theorem.. *)
    Theorem Refl : forall x, Ordering x x.
    Proof.
      intros; constructor.
    Qed.

    Theorem Antisym : forall x y, Ordering x y
                                -> Ordering y x
                                -> x = y.
    Proof.
      repeat inversion 1; auto.
    Qed.

    Theorem Trans : forall x y z, Ordering x y
                                -> Ordering y z
                                -> Ordering x z.
    Proof.
      repeat inversion 1; subst; auto; constructor. (* This is a proof that does not deserve to be good *)
    Qed.
  End M3.

End Examples.
