Section po.
  Variables (Carrier : Set) (Ordering : Carrier -> Carrier -> Prop).
  Notation "x ≼ y" := (Ordering x y) (at level 70).

  (* TODO: Generalizable varibles *)
  (* TODO: This has to eventually be a typeclass, I think *)
  Record PartialOrder := {
    refl : forall x, x ≼ x ;
    antisym : forall x y, x ≼ y -> y ≼ x -> x = y ;
    trans : forall x y z, x ≼ y -> y ≼ z -> x ≼ z ;
    }.

End po.



(* I wish there was a way to define Local Inductive *)
Module Throw.
  (* It is quite sad that Coq does not have local inductive definitions. Seems very 'client-side modules' *)
  Inductive M3 : Set :=  root | alice | bob | chuck | any.

  Reserved Notation "x ≼ y" (at level 70).
  Inductive M3_ord : M3 -> M3 -> Prop :=
    | root_top (e : _) : e ≼ root
    | any_bot (e : _) : any ≼ e
    | refl (e : _) : e ≼ e
  where "x ≼ y" :=  (M3_ord x y). 

  (* This should be 'Instance', eventually*)
  Lemma M3_po : PartialOrder M3 M3_ord. Proof.
    firstorder; 
    repeat match goal with [ H : _ ≼ _ |- _] => inversion H; clear H; subst end; 
    congruence || constructor.
  Qed.

End Throw.
