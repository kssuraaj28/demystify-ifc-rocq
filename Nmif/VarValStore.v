From Stdlib Require ssreflect ssrbool FunctionalExtensionality. 
Import ssreflect ssrbool FunctionalExtensionality.

Require Util Tacs.
Import Util.Dec.

Class VarPrm := {Vars : Type ; vars_deceq :: DecEq Vars}. 
Class ValPrm := {Vals : Type}.

Section store.
  Import Util.Dec.Notations.
  Context `{!VarPrm, !ValPrm}.

  Definition Store := Vars -> Vals.
  Definition get_from_store (st : Store) (v : Vars) : Vals := st v.
  Definition update_to_store (st : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if (v = v')? is true then vl else st v'.  (* The double colon in vars_deceq is needed here. *)

  (* I don't get dependent types :(. Maybe once I am good, I will use them *)
  Definition StoreView := Vars -> option Vals.

  Definition store_to_view (p: pred Vars) (s: Store) : StoreView :=
    fun v => if p v is true then Some (s v) else None.

  Definition view_to_store (sv: StoreView) (s_old: Store) : Store :=
    fun v => if sv v is (Some vl) then vl else s_old v. 
End store.

(* Without dependent types, you lose the cool type inference.. *)
Module Notations.
  (* TODO: Perhaps we want to have something like a notation key / delimiter?  *)
  Notation "⟨ s | p ⟩" := (store_to_view p s).
  Notation "⟨ sv → s ⟩" := (view_to_store sv s). (* TODO: Some warning here. *)
  Section test.
    Context `{!VarPrm, !ValPrm}.
    Variable (s: Store) (sv: StoreView) (p : pred Vars).
    Check ⟨ s | p ⟩.
    Check ⟨ sv → s ⟩.
  End test.
End Notations.

Section thms.
  Import Notations.
  Context `{!VarPrm, !ValPrm}.

  Theorem storeview_eq: 
    forall s1 s2 p inp,
      ⟨ s1 | p ⟩ = ⟨ s2 | p ⟩ -> p inp -> 
      s1 inp = s2 inp.
  Proof.
    move=>??? inp; rewrite/⟨_|_⟩.
    by move=> /equal_f/(_ inp)/[swap]->[].
  Qed.

End thms.
