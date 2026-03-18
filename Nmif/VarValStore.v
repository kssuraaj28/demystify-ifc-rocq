From Stdlib Require ssreflect ssrbool FunctionalExtensionality. 
Import ssreflect ssrbool FunctionalExtensionality.

Require Util Tacs.
Import Util.Dec Util.BoolPred Tacs.

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

  Definition store_to_view (s: Store) (p: pred Vars) : StoreView :=
    fun v => if p v is true then Some (s v) else None.

  Definition view_to_store (sv: StoreView) (s_old: Store) : Store :=
    fun v => if sv v is (Some vl) then vl else s_old v. 
End store.

(* Without dependent types, you lose the cool type inference.. *)
Module Notations.
  (* TODO: Perhaps we want to have something like a notation key / delimiter?  *)
  Notation "⟨ s | p ⟩" := (store_to_view s p)(only parsing). 
  Notation "⟨ sv → s ⟩" := (view_to_store sv s)(only parsing). (* TODO: Some warning here. *)
  Section test.
    Context `{!VarPrm, !ValPrm}.
    Variable (s: Store) (sv: StoreView) (p : pred Vars).
    Check ⟨ s | p ⟩.
    Check ⟨ sv → s ⟩.
  End test.
End Notations.
