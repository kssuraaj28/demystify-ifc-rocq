From Stdlib Require ssreflect ssrbool. 
Import ssreflect ssrbool.

Require Util VarVal Tacs.
Import VarVal Util.Notations Tacs.

Section store.
  Context `{!VarPrm, !ValPrm}.

  Definition Store := Vars -> Vals.
  Definition get_from_store (st : Store) (v : Vars) : Vals := st v.
  Definition update_to_store (st : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if (v = v')? is true then vl else st v'.  (* The double colon in vars_deceq is needed here. *)

  Definition StoreView (p : pred Vars) := {v: Vars | p v} -> Vals.

  (* 
    I wonder whether it makes sense to use Ltac2 for this..
    I would want to see how destruct, etc. are used
  *)
  Section store_to_view.
    Context {p: pred Vars} (s: Store).

    Let def : StoreView p. Proof.
      intro vp.
      destruct vp as [v _].
      exact (s v).
    Defined.

    Definition store_to_view : StoreView p := ltac:(hnf_clean (def)).
  End store_to_view.


  Section view_to_store.
    Context {p} (sv : StoreView p) (s: Store).
    (* There is a trick to {p} in previous also. *)

    Let def : Store. Proof.
      intro var.
      destruct (p var) eqn: ?; ltac2:(goals [@TR; @FLS]).

      [FLS]: { exact (s var). }

      [TR]: {
        refine (sv _).
        unshelve esplit; [exact var | assumption].
      }
    Defined.

    Definition view_to_store : Store := 
      ltac:(hnf_clean def).
  End view_to_store.
End store.

Module Notations.
  (* TODO: Perhaps we want to have something like a notation key / delimiter?  *)
  Notation "⟨ s ⟩" := (store_to_view s).
  Notation "⟨ sv → s ⟩" := (view_to_store sv s).
End Notations.
