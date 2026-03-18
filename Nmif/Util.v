From Stdlib Require List ssreflect ssrbool.
Import List ListNotations ssreflect ssrbool.

From QuickChick Require Decidability.

Module Dec.
  (* Should this be #[global]? *)
  Notation DecEq := Decidability.Dec_Eq.

  Module Notations.
    Export (notations) Decidability.
  End Notations.
End Dec.

Module List.
  Section nlist.
    Context {A: Type}.
    Fixpoint nlist (a:A) (n : nat) : list A :=
      match n with
      | 0 => []
      | S n' => a :: (nlist a n')
      end.

    (* TODO: Learn ssr rewrite. Also, f_equal? *)
    Lemma nlist_len: 
      forall n (a:A), length (nlist a n) = n. 
    Proof.
      elim; first by [].
      by simpl; auto.
    Qed.

    Lemma nlist_content: 
      forall n (a:A), 
        Forall (fun a' => a' = a) (nlist a n). 
    Proof.
      elim; first by [].
      by simpl; auto.
    Qed.
  End nlist.
End List.
