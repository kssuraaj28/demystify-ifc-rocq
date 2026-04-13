From Stdlib Require List ssreflect ssrbool.
Import List ListNotations ssreflect ssrbool.

Require Tacs.
Import Tacs.


Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Module DecEq.
  (* 
    I got this from QuickChick.
    Ideally there should be one library for all of this.
    TODO
  *)
  Class DecEq (A : Type) := {
    dec_eq : forall (x y : A), decidable (x = y)
  }.

  Module Notations.
    Notation "x '=?' y" := 
        (match (dec_eq x y) with
           | left _ => true
           | right _ => false
         end) (at level 100).

  End Notations.
End DecEq.

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
      elim=> /=; auto.
    Qed.

    Lemma nlist_content: 
      forall n (a:A), 
        Forall (fun a' => a' = a) (nlist a n). 
    Proof.
      elim=> /=; auto.
    Qed.
  End nlist.

  (* TODO: What naming conventions am I using? *)
  Ltac stp_Forall_app_gl := lazymatch goal with |- Forall _ (_ ++ _) => apply/Forall_app end.
  
  Section test.
    Generalizable All Variables.
    Goal `(Forall (A := A) P (l1 ++ l2)).
    Proof.  move=> *; stp_Forall_app_gl.  Abort.
  End test.
  
  (* A high good tactic consumes 'low grade' hypotheses (in context), 
    and produces high grade hypotheses *)
  Ltac Forall_inv H :=   move: H=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _).
  (* TODO: Test for these also *)
End List.
