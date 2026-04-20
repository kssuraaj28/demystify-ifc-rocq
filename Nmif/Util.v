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
  Fixpoint combine_extend {A B} 
    (la : list A) (lb : list B)
    (da : A) (db : B) : list (A * B) :=
      match la, lb with
      | ha :: la' , hb :: lb' => (ha , hb) :: combine_extend la' lb' da db
      | [] , lb => map (fun b => (da, b)) lb
      | la , [] => map (fun a => (a, db)) la
      end.
  
  Goal combine_extend [1; 3] [true] 10 false = [(1, true); (3, false)].  
  Proof. done. Qed.

  Goal combine_extend [1; 3] [true; false; false] 10 false = [(1, true); (3, false); (10, false)].
  Proof. done. Qed.

  (* TODO: What naming conventions am I using? *)
  Ltac stp_Forall_app_gl := lazymatch goal with |- Forall _ (_ ++ _) => apply/Forall_app end.
  
  Section test.
    Generalizable All Variables.
    Goal `(Forall (A := A) P (l1 ++ l2)).
    Proof.  move=> *; stp_Forall_app_gl.  Abort.
  End test.
  
  (* A high good tactic consumes 'low grade' hypotheses (in context), and produces high grade hypotheses (intros) *)
  Ltac Forall_inv H :=   move: H=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _).
  (* TODO: Test for these also *)
End List.
