From Stdlib Require List ssreflect ssrbool ssrfun.
Import List ListNotations ssreflect ssrbool ssrfun.

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
  Fixpoint combine_extend2 {A B} 
    (la : list A) (lb : list B)
    (da : A) (db : B) : list (A * B) :=
      match la, lb with
      | ha :: la' , hb :: lb' => (ha , hb) :: combine_extend2 la' lb' da db
      | [] , lb => map (fun b => (da, b)) lb
      | la , [] => map (fun a => (a, db)) la
      end.
  
  Goal combine_extend2 [1; 3] [true] 10 false = [(1, true); (3, false)].  
  Proof. done. Qed.

  Goal combine_extend2 [1; 3] [true; false; false] 10 false = [(1, true); (3, false); (10, false)].
  Proof. done. Qed.

  (* Maybe use Ltac2 to define this.. *)
  Definition combine_extend3 {A B C}
    (la : list A) (lb : list B) (lc : list C)
    (da : A) (db : B) (dc : C) : list (A * B * C) :=
      combine_extend2 (combine_extend2 la lb da db) lc (da,db) dc.

  Lemma combine_extend3_empty:
    forall {A B C} l2 l3 (d1 :A) (d2: B) (d3: C),
      combine_extend3 [] l2 l3 d1 d2 d3 =
      map (fun '(e2, e3) => (d1,e2,e3))(combine_extend2 l2 l3 d2 d3).
  Proof.
    move=> A B C; elim=> [|h2 t2 IH] l3 d1 d2 d3.
    - by rewrite /combine_extend3 /= map_map.
    - case: l3 => [|h3 t3].
      + by rewrite /combine_extend3 /= !map_map.
      + rewrite /combine_extend3 /= -/(combine_extend3 [] t2 t3 d1 d2 d3).
        by rewrite IH.
  Qed.

  Lemma Forall_combine2_ind1 :
     forall {A B} P l1 l2 (d1:A) (d2:B) Q,
     (forall e, Q e.1 -> P e) ->
     Forall Q l1 -> Q d1 ->
     Forall P (combine_extend2 l1 l2 d1 d2).
  Proof.
    move=> A B P; elim=> [|h1 t1 IH] l2 d1 d2 Q HPQ HQ HQd /=.
    - elim: l2 => [|h2 t2 IH2] /=.
      + exact: Forall_nil.
      + by apply: Forall_cons; [apply: HPQ | ].
    - have HQh1 := Forall_inv HQ. have HQt1 := Forall_inv_tail HQ. clear HQ.
      case: l2 => [|h2 t2] /=.
      + apply: Forall_cons; first by apply: HPQ.
        clear IH HQh1. elim: t1 HQt1 => [|h t IHt] /= HQt1.
        * exact: Forall_nil.
        * have ? := Forall_inv HQt1. have ? := Forall_inv_tail HQt1.
          by apply: Forall_cons; [apply: HPQ | apply: IHt].
      + apply: Forall_cons; first by apply: HPQ.
        exact: (IH _ _ _ _ HPQ HQt1 HQd).
  Qed.

  Lemma Forall_combine2_ind2 :
     forall {A B} P l1 l2 (d1:A) (d2:B) Q,
     (forall e, Q e.2 -> P e) ->
     Forall Q l2 -> Q d2 ->
     Forall P (combine_extend2 l1 l2 d1 d2).
  Proof.
    move=> A B P; elim=> [|h1 t1 IH] l2 d1 d2 Q HPQ HQ HQd /=.
    - elim: l2 HQ => [|h2 t2 IH2] HQ /=.
      + exact: Forall_nil.
      + have ? := Forall_inv HQ. have ? := Forall_inv_tail HQ.
        by apply: Forall_cons; [apply: HPQ | apply: IH2].
    - case: l2 HQ => [|h2 t2] HQ /=.
      + apply: Forall_cons; first by apply: HPQ.
        clear IH. elim: t1 => [|h t IHt] /=.
        * exact: Forall_nil.
        * by apply: Forall_cons; [apply: HPQ | ].
      + have HQh2 := Forall_inv HQ. have HQt2 := Forall_inv_tail HQ.
        apply: Forall_cons; first by apply: HPQ.
        exact: (IH _ _ _ _ HPQ HQt2 HQd).
  Qed.


  Lemma Forall_combine2_same:
    forall {A} P l (d: A),
      Forall (fun x => P (x,x)) l ->
      Forall P (combine_extend2 l l d d).
  Proof.
    move=> A P; elim=> [|h t IH] d HF /=.
    - exact: Forall_nil.
    - have ? := Forall_inv HF. have ? := Forall_inv_tail HF.
      by apply: Forall_cons; [|apply: IH].
  Qed.

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
