From Stdlib Require List ssreflect ssrbool ssrfun.
Import List ListNotations ssreflect ssrbool ssrfun.

From Ltac2 Require Ltac2 Printf.
Import Ltac2 Printf.

Require Tacs.
Import Tacs Tacs.Cook.


Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

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
  Import Tacs.Cook.
  #[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
  Ltac2 Set this_cookbook_ := create_new_cookbook.

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

  Lemma combine_extend2_nil_l {A B} lb (da:A) (db:B) :
    ltac2:(cbn_eq (combine_extend2 [] lb da db)).
  Proof. done. Qed.

  Lemma combine_extend2_nil_r {A B} la (da:A) (db:B) :
    ltac2:(cbn_eq (combine_extend2 la [] da db)).
  Proof. case: la; done. Qed.

  (* Maybe use Ltac2 to define this.. *)
  Definition combine_extend3 {A B C}
    (la : list A) (lb : list B) (lc : list C)
    (da : A) (db : B) (dc : C) : list (A * B * C) :=
      combine_extend2 (combine_extend2 la lb da db) lc (da,db) dc.

  Definition combine_extend4 {A B C D}
    (la : list A) (lb : list B) (lc : list C) (ld: list D)
    (da : A) (db : B) (dc : C) (dd: D) : list (A * B * C * D) :=
      combine_extend2 (combine_extend3 la lb lc da db dc) ld (da,db,dc) dd.

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

  Ltac2 Set this_cookbook_ as old :=
    add_stirstep 2
      ltac1:(match goal with
             | |- Forall _ (combine_extend2 _ _ _ _) => apply/Forall_combine2_ind1; [move=> ?; apply|..]
             | |- Forall _ (combine_extend2 _ _ _ _) => apply/Forall_combine2_ind2; [move=> ?; apply|..]
             end)
      "Forall_combine2_ind" old.


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

  Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(apply:Forall_combine2_same) "Forall_combine2_same" old.

  Ltac2 Set this_cookbook_ as old := add_stirstep 2 
    ltac1:(lazymatch goal with |- Forall _ (_ ++ _) => apply/Forall_app; split end)
    "Forall_app" old.
  
  Section test.
    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()). (* Maybe keep only 1 *)
    Generalizable All Variables.
    Goal `(Forall (A := A) P (l1 ++ l2)).
    Proof.  move=> *; cook.  Abort.
  End test.
  
  (* A high good tactic consumes 'low grade' hypotheses (in context), and produces high grade hypotheses (intros) *)
  Ltac Forall_inv H :=   
    (idtac; move: H=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _)).
  Ltac2 Set this_cookbook_ as old := add_cookstep 1 ltac1:(someh Forall_inv) "Forall_inv" old.


  (* TODO: Test for these also *)
  Ltac2 Set this_cookbook_ as old := add_stirstep 1
    ltac1:(lazymatch goal with |- Forall _ (map _ _) => apply/Forall_map end)
    "Forall_map" old.

  Ltac2 Set this_cookbook_ as old :=
    add_stirstep 1 ltac1:(rewrite -> combine_extend2_nil_l in * ) "combine_extend2_nil_l" old.
  Ltac2 Set this_cookbook_ as old :=
    add_stirstep 1 ltac1:(rewrite -> combine_extend2_nil_r in * ) "combine_extend2_nil_r" old.

  Ltac2 this_cookbook () := this_cookbook_ ().
  Hint Extern 10 => lazymatch goal with _ =>  apply/Forall_forall end : trickbag.
End List.


(* This is a decent forward reasoning tactic *)
Ltac if_easy_goals :=
  (* In Ltac, doing match goals will do focus *)
  (idtac; (* TODO: harden. This will change hyps though.. *)
  match goal with
  |- context [if ?b then _ else _] =>  
      let e := fresh in let v := fresh in 
      move e: b=> v; move: v e;
      ensure_goals <= 1 (idtac; case=> ?; try done) (* TODO: Parameterize *)
  end).
Section test.
  Goal forall b, if b then True else False.
  Proof. move=> ?. if_easy_goals. Abort.
End test.
Ltac2 Set this_cookbook_ as old := add_cookstep <= 1 ltac1:(if_easy_goals) "if_easy_goals" old.

(* 
  Maybe it is not worth forcing goal count in cook.
  This is certainly a very very good forward reasoning tactic.
*)
(* The is_constructor check below is delegated to Ltac1; it could equivalently
   be written in Ltac2 by inspecting Constr.Unsafe.kind for a Constructor node. *)
Ltac2 cnstrct_eq_gl () :=
  let t := fun () =>
    lazy_match! goal with
    | [ |- ?a = ?b ] =>
      let hl := head a in
      let hr := head b in
      if Constr.equal hl hr then
        ltac1:(f |- is_constructor f; congr f) (Ltac1.of_constr hl)
      else softfail_m "cnstrct_eq_gl" (fprintf "heads differ: %t vs %t" hl hr) 
    end in
  precise_harden t None false true. (* You don't really touch the hypothesis here! *)

Ltac cnstrct_eq_gl := ltac2:(cnstrct_eq_gl ()).


Section test.
  Goal forall n m, S n = S m.
  Proof. move=> *. cnstrct_eq_gl. Abort.

  Goal forall (n1 n2 m1 m2: nat), (n1, n2) = (m1, m2).
  Proof. move=> *. cnstrct_eq_gl. Abort.
End test.

Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1 ltac1:(match goal with H : Some _ = Some _ |- _ => move:H; case=> H end) "some_eq_hyp" old.

(* TODO: This is no longer built into the tactic  *)
Ltac2 Set this_cookbook_ as old := 
  add_cookstep 1 ltac1:(progress (move=> * )) "move=> *" old.

Ltac2 Set this_cookbook_ as old := 
  add_cookstep 1 
    ltac1:(
      match goal with 
      |- context [match ?v with _ => _ end] =>  
        is_var v;  
        ensure_goals 1 (idtac; case: v) => * (* case: ensures that v does not appear anywhere else *)
      end)
   "safe_case" old.

Section test.
  Variable P : nat -> Prop.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["safe_case"]) ().
  Ltac2 Eval print_cookbook curr_cookbook.
  Ltac2 Eval print_cookbook curr_stirbook.
  Ltac2 Set cook_debug := 2.
  Goal forall x: (nat*nat), let: (n,_) := x in  P n.
  Proof. 
    move=> *; goal_hygiene.
    Succeed cook_step; (cook_step || idtac "no more").
    Fail stir_step. 
    Succeed progress cook.
  Abort.
End test.

  
Ltac2 Set this_cookbook_ as old := 
  add_stirstep 1 
    ltac1:(match goal with  
           | H: ?x = ?b |- context [if ?x then _ else _] => is_constructor b; pattern x; rewrite H
           | H: ?b = ?x |- context [if ?x then _ else _] => is_constructor b; pattern x; rewrite -H
           end)
    "if_w_hyp_eq" old.

Section test.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["if_w_hyp_eq"]) ().
  Ltac2 Eval print_cookbook curr_cookbook.  Ltac2 Eval print_cookbook curr_stirbook.
  Ltac2 Set cook_debug := 2.
  Goal forall b, b = true -> if b then True else False.
  Proof. 
    Succeed now cook. (* Backward reasoning *)
    Succeed now stir.
    Fail cook_step.
    Fail stir_step.
    move=> ? ?.
    stir_step.
    exact I.
  Qed.
End test.


(* TODO: maybe better to have  
Example map_nil_simpl {A B} (f: A -> B) := (erefl : ltac2:(cbn_eq (map f []))). 
*)
Lemma map_nil_simpl {A B} (f: A -> B) : ltac2:(cbn_eq (map f [])). Proof. done. Qed.
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> map_nil_simpl in * ) "map_nil_simpl" old.

Lemma if_same {T} (b : bool) (t: T) :
  (if b then t else t) = t.
Proof.  case: b; done. Qed.

Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> if_same in * ) "if_same" old.

Lemma fst_pair {A B} (a : A) (b : B) : ltac2:(cbn_eq (a, b).1). Proof. done. Qed.
Lemma snd_pair {A B} (a : A) (b : B) : ltac2:(cbn_eq (a, b).2). Proof. done. Qed.

Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> fst_pair in * ) "fst_pair" old.
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> snd_pair in * ) "snd_pair" old.

Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(progress cbn [andb orb]) "cbn_andb_orb" old.

Ltac2 Set this_cookbook_ as old := add_stirstep 0 ltac1:(done) "done" old.

Ltac2 Set this_cookbook_ as old := add_cookstep 1 ltac1:(progress subst) "subst" old.

Ltac2 this_cookbook () := this_cookbook_ ().

(* TODO: multimatch vs lazymatch in trickbag *)
Hint Extern 10 => multimatch goal with H : _ = _ |- _ => rewrite H end : trickbag. (* TODO: This should go somewhere good *)
Hint Extern 10 => multimatch goal with H : _ = _ |- _ => rewrite -H end : trickbag. (* TODO: This should go somewhere good *)
