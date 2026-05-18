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
    combine_extend2 [] lb da db = map (fun b => (da, b)) lb.
  Proof. done. Qed.

  Lemma combine_extend2_nil_r {A B} la (da:A) (db:B) :
    combine_extend2 la [] da db = map (fun a => (a, db)) la.
  Proof. case: la; done. Qed.

  (* Uniform cons lemmas: combine_extend2 advances both lists by one,
     using the default when a list has run out. *)
  Lemma combine_extend2_consl {A B} x (X : list A) (Y : list B) dX dY :
    combine_extend2 (x :: X) Y dX dY =
    (x, hd dY Y) :: combine_extend2 X (tl Y) dX dY.
  Proof.
    case: Y => [|y Y'].
    - case: X => [|x' X']; reflexivity.
    - reflexivity.
  Qed.

  Lemma combine_extend2_consr {A B} (X : list A) y (Y : list B) dX dY :
    combine_extend2 X (y :: Y) dX dY =
    (hd dX X, y) :: combine_extend2 (tl X) Y dX dY.
  Proof. case: X => [|x X']; reflexivity. Qed.

  (* If the 2nd column of the zip is `map g X`, the zip is `map (x => (x, g x)) X`.
     (The hypothesis being a list equality also forces |Y| <= |X|.) *)
  Lemma combine_extend2_map_snd {A B} (X : list A) (Y : list B) dX dY (g : A -> B) :
    map snd (combine_extend2 X Y dX dY) = map g X ->
    combine_extend2 X Y dX dY = map (fun x => (x, g x)) X.
  Proof.
    elim: X Y => [|x X' IH] Y.
    - case: Y => [|y Y'] /=.
      + done.
      + move=> H; discriminate H.
    - rewrite combine_extend2_consl /=. move=> [= Hd Ht].
      congr (_ :: _).
      + congr (_, _). exact: Hd.
      + apply: IH. exact: Ht.
  Qed.

  (* Mirror of combine_extend2_map_snd: if the 1st column is `map h Y`. *)
  Lemma combine_extend2_map_fst {A B} (X : list A) (Y : list B) dX dY (h : B -> A) :
    map fst (combine_extend2 X Y dX dY) = map h Y ->
    combine_extend2 X Y dX dY = map (fun y => (h y, y)) Y.
  Proof.
    elim: Y X => [|y Y' IH] X.
    - case: X => [|x X'] /=.
      + done.
      + move=> H; discriminate H.
    - rewrite combine_extend2_consr /=. move=> [= Hd Ht].
      congr (_ :: _).
      + congr (_, _). exact: Hd.
      + apply: IH. exact: Ht.
  Qed.

  (* Zipping a list against itself is the diagonal. *)
  Lemma combine_extend2_same {A} (l : list A) (d : A) :
    combine_extend2 l l d d = map (fun x => (x, x)) l.
  Proof. elim: l => [| h t IH] //=. rewrite IH //. Qed.

  (* Maybe use Ltac2 to define this.. *)
  Definition combine_extend3 {A B C}
    (la : list A) (lb : list B) (lc : list C)
    (da : A) (db : B) (dc : C) : list (A * B * C) :=
      combine_extend2 (combine_extend2 la lb da db) lc (da,db) dc.

  Definition combine_extend4 {A B C D}
    (la : list A) (lb : list B) (lc : list C) (ld: list D)
    (da : A) (db : B) (dc : C) (dd: D) : list (A * B * C * D) :=
      combine_extend2 (combine_extend3 la lb lc da db dc) ld (da,db,dc) dd.

  Lemma combine_extend4_regroup3 {A B C D}
    (la : list A) (lb : list B) (lc : list C) (ld : list D)
    da db dc dd :
    combine_extend4 la lb lc ld da db dc dd =
    map (fun '(a, b, d, c) => (a, b, c, d))
        (combine_extend2 (combine_extend3 la lb ld da db dd) lc (da,db,dd) dc).
  Admitted. (* TODO: combinatorial induction. *)

  Lemma combine_extend3_regroup2 {A B C}
    (la : list A) (lb : list B) (lc : list C) da db dc :
    combine_extend3 la lb lc da db dc =
    map (fun '(a, c, b) => (a, b, c))
        (combine_extend2 (combine_extend2 la lc da dc) lb (da,dc) db).
  Admitted. (* TODO: combinatorial induction. *)

  Lemma combine_extend3_swap23 {A B C}
    (la : list A) (lb : list B) (lc : list C) da db dc :
    combine_extend3 la lb lc da db dc =
    map (fun '(a, c, b) => (a, b, c)) (combine_extend3 la lc lb da dc db).
  Proof. exact: combine_extend3_regroup2. Qed.

  Lemma combine_extend4_swap34 {A B C D}
    (la : list A) (lb : list B) (lc : list C) (ld : list D) da db dc dd :
    combine_extend4 la lb lc ld da db dc dd =
    map (fun '(a, b, d, c) => (a, b, c, d)) (combine_extend4 la lb ld lc da db dd dc).
  Proof. exact: combine_extend4_regroup3. Qed.

  (* combine_extend3 grouped as ((a,b),c) -- this is the definition. *)
  Lemma combine_extend3_splitr {A B C}
    (la : list A) (lb : list B) (lc : list C) da db dc :
    combine_extend3 la lb lc da db dc =
    combine_extend2 (combine_extend2 la lb da db) lc (da, db) dc.
  Proof. done. Qed.

  (* combine_extend3 grouped as (a,(b,c)) -- zip-with-padding is associative. *)
  Lemma combine_extend3_splitl {A B C}
    (la : list A) (lb : list B) (lc : list C) da db dc :
    combine_extend3 la lb lc da db dc =
    map (fun '(a, (b, c)) => (a, b, c))
        (combine_extend2 la (combine_extend2 lb lc db dc) da (db, dc)).
  Admitted. (* TODO: associativity of combine_extend2-with-padding. *)

  (* Map fusion: a `map` on the first list pulls out of `combine_extend2`. *)
  Lemma combine_extend2_map_l {A A' B} (f : A -> A')
    (X : list A) (Y : list B) (dX : A) (dX': A') (dY : B) :
    dX' = f dX ->
    combine_extend2 (map f X) Y dX' dY =
    map (fun '(x, y) => (f x, y)) (combine_extend2 X Y dX dY).
  Proof.
    move=> ->; elim: X Y => [| x X' IH] Y.
    - rewrite /= map_map //.
    - rewrite map_cons !combine_extend2_consl map_cons IH //.
  Qed.

  (* Map fusion: a `map` on the second list pulls out of `combine_extend2`. *)
  Lemma combine_extend2_map_r {A B B'} (g : B -> B')
    (X : list A) (Y : list B) (dX : A) (dY': B') (dY : B) :
    dY' = g dY ->
    combine_extend2 X (map g Y) dX dY' =
    map (fun '(x, y) => (x, g y)) (combine_extend2 X Y dX dY).
  Proof.
    move=> ->; elim: Y X => [| y Y' IH] X.
    - rewrite /= !combine_extend2_nil_r map_map //.
    - rewrite map_cons !combine_extend2_consr map_cons IH //.
  Qed.

  (* Second list is `map g` of the first: equal length, so defaults are dead. *)
  Lemma combine_extend2_map_self_r {A B} (g : A -> B) (X : list A) dX dY :
    combine_extend2 X (map g X) dX dY = map (fun x => (x, g x)) X.
  Proof. elim: X => [| h t IH] //=. rewrite IH //. Qed.

  (* First list is `map f` of the second: equal length, so defaults are dead. *)
  Lemma combine_extend2_map_self_l {A B} (f : B -> A) (Y : list B) dX dY :
    combine_extend2 (map f Y) Y dX dY = map (fun y => (f y, y)) Y.
  Proof. elim: Y => [| h t IH] //=. rewrite IH //. Qed.

  (* Swapping the two lists transposes the columns. *)
  Lemma combine_extend2_swap {A B} (X : list A) (Y : list B) dX dY :
    combine_extend2 X Y dX dY =
    map (fun '(y, x) => (x, y)) (combine_extend2 Y X dY dX).
  Proof.
    elim: X Y => [| x X' IH] Y.
    - rewrite combine_extend2_nil_l combine_extend2_nil_r map_map //.
    - case: Y => [| y Y'].
      + rewrite combine_extend2_nil_r combine_extend2_nil_l map_map //.
      + rewrite /= IH //.
  Qed.

  (* map o filter over combine_extend2 collapses to a single list when the
     filter predicate factors through one column and the map ignores the
     other -- the discarded column is exactly the one filter desyncs.
     Needs only `q d = false` on the governing column's default. *)
  Lemma map_filter_combine_extend2_ind1 {A B C}
    (l1 : list A) (l2 : list B) d1 d2
    (p : A * B -> bool) (q : A -> bool) (f : A * B -> C) (g : A -> C) :
    (forall x y, p (x, y) = q x) ->
    (forall x y, f (x, y) = g x) ->
    q d1 = false ->
    map f (filter p (combine_extend2 l1 l2 d1 d2)) = map g (filter q l1).
  Proof.
    move=> pq fg qd1.
    elim: l1 l2 => [| x l1' IH] l2.
    - rewrite combine_extend2_nil_l.
      elim: l2 => [| y l2' IH2] //=.
      rewrite pq qd1 /=. exact: IH2.
    - rewrite combine_extend2_consl /=.
      rewrite pq. case: (q x) => /=.
      + rewrite fg IH //.
      + rewrite IH //.
  Qed.

  Lemma map_filter_combine_extend2_ind2 {A B C}
    (l1 : list A) (l2 : list B) d1 d2
    (p : A * B -> bool) (q : B -> bool) (f : A * B -> C) (g : B -> C) :
    (forall x y, p (x, y) = q y) ->
    (forall x y, f (x, y) = g y) ->
    q d2 = false ->
    map f (filter p (combine_extend2 l1 l2 d1 d2)) = map g (filter q l2).
  Proof.
    move=> pq fg qd2.
    elim: l2 l1 => [| y l2' IH] l1.
    - rewrite combine_extend2_nil_r.
      elim: l1 => [| x l1' IH1] //=.
      rewrite pq qd2 /=. exact: IH1.
    - rewrite combine_extend2_consr /=.
      rewrite pq. case: (q y) => /=.
      + rewrite fg IH //.
      + rewrite IH //.
  Qed.

  Lemma combine_extend3_nil1 {A B C}
    (l2 : list B) (l3 : list C) (d1 : A) (d2 : B) (d3 : C) :
    combine_extend3 [] l2 l3 d1 d2 d3 =
    map (fun '(b, c) => (d1, b, c)) (combine_extend2 l2 l3 d2 d3).
  Proof.
    rewrite /combine_extend3 combine_extend2_nil_l.
    erewrite (combine_extend2_map_l (fun b => (d1, b)))=> //.
  Qed.

  Lemma combine_extend3_nil2 {A B C}
    (l1 : list A) (l3 : list C) (d1 : A) (d2 : B) (d3 : C) :
    combine_extend3 l1 [] l3 d1 d2 d3 =
    map (fun '(a, c) => (a, d2, c)) (combine_extend2 l1 l3 d1 d3).
  Proof.
    rewrite /combine_extend3 combine_extend2_nil_r.
    erewrite (combine_extend2_map_l (fun a => (a, d2)))=> //.
  Qed.

  Lemma combine_extend3_nil3 {A B C}
    (l1 : list A) (l2 : list B) (d1 : A) (d2 : B) (d3 : C) :
    combine_extend3 l1 l2 [] d1 d2 d3 =
    map (fun '(a, b) => (a, b, d3)) (combine_extend2 l1 l2 d1 d2).
  Proof.
    rewrite /combine_extend3 combine_extend2_nil_r.
    apply: map_ext. move=> [a b] //.
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

Lemma repeat_0 {A} (x : A) : repeat x 0 = []. Proof. done. Qed.

Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> fst_pair in * ) "fst_pair" old.
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> snd_pair in * ) "snd_pair" old.
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> repeat_0 in * ) "repeat_0" old.

Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(progress cbn [andb orb]) "cbn_andb_orb" old.

(* cbn reduces andb/orb only when the FIRST operand is a literal. These cover
   the right-operand cases, which need a rewrite (case split), not reduction. *)
(* DEBUG: bool rewrite stir rules were removed once before — `andFb` caused a
   "2 goals focused" crash during stir/cook. Not re-added here; if that error
   resurfaces, one of the four below (rewrite ... in * with no hit, or a
   leftover evar in a hyp) is the suspect — bisect by stir-step name. *)
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> andbF in * ) "andbF" old.
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> andbT in * ) "andbT" old.
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> orbF in * ) "orbF" old.
Ltac2 Set this_cookbook_ as old := add_stirstep 1 ltac1:(rewrite -> orbT in * ) "orbT" old.

Ltac2 Set this_cookbook_ as old := add_stirstep 0 ltac1:(done) "done" old.

Ltac2 Set this_cookbook_ as old := add_cookstep 1 ltac1:(progress subst) "subst" old.

Ltac2 this_cookbook () := this_cookbook_ ().

(* TODO: multimatch vs lazymatch in trickbag *)
Hint Extern 10 => multimatch goal with H : _ = _ |- _ => rewrite H end : trickbag. (* TODO: This should go somewhere good *)
Hint Extern 10 => multimatch goal with H : _ = _ |- _ => rewrite -H end : trickbag. (* TODO: This should go somewhere good *)
