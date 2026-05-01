From Ltac2 Require Import Ltac2 Printf. (* TODO: Hygiene *)
Require Import ssreflect.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.


(* TODO: This file structure is ugly *)

(* TODO: Notation for this *)
Ltac2 goals l :=
  let name_goal x := ltac1:(x |- refine ?[x]) (Ltac1.of_ident x) in
  Control.dispatch (List.map (fun x () => name_goal x) l).

Section fail.
  (* If it does not tac arguments, then this works fine! *)
  #[local] Tactic Notation "goals" ne_ident_list(l) :=
    let f := ltac2:(ll |-
      printf "numgoals = %i" (Control.numgoals ());
      goals (List.map (fun x => Option.get (Ltac1.to_ident x))
                      (Option.get (Ltac1.to_list ll)))) in
    f l.

  #[local] Tactic Notation "goals_hc" :=
    let f := ltac2:(
      printf "numgoals = %i" (Control.numgoals ());
      goals [@x; @y]) in
    f.

  Variable P : Prop.
  Goal P /\ P.
  Proof.
    Fail (split; goals a b).
    Fail (split; goals a).
    split; goals_hc.
  Abort.
End fail.


Tactic Notation "NAME_GOALS_AFTER" tactic0(t) ne_ident_list(l) :=
  let f := ltac2:(tt ll |-
    Ltac1.run tt;
    goals (List.map (fun x => Option.get (Ltac1.to_ident x))
                    (Option.get (Ltac1.to_list ll)))) in
  f t l.

Section test.
  Variable P : Prop.
  Goal P /\ P.
  Proof. NAME_GOALS_AFTER split a b. Abort.
End test.



(*  
    If t is a tactic that takes in a hypothesis, 
    this tactic will apply the top hypothesis on it
    The top hypothesis might go away
*)
Tactic Notation "toph" tactic(t) := let f := fresh in (move=> f); t f. (* Tactic Notation vs Ltac Notation *)

(* This is a little hacky because you don't you are doing trial and error.. 
   Maybe better to specialize *)
Tactic Notation "someh" tactic(t) :=
    match goal with
    H : _ |- _ => t H
    end.

Section test.
  Ltac t H := idtac H.
  Goal False -> False.  Proof.  toph t. Abort.
  Goal False -> False.  Proof.  move=> *. someh t . Abort.
End test.

(* TODO: Why does wrapping this with assert_goals true 1 not work? *)
Ltac2 bt_guard () : unit :=
  Control.plus (fun () => ())
       (fun e =>
         Message.print (Message.of_exn e); (* TODO: Put this in the exception *)
         Control.throw (Tactic_failure (Some (fprintf "bt_guard: caught backtracking")))).

Tactic Notation "bt_guard" := ltac2:(bt_guard ()).
Section test.
  Variable P Q : Prop.

  Goal True. Proof. bt_guard. exact I. Abort.
  Goal True. Proof. Fail (bt_guard; fail) || idtac. Abort.
  Goal True. Proof. (idtac "a" + idtac "b"); bt_guard; exact I. Abort.
  Goal True. Proof. Fail ((idtac "a" + idtac "b"); bt_guard; fail). Abort.
End test.

(* 
  assert_goals:  run `t`, if it succeeds, then check that exactly n goals remain. 
  Use `bt_guard` to stop backtracking. 
  In general, it seems impossible to have a tactic that can seletively
  halt soft backtracking in goals
*)
(* TODO: Is Ltac1.run tt the same as ltac1:(x |- x) tt ?*)
Ltac2 assert_goals (hard : bool) (t : unit -> unit) (n: int) : unit :=
  Control.enter (fun () =>
    t ();
    let m := Control.numgoals () in
    if Int.equal m n then () else
    let e := Tactic_failure (Some (fprintf "assert_goals: expected %i goal(s), got %i" n m)) in
    if hard then Control.throw e else Control.zero e).

(* Ltac1 wrappers. Use parens for compound tactics: `assert_goals_hard (a; b) 3`.
   tactic0 has tightest precedence is required so the tactic argument doesn't
   greedily consume the trailing integer. TODO: Check
*)
Tactic Notation "assert_goals_hard" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |- assert_goals true (fun () => Ltac1.run tt) (Option.get (Ltac1.to_int nn))) in
  f t n.

Tactic Notation "assert_goals_soft" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    assert_goals false (fun () => Ltac1.run tt) (Option.get (Ltac1.to_int nn))) in
  f t n.


Section test.
  Goal True.
  Proof.
    Succeed assert_goals_hard 0 easy.
    Fail assert_goals_hard 1 easy. 
    Fail assert_goals_soft 1 easy. 
    Succeed (assert_goals_hard 2 fail) || idtac. 
    Fail (bt_guard; assert_goals_hard 2 fail) || idtac. 
    Succeed bt_guard; (assert_goals_hard 2 fail) || idtac. 
    Fail (bt_guard; assert_goals_hard 10 fail) || idtac. 
  Abort.

  Variable P : Prop.
  Goal P /\ P.  Proof. assert_goals_hard 2 split. Abort.
  Goal P /\ P.  Proof. Fail assert_goals_hard 3 split. Abort.
  Goal P /\ P.  Proof. first [ idtac "Trying 3"; assert_goals_soft 3 split | idtac "Trying 2"; assert_goals_soft 2 split  ]. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. all: assert_goals_hard 2 split. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split; assert_goals_hard 2 split. Abort.
End test.



Ltac evar_spec H :=  assert_goals_hard 1
                       (move: H; let t := open_constr:(_) in let f := fresh in  pose f := t=> /(_ f); subst f).

Section test.
  Variable P : nat -> Prop.
  Variable Q : Prop.
  Goal (P 5 -> Q) -> (forall n, P n) -> Q.  
  Proof. 
    Succeed move=> x; (toph evar_spec); exact x.
    move=> x. unshelve toph evar_spec. 2: exact x. (* Applying to second goal solves the first goal. *)
  Qed.
End test.

Ltac2 revert_hyp_type (dependent: bool) (ty : constr) :=
  let hyps := List.filter (fun h => let (_, _, t) := h in Constr.equal t ty) (Control.hyps ()) in
  match hyps with
  (* If others depend on it, we fail*)
  | [(h, _, _)] => 
    let revert_t := if dependent 
                      then ltac1:(x |- generalize dependent x)  (* TODO: It seems like it would be good to assert the number of goals *)
                      else ltac1:(x |- revert x)  in
    let hcnstr := Control.hyp h in revert_t (Ltac1.of_constr hcnstr)
  (* Unless you absolutely require zero, don't use zero *)
  | [] => Control.throw (Tactic_failure (Some (fprintf "No hypothesis of type %t" ty))) 
  | _ => Control.throw (Tactic_failure (Some (fprintf "Multiple hypotheses of type %t" ty)))
  end.

Tactic Notation "revert_hyp_type" constr(ty) :=
  let f := ltac2:(ty |- revert_hyp_type false (Option.get (Ltac1.to_constr ty))) in
  f ty.

Tactic Notation "revert_hyp_type_dep" constr(ty) :=
  let f := ltac2:(ty |- revert_hyp_type true (Option.get (Ltac1.to_constr ty))) in
  f ty.

Section test.
  Goal nat -> False. Proof. move=> *.  revert_hyp_type nat. Abort.
  Goal nat -> nat -> False. Proof. move=> *.  Fail revert_hyp_type nat. Abort.
  Variable P : nat -> Prop.
  Goal forall n, P n -> False. Proof. move=> *. revert_hyp_type_dep nat. Abort.
End test.

(* Using Constr.Unsafe.kind: the App node exposes the full n-ary application
   (head + all args) in one step. With `match!` and `?f _` we'd have to recurse,
   since that pattern peels off one argument at a time. TODO: verify *)
Ltac2 head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h _ => h
  | _ => t
  end.

(* The is_constructor check below is delegated to Ltac1; it could equivalently
   be written in Ltac2 by inspecting Constr.Unsafe.kind for a Constructor node. *)
Ltac2 cnstrct_eq_gl () :=
  lazy_match! goal with
  | [ |- ?a = ?b ] =>
    let hl := head a in
    let hr := head b in
    if Constr.equal hl hr then
      ltac1:(f |- is_constructor f; congr f) (Ltac1.of_constr hl)
    else Control.zero (Tactic_failure (Some (fprintf "heads differ: %t vs %t" hl hr)))
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "goal is not an equality")))
  end.

Ltac cnstrct_eq_gl := ltac2:(cnstrct_eq_gl ()).

Section test.
  Goal forall n m, S n = S m.
  Proof. move=> *. cnstrct_eq_gl. Abort.

  Goal forall (n1 n2 m1 m2: nat), (n1, n2) = (m1, m2).
  Proof. move=> *. cnstrct_eq_gl. Abort.
End test.

Module GallinaHole.
  (* Holes *)
  #[local] Ltac2 admit_tac () := 
    let hole_constr := Control.hyp @hole in
    Control.refine (fun () => '($hole_constr _)).

    (* TODO: I wish that this was exact. 
    I also wish that I could check the type of hole,
    and make sure that it is forall T, T

    Maybe then have marked hole, etc.
    You could have a way to look for marked holes, etc.

    You could also attach arbitrary ltac2 things.
    Maybe the right place for this is to know the types of certain things..
    Can we get gallina notations for this?
    Notation x _ := x.
    *)
  Notation "??" := ltac2:(admit_tac ()) (only parsing).

  Section usage. 
    Fail Check ?? + 5.
    Hypothesis hole : forall T, T.
    Check ??.
    Let x := ?? + ??. Print x.
    Let y := 5 + ??. Print x.
    Check ?? + 5.

    Compute  (match ?? with 
      | true => ??
      | false => ??
      end).

  End usage.

  Section test. Variable hole : bool.   Fail Check ??.  End test.
End GallinaHole.
