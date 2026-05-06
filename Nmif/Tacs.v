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



Ltac2 Type exn ::= [ ProgressWrap (exn) ].

Ltac2 harden0 (t: unit -> unit) : unit :=
    match Control.case (fun () =>
      Control.progress (fun () =>
        match Control.case t with
        | Err e => Control.zero (ProgressWrap e)
        | _ => ()
        end))
    with
    | Err (ProgressWrap e) => Control.zero e
    | Err e =>
        printf "Warning: harden progress failure";
        Control.throw e
    | _ => ()
    end.

Ltac2 Notation "harden" t(thunk(self)) := harden0 t.

Tactic Notation "harden" tactic0(t) :=
  let f := ltac2:(tt |- harden (Ltac1.run tt)) in
  f t.

Section test.
  Goal True.
  Proof.
    Succeed harden easy.
    Succeed try (harden fail).
    Fail harden idtac.
    Fail try (harden idtac).
  Abort.

  Variable P : Prop.
  Goal P /\ P.  
  Proof. 
    Succeed harden split. 
    Fail try (harden idtac).
  Abort.
End test.

(*
  Run `t`. If it succeeds, then check goals
*)
(* TODO: Is Ltac1.run tt the same as ltac1:(x |- x) tt ?*)
Ltac2 goals_check (t : unit -> unit) (n: int) (is_le: bool) (is_hard: bool) : unit :=
  let err := if is_hard then Control.throw else Control.zero in 
  Control.enter (fun () =>
    t ();
    let m := Control.numgoals () in
    let tst := if is_le then (Int.le m n) else (Int.equal m n) in
    if tst then () else
    let e_str := if is_le 
                    then fprintf "assert_goals: got %i goal(s), not less than %i" m n
                    else fprintf "assert_goals: got %i goal(s), not equal to %i" m n in
    err (Tactic_failure (Some e_str))).


Ltac2 Notation "ensure_goals" n(tactic(0)) t(thunk(self)) :=
  goals_check (fun () => harden0 t) n false false.

(* 
   Ltac1 wrappers: use parens for compound tactics, e.g. `assert_goals 3 (a; b)`.
   tactic0 has tightest precedence is required so the tactic argument doesn't
   greedily consume the trailing integer. TODO: Check
*)
Tactic Notation "ensure_goals" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    ensure_goals (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

Ltac2 Notation "ensure_goals" "<=" n(tactic(0)) t(thunk(self)) :=
  goals_check (fun () => harden0 t) n true false.

Tactic Notation "ensure_goals" "<=" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    ensure_goals <= (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

Ltac2 Notation "assert_goals" n(tactic(0)) t(thunk(self)) :=
  goals_check (fun () => harden0 t) n false true.

Tactic Notation "assert_goals" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    assert_goals (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

Ltac2 Notation "assert_goals" "<=" n(tactic(0)) t(thunk(self)) :=
  goals_check (fun () => harden0 t) n true true.

Tactic Notation "assert_goals" "<=" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    assert_goals <= (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

Section test.
  Goal True.
  Proof.
    Succeed ensure_goals 0 easy. 
    Fail ensure_goals 1 easy. 
    Succeed try (ensure_goals 1 easy).  Fail try (assert_goals 1 easy).
    Fail try (first [ensure_goals 1 easy | fail_hard]). 
    Succeed ensure_goals <=1 easy.
    Succeed (ensure_goals 102 fail) || idtac. (* The tactic can fail itself *)
  Abort.


  (* TODO: Clean these tests.. *)
  Variable P : Prop.
  Goal P /\ P.  Proof. ensure_goals 2 split. Abort.
  Goal P /\ P.  Proof. Fail ensure_goals 3 split. Abort.
  Goal P /\ P.  Proof. first [ idtac "Trying 3"; ensure_goals 3 split | idtac "Trying 2"; ensure_goals 2 split ]. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. all: ensure_goals 2 split. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split; ensure_goals 2 split. Abort.

  Goal P /\ P.  Proof. assert_goals 2 split. Abort.
  Goal P /\ P.  Proof. Fail assert_goals 3 split. Abort.
  Goal P /\ P.  Proof. Fail try (assert_goals 3 split). Abort.
End test.

(*  
    If t is a tactic that takes in a hypothesis, 
    this tactic will apply the top hypothesis on it
    The top hypothesis might go away
*)
Tactic Notation "toph" tactic(t) := harden (let f := fresh in (move=> f); t f). (* Tactic Notation vs Ltac Notation *)

(* This is a little hacky because you don't you are doing trial and error.. 
   Maybe better to specialize *)
Tactic Notation "someh" tactic(t) :=
  harden 
    match goal with
    H : _ |- _ => t H
    end.

Section test.
  Ltac t H := apply H.
  Goal False -> False.  Proof.  toph t. Abort.
  Goal False -> False.  Proof.  move=> *. someh t . Abort.
End test.

Ltac evar_spec h :=
  assert_goals 2
  (unshelve (move: h; let t := open_constr:(_) in let f := fresh in pose f := t=> /(_ f); subst f); cycle 1).


Section test.
  Variable P : nat -> Prop.
  Variable Q : Prop.
  Goal (P 5 -> Q) -> (forall n, P n) -> Q.
  Proof.
    Succeed move=> x i; (evar_spec i); [exact x|].
    Fail move=> x; (toph evar_spec); cycle 1; exact x.
    Succeed move=> x; (toph evar_spec); exact x.
    move=> x. unshelve toph evar_spec. 1: exact x. (* Applying to second goal solves the first goal. *)
  Qed.
End test.


Ltac2 revert_hyp_type (dependent: bool) (ty : constr) :=
  assert_goals 1 (
  let hyps := List.filter (fun h => let (_, _, t) := h in Constr.equal t ty) (Control.hyps ()) in
  match hyps with
  (* If others depend on it, we fail*)
  | [(h, _, _)] =>
    let revert_t := if dependent
                      then ltac1:(x |- generalize dependent x)
                      else ltac1:(x |- revert x)  in
    let hcnstr := Control.hyp h in
    revert_t (Ltac1.of_constr hcnstr)
  (* Unless you absolutely require zero, don't use zero *)
  | [] => Control.throw (Tactic_failure (Some (fprintf "No hypothesis of type %t" ty)))
  | _ => Control.throw (Tactic_failure (Some (fprintf "Multiple hypotheses of type %t" ty)))
  end).

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
  harden
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
