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

(* 
  - run `t`. 
  - if it succeeds, then check that exactly n goals remain. 
  - is_hard either throws or zeroes. You can't just first[once_assert_goals* t ?? | throw] because
    you'd want to control whether you throw for this assert or not..
  In general, it seems impossible to have a tactic that can seletively
  halt soft backtracking in goals
*)
(* TODO: Is Ltac1.run tt the same as ltac1:(x |- x) tt ?*)
Ltac2 goals_chck (t : unit -> unit) (n: int) (is_le: bool) (is_hard: bool) : unit :=
  Control.enter (fun () =>
    t ();
    let m := Control.numgoals () in
    let tst := if is_le then (Int.le m n) else (Int.equal m n) in
    if tst then () else
    let e_str := if is_le 
                    then fprintf "assert_goals: got %i goal(s), not less than %i" m n
                    else fprintf "assert_goals: got %i goal(s), not equal to %i" m n in
    let err := if is_hard then Control.throw else Control.zero in 
    err (Tactic_failure (Some e_str))).


(* Ltac1 wrappers. Use parens for compound tactics: `assert_goals_hard (a; b) 3`.
   tactic0 has tightest precedence is required so the tactic argument doesn't
   greedily consume the trailing integer. TODO: Check
*)
(* For now, we only use the hard assert in our automation engine. Use the soft assert in tactics *)
Tactic Notation "once_ensure_goals" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    goals_chck (fun () => Ltac1.run tt) (Option.get (Ltac1.to_int nn)) false false) in
  f t n.

Tactic Notation "once_ensure_goals" "<=" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    goals_chck (fun () => Ltac1.run tt) (Option.get (Ltac1.to_int nn)) true false) in
  f t n.

Section test.
  Goal True.
  Proof.
    Succeed once_ensure_goals 0 easy.
    Fail once_ensure_goals 1 easy. 
    try (once_ensure_goals 1 easy). 
    Fail try (first [once_ensure_goals 1 easy | fail_hard]). 
    Succeed once_ensure_goals <=1 easy.
    Succeed (once_ensure_goals 102 fail) || idtac. (* The tactic can fail itself *) 
  Abort.

  Variable P : Prop.
  Goal P /\ P.  Proof. once_ensure_goals 2 split. Abort.
  Goal P /\ P.  Proof. Fail once_ensure_goals 3 split. Abort.
  Goal P /\ P.  Proof. first [ idtac "Trying 3"; once_ensure_goals 3 split | idtac "Trying 2"; once_ensure_goals 2 split ]. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. all: once_ensure_goals 2 split. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split; once_ensure_goals 2 split. Abort.
End test.

Ltac2 Type hardened_step := 
  { tac : unit -> unit; goals : int; is_lt : bool }.   
  (* true: remaining goals < goals; false: = goals *)

Ltac2 mk_hardened_step t g is_lt :=
  { tac := t; goals := g; is_lt := is_lt }.

(* Convert a hardened_step to/from an Ltac1.t value (so it can flow through
   Ltac1 contexts). Encoded as a 3-element Ltac1 list:
   [thunk-as-Ltac1-closure; goals as Ltac1 int; is_lt as 0/1 Ltac1 int]. *)
Ltac2 hs_to_ltac1 (hs : hardened_step) : Ltac1.t :=
  Ltac1.of_list [
    Ltac1.lambda (fun _ => hs.(tac) (); Ltac1.of_constr constr:(I));
    Ltac1.of_int (hs.(goals));
    Ltac1.of_int (if hs.(is_lt) then 1 else 0)
  ].

Ltac2 hs_from_ltac1 (l : Ltac1.t) : hardened_step :=
  match Ltac1.to_list l with
  | Some [t_l1; n_l1; is_lt_l1] =>
      let n := Option.get (Ltac1.to_int n_l1) in
      let is_lt := Int.equal (Option.get (Ltac1.to_int is_lt_l1)) 1 in
      let tac := fun () => Ltac1.apply t_l1 [Ltac1.of_constr constr:(I)] (fun _ => ()) in
      mk_hardened_step tac n is_lt
  | _ => Control.throw (Tactic_failure (Some (fprintf "hs_from_ltac1: expected 3-element list")))
  end.

Tactic Notation "mk_hardened_step" tactic0(t) integer(g) := 
  let ret := ltac2val:(tt gg |- 
    let tac := fun () => Ltac1.run tt in 
    let gls := Option.get (Ltac1.to_int gg) in
    let hs := mk_hardened_step tac gls false in
    hs_to_ltac1 hs
  ) in 
  ret t g.

Tactic Notation "mk_hardened_step" tactic0(t) "<=" int(g) := 
  let ret := ltac2val:(tt gg |- 
    let tac := fun () => Ltac1.run tt in 
    let gls := Option.get (Ltac1.to_int gg) in
    let hs := mk_hardened_step tac gls true in
    hs_to_ltac1 hs
  ) in 
  ret t g.


(* When you create a hardened_step, you really want to do: 
 - once
 - unshelve
 - assert_goals
 - TODO: progress - Ideally progress hard. The idea is that once the goal completes, we'd want to check whether there was some progress. It's okay if the goal fails though
*)
(* TODO: Control.enter? *)
Ltac2 run_hardened_step hs :=
    let m := Control.numgoals () in
    if Bool.neg (Int.equal m 1) then
        Control.throw (Tactic_failure (Some (fprintf "Should be run with 1 goal focused"))) else
    goals_chck (unshelve (once (hs.(tac)))) (hs.(goals)) (hs.(is_lt)) true.

Ltac run_hardened_step hs :=
  let f := 
    ltac2:(hsenc |- 
      let hsdec := hs_from_ltac1 hsenc in
      run_hardened_step hsdec) in
  f hs.

Ltac evar_spec_step h :=
  let t := (move: h; let t := open_constr:(_) in let f := fresh in pose f := t=> /(_ f); subst f) in
  mk_hardened_step t 1.

Section test.
  Variable P : nat -> Prop.
  Variable Q : Prop.
  Goal (P 5 -> Q) -> (forall n, P n) -> Q.  
  Proof. 
    move=> x i.
    (* TODO: Claude should debug this *)
    let t := (evar_spec_step i) in 
    run_hardened_step t.
  Qed.
End test.





(* Should I stepify this? *)
Ltac2 evar_spec_step (h : ident): hardened_step :=
  let t := 
    fun () => (ltac1:(h |- move: h; let t := open_constr:(_) in let f := fresh in pose f := t=> /(_ f); subst f) (Ltac1.of_ident h)) in
  mk_hardened_step t 1 false.

    
(* 
  Claude used Ltac1.tag_name. TODO: What does it do? 
*)
Ltac evar_spec h :=
  let f := ltac2:(h |-
    let id := match Option.get (Ltac1.to_intro_pattern h) with
              | Std.IntroNaming (Std.IntroIdentifier i) => i
              | _ => Control.throw (Tactic_failure (Some (fprintf "evar_spec: expected ident hypothesis")))
              end in
    let step := evar_spec_step id in
    run_hardened_step step) in
  f h.


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
