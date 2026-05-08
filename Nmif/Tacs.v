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

Tactic Notation "enter" tactic0(t) := 
  let f := ltac2:(tt |- Control.enter (fun () => Ltac1.run tt)) in  f t.


Ltac2 assert_no_evars () : unit :=
    if Bool.neg (Int.equal (Control.numgoals()) 1) then
        Control.throw (Tactic_failure (Some (fprintf "assert_no_evars: Needs to run with one focused goal"))) else
    if Constr.has_evar (Control.goal ()) then 
        Control.throw (Tactic_failure (Some (fprintf "assert_no_evars: Goal has evar"))) else
    let hyp_has_evar (_, body, ty) :=
      let body_evar := match body with Some b => Constr.has_evar b | _ => false end in
      Bool.or body_evar (Constr.has_evar ty) in
    List.iter (fun (name, body, ty) =>
      let body_evar := match body with Some b => Constr.has_evar b | _ => false end  in
      if body_evar then
        Control.throw (Tactic_failure (Some (fprintf "assert_no_evars: Hyp %I body has evar" name))) else
      let type_evar := Constr.has_evar ty in
      if type_evar then
        Control.throw (Tactic_failure (Some (fprintf "assert_no_evars: Hyp %I has evar" name))) else
      ()) (Control.hyps()).


Tactic Notation "assert_no_evars" := ltac2:(assert_no_evars ()).
  
Section test.
  Goal exists n, n = 2.
  Proof.
    assert_no_evars.
    eexists. Fail assert_no_evars.
  Abort.

  Goal True.
  Proof.
    evar (T : Prop).
    Fail assert_no_evars.
  Abort.
End test.



#[local] Ltac2 Type exn ::= 
  [ProgressWrap (exn)].

(* TODO: After this runs, ensure that there are no evars generated. 
   - You have to unshelve
   - Maybe also check that there are no evars which get generated

*)
#[local] Ltac2 harden0 (t: unit -> unit) : unit :=
    if Bool.neg (Int.equal (Control.numgoals()) 1) then
        Control.throw (Tactic_failure (Some (fprintf "harden: Needs to run with one focused goal"))) else
    (* once *)
    let t := fun () => match Control.case t with | Err e => Control.zero (ProgressWrap e) | _ => () end in
    (* progress *)
    let t := fun () => Control.progress t in 
    (* unshelve *)
    let t := fun () => Control.unshelve t in 
    match Control.case t with
    | Err (ProgressWrap e) => Control.zero e
    | Err e => printf "Error: harden progress failure"; Control.throw e
    | _ => Control.enter assert_no_evars 
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

(* Run `t`. If it succeeds, then check goals. TODO: Reconsider Control.enter. Maybe better to pull that out? *)
(* TODO: Is Ltac1.run tt the same as ltac1:(x |- x) tt ?*)
#[local] Ltac2 goals_check (t : unit -> unit) (n: int) (is_le: bool) (is_hard: bool) : unit :=
  if Bool.neg (Int.equal (Control.numgoals()) 1) then
      Control.throw (Tactic_failure (Some (fprintf "goals_check: Needs to run with one focused goal"))) else
  let err := if is_hard then Control.throw else Control.zero in 
  t ();
  let m := Control.numgoals () in
  let tst := if is_le then (Int.le m n) else (Int.equal m n) in
  if tst then () else
  let e_str := if is_le 
                  then fprintf "assert_goals: got %i goal(s), not less than %i" m n
                  else fprintf "assert_goals: got %i goal(s), not equal to %i" m n in
  err (Tactic_failure (Some e_str)).


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
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. Fail all: ensure_goals 2 split. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. all: enter (ensure_goals 2 split). Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. Fail all: (ensure_goals 2 (enter split)). Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split; enter (ensure_goals 2 split). Abort.

  Goal P /\ P.  Proof. assert_goals 2 split. Abort.
  Goal P /\ P.  Proof. Fail assert_goals 3 split. Abort.
  Goal P /\ P.  Proof. Fail try (assert_goals 3 split). Abort.
End test.

(*  
    If t is a tactic that takes in a hypothesis, 
    this tactic will apply the top hypothesis on it
    The top hypothesis might go away. I'm not doing any hardening. 
    Maybe worth doing a goals_check? TODO
*)
Tactic Notation "toph" tactic(t) := (let f := fresh in (move=> f); t f). (* Tactic Notation vs Ltac Notation *)

(* This is a little hacky because you don't you are doing trial and error.. 
   Maybe better to specialize *)
Tactic Notation "someh" tactic(t) :=
    match goal with
    H : _ |- _ => t H
    end.

Section test.
  Ltac t H := apply H.
  Goal False -> False.  Proof.  toph t. Abort.
  Goal False -> False.  Proof.  move=> *. someh t . Abort.
End test.

Ltac evar_spec h :=  move: h; let t := open_constr:(_) in let f := fresh in pose f := t=> /(_ f); subst f.


Section test.
  Variable P : nat -> Prop.
  Variable Q : Prop.
  Goal (P 5 -> Q) -> (forall n, P n) -> Q.
  Proof.
    Succeed move=> x i; (evar_spec i); exact x.
    Succeed move=> x; (toph evar_spec); exact x.
    move=> x. unshelve toph evar_spec. 2: exact x. (* Applying to second goal solves the first goal. *)
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

(* TODO: Maybe change this to an intropattern? *)
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

Ltac2 Notation "cbn_eq" t(thunk(constr)) :=
  let t := t () in
  let t' := eval cbn in $t in
  exact ($t = $t').

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


  (* TODO: You could do some preprocessing. Check if id's are really in hypotheses *)
#[local] Ltac2 rec exfalso_move_some_hack (ids : ident list) : ident * bool :=
  exfalso;
  match ids with
  | [] => Control.throw (Tactic_failure (Some (fprintf "move_some: nothing movable")))
  | id :: rest =>
      match Control.case (fun () =>
        ltac1:(h |- move: h) (Ltac1.of_ident id)) with
      | Val ((), _) =>
          let still_there := List.exist
            (fun h => let (i, _, _) := h in Ident.equal i id)
            (Control.hyps ()) in
          (id, still_there)
      | Err _ => exfalso_move_some_hack rest
      end
  end.

Section test.
  Variables A B : Prop.
  Let x := 5.
  Goal A -> B -> True.
  Proof.
    move=> ha hb.
    ltac2:(
      let (id, sv) := exfalso_move_some_hack [@ha; @hb] in 
      if sv then printf "secvar" else ();
      printf "id: %I" id).

    ltac2:(
      let (id, sv) := exfalso_move_some_hack [@ha; @hb] in 
      if sv then printf "secvar" else ();
      printf "id: %I" id).

    ltac2:(
      let (id, sv) := exfalso_move_some_hack [@A; @hb] in 
      if sv then printf "secvar" else ();
      printf "id: %I" id).

    Fail ltac2:(let (id, _) := move_some [@ha; @hb] in printf "id: %I" id).

    ltac2:(
      let (id, sv) := exfalso_move_some_hack [@x] in 
      if sv then printf "secvar" else ();
      printf "id: %I" id).
  Abort.

End test.

#[local] Ltac2 Type exn ::= [ SectionVarsResult (ident list) ].

Ltac2 section_vars () : ident list :=
  match Control.case (fun () =>
    let remaining := List.map (fun h => let (i, _, _) := h in i) (Control.hyps ()) in
    let rec loop (remaining : ident list) (section : ident list) : ident list :=
      if Int.equal (List.length remaining) 0 then section else
      match Control.case (fun () => exfalso_move_some_hack remaining) with
      | Val ((moved_h, is_secvar), _) =>
          let new_section := if is_secvar then (moved_h :: section) else section in
          loop (List.filter (fun i => Bool.neg (Ident.equal i moved_h)) remaining) new_section
      | _ => Control.throw (Tactic_failure (Some (fprintf "section_vars: move_some failed unexpectedly")))
      end in
    let result := loop remaining [] in
    Control.zero (SectionVarsResult result))
  with
  | Err (SectionVarsResult l) => l
  | _ => Control.throw (Tactic_failure (Some (fprintf "section_vars: unexpected control flow")))
  end.

Section test.
  Variables A B : Prop.
  Goal False.
  Proof.
    ltac2:(let svs := section_vars () in 
      if Int.equal (List.length svs) 2 then ()
      else Control.throw (Tactic_failure (Some (fprintf "expected 2 section vars, got %i" (List.length svs))))).
  Abort.

  Variables C : Prop.

  Goal False.
  Proof.
    ltac2:(let svs := section_vars () in
      if Int.equal (List.length svs) 3 then ()
      else Control.throw (Tactic_failure (Some (fprintf "expected 2 section vars, got %i" (List.length svs))))).
  Abort.
End test.

(* These two funtions are AI generated. I don't care *)
#[local] Ltac2 strip_underscores (s : string) : string :=
  let n := String.length s in
  let underscore := Char.of_int 95 in
  let rec drop_leading i :=
    if Int.equal i n then i
    else if Char.equal (String.get s i) underscore then drop_leading (Int.add i 1)
    else i in
  let rec drop_trailing j :=
    if Int.equal j 0 then 0
    else if Char.equal (String.get s (Int.sub j 1)) underscore then drop_trailing (Int.sub j 1)
    else j in
  let lo := drop_leading 0 in
  let hi := drop_trailing n in
  if Int.le hi lo then "" else String.sub s lo (Int.sub hi lo).

#[local] Ltac2 cleanup_id (id : ident) : string :=
  let s := Ident.to_string id in
  if Int.equal (String.length s) 0 then
    Control.throw (Tactic_failure (Some (fprintf "cleanup_id: empty identifier"))) else
  strip_underscores s.

#[local] Ltac2 collect_renames (hyps : ident list) : (ident * ident) list :=
  let rec go hyps used :=
    match hyps with
    | [] => []
    | id :: rest =>
        let core := cleanup_id id in
        let core_id := Option.get (Ident.of_string core) in
        let fresh_core := Fresh.fresh used core_id in
        let used' := Fresh.Free.union used (Fresh.Free.of_ids [fresh_core]) in
        let wrapped_str := String.app "_" (String.app (Ident.to_string fresh_core) "_") in
        let wrapped := Option.get (Ident.of_string wrapped_str) in
        (id, wrapped) :: go rest used'
    end in
  go hyps (Fresh.Free.of_goal ()).

#[local] Ltac2 goal_hygiene0 () : unit :=
  Control.enter (fun () =>
    let hyps := List.map (fun h => let (i, _, _) := h in i) (Control.hyps ()) in
    let sec := section_vars () in
    let hyps := List.filter (fun id => Bool.neg (List.exist (fun s => Ident.equal s id) sec)) hyps in
    let renames := collect_renames hyps in
    match Control.case (fun () => Std.rename renames) with
    | Val ((),_) => ()
    | Err e => 
      printf "Error: goal_hygiene failure";
      Control.throw e
    end).

Ltac goal_hygiene := ltac2:(goal_hygiene0 ()).

Section test.
  Variables A B C : Prop.
  Goal A -> B -> C -> A. Proof. 
  move=> *. goal_hygiene. assumption. Abort.
  Goal A -> B -> C -> A. Proof. move=> > _ha_ ha *. goal_hygiene. Abort.
  Goal A /\ B. Proof. split; goal_hygiene. Abort.

  Variables P : nat -> Prop.
  Goal forall n, P n. Proof. move=> i. goal_hygiene. Abort.
  
End test.


Module Cook.

  #[abstract] Ltac2 Type cook_tac := ((unit -> unit) * (string)).
  #[abstract] Ltac2 Type cookbook := cook_tac list.

  Ltac2 create_new_cookbook () : cookbook := [].
  Ltac2 mutable curr_cookbook () : cookbook := []. (* TODO notation that wraps () *)
  Ltac2 mutable cook_debug : bool := false.

  #[local] Ltac2 print_cookbook0 (l : cookbook) : unit :=
    List.iteri (fun i p => let (_, desc) := p in printf "%i: %s" i desc) (l).

  Ltac2 Notation "print_cookbook" l(tactic(0)) :=  print_cookbook0 (l ()).

  #[local] Ltac2 keep_only0 (l : cookbook) (idxs : int list) : cookbook :=
    let mem i := List.exist (fun n => Int.equal n i) idxs in
    List.map (fun p => let (_, x) := p in x)
      (List.filter (fun p => let (i, _) := p in mem i)
        (List.mapi (fun i x => (i, x)) l)).

  Ltac2 Notation "keep_only" l(tactic(0)) idxs(tactic(0)) := fun () => keep_only0 (l ()) idxs.

  #[local] Ltac2 delete0 (l : cookbook) (idxs : int list) : cookbook :=
    let mem i := List.exist (fun n => Int.equal n i) idxs in
    List.map (fun p => let (_, x) := p in x)
      (List.filter (fun p => let (i, _) := p in Bool.neg (mem i))
        (List.mapi (fun i x => (i, x)) l)).

  Ltac2 Notation "delete" l(tactic(0)) idxs(tactic(0)) :=  fun () => delete0 (l ()) idxs.

  (* TODO: Maybe check that there is no name duplication in the future? Throw a warning if this is the case *)
  #[local] Ltac2 append_tac0 (t: unit -> unit) (desc: string) (n: int) (is_le: bool) (l : cookbook) : cookbook :=
    let wrapped := if is_le then (fun () => assert_goals <= n t()) else 
                                 (fun () => assert_goals n t()) in
    (wrapped, desc) :: l.

  (* TODO: This desc() is sus *)
  Ltac2 Notation "append_tac" n(tactic(0)) t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) n false (l ()).

  Ltac2 Notation "append_tac" "<=" n(tactic(0)) t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) n true (l ()).

  #[local] Ltac2 join_taclist0 (l1: cookbook)(l2 : cookbook) : cookbook := List.append l1 l2.

  Ltac2 Notation "join_taclist" l1(tactic(0)) l2(tactic(0)) := fun () => join_taclist0 (l1 ()) (l2 ()).

  #[local] Ltac2 cook_step_n (i : int) : unit :=
    let gls := Control.numgoals() in
    if Bool.neg (Int.equal gls 1) then Control.throw (Tactic_failure (Some (fprintf "cook_step_n: Needs to run with one focused goal"))) else
    let l := curr_cookbook () in
    match List.nth_opt l i with
    | None => Control.throw (Tactic_failure (Some (fprintf "cook_step_n: index %i out of range (length %i)" i (List.length l))))
    | Some (t, _) => ltac1:(move => * ); t (); ltac1:(move=> * )
    end.

  Tactic Notation "cook_step" integer(n) :=
    let f := ltac2:(nn |- cook_step_n (Option.get (Ltac1.to_int nn))) in
    f n; goal_hygiene.

  #[local] Ltac2 cook_step () : unit :=
    let l := curr_cookbook () in
    let len := List.length l in
    let rec go i :=
      if Int.ge i len then Control.zero (Tactic_failure (Some (fprintf "cook_step: all tactics failed")))else
      match Control.case (fun () => cook_step_n i) with
      (* It is the client's responsibility to put harden. If the client does not put it, then the thing will spin forever! *)
      | Val ((),_) => if Bool.neg cook_debug then () else
                        let (_, desc) := List.nth l i in
                        printf "cook_step[%i]: %s success" i desc
      | Err _ => go (Int.add i 1)
      end in

    go 0.

  Tactic Notation "cook_step" := ltac2:(cook_step ()); goal_hygiene.

  (* 
    - Singleton hintdatabase with cook_step. 
    Clients are not allowed to touch this database
  *)
  Create HintDb __cook_step. (* TODO: Does #[local] help *)
  Hint Extern 100  => ltac2:(cook_step ()) : __cook_step. 

  Ltac2 mutable cook_auto_dbs () : ident list := [].
  Ltac2 mutable cook_auto_depth : int := 5.

  #[local] Ltac2 cook_auto () : unit :=
    let dbs := List.append (cook_auto_dbs ()) [@__cook_step] in
    let dbg := if cook_debug then Std.Info else Std.Off in
    Std.auto dbg (Some cook_auto_depth) [] (Some dbs).

  Tactic Notation "cook_auto" := ltac2:(cook_auto ()); goal_hygiene.

  (* For every focued goal, it runs cook_step one by one. (dfs strategy)  *)
  #[local] Ltac2 cook (gas : int option) : unit :=
    let rec go (gas : int option) : unit :=
      (* Gas check *)
      if match gas with Some n => Int.equal n 0 | None => false end then () else

      let gls := Control.numgoals () in
      if cook_debug then printf "cook: numgoals = %i" gls else ();
      (* Goals check: TODO: What happens if we throw or assert? *)
      if Int.equal gls 0 then () else

      (* Run the first goal *)
      (Control.focus 1 1 (fun () =>
        match Control.case (fun () => cook_step ()) with
        | Val ((), _) => ()
        | Err _ => 
              (if cook_debug then printf "cook: FW reasoning failed, trying BW reasoning" else ());
              cook_auto (); 
              if Int.equal (Control.numgoals () ) 0 then () else
              (if cook_debug then printf "cook: BW reasoning failed, Can't solve goal " else ());
              Control.shelve ()
        end);
       let next_gas := match gas with | Some n => Some (Int.sub n 1) | None => None end in
       go next_gas) in
    unshelve (go gas).
  
  Tactic Notation "cook" := ltac2:(cook None); goal_hygiene.
  Tactic Notation "cook" integer(n) :=
    let f := ltac2:(nn |- cook (Some (Option.get (Ltac1.to_int nn)))) in
    f n; goal_hygiene.
  

End Cook.
Section usage.
  Import Cook.
  Ltac2 mutable db := create_new_cookbook.
  Ltac2 Set db as old := append_tac 1 ltac1:(progress idtac) "desc" old.
  Ltac2 Set db as old := join_taclist old old.
End usage.  Fail Ltac2 Check db.
