From Ltac2 Require Import Ltac2 Printf. (* TODO: Hygiene *)
Require Import ssreflect.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.


Ltac2 panic_m (fn_name: string) (m: message) := 
  Control.throw (Tactic_failure (Some (fprintf "%s: %m" fn_name m))).
Ltac2 softfail_m (fn_name: string) (m: message) :=
  Control.zero (Tactic_failure (Some (fprintf "%s: %m" fn_name m))).

Ltac2 panic_s (fn_name: string) (s: string) := panic_m fn_name (Message.of_string s).
Ltac2 softfail_s (fn_name: string) (s: string) := softfail_m fn_name (Message.of_string s).

Ltac2 one_goal_assertion (fn_name: string) :=
  if (Int.equal (Control.numgoals()) 1) then () else
  panic_s fn_name "Needs to run with one goal".
 

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


(* Run `t`. If it succeeds, then check goals. TODO: Reconsider Control.enter. Maybe better to pull that out? *)
(* TODO: Is Ltac1.run tt the same as ltac1:(x |- x) tt ?*)
#[local] Ltac2 goals_check (t : unit -> unit) (n: int) (is_le: bool) (is_hard: bool) : unit :=
  one_goal_assertion "goals_check";
  t ();
  let m := Control.numgoals () in
  let tst := if is_le then (Int.le m n) else (Int.equal m n) in
  if tst then () else
  let e_str := if is_le 
                  then fprintf "got %i goal(s), not less than %i" m n
                  else fprintf "got %i goal(s), not equal to %i" m n in
  if is_hard 
    then panic_m "goals_check" e_str 
    else softfail_m "goals_check" e_str.


Ltac2 Notation "ensure_goals" n(tactic(0)) t(thunk(self)) :=
  goals_check t n false false.

(* 
   tactic0 has tightest precedence is required so the tactic argument doesn't
   greedily consume the trailing integer. TODO: Check
*)
Tactic Notation "ensure_goals" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    ensure_goals (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

Ltac2 Notation "ensure_goals" "<=" n(tactic(0)) t(thunk(self)) :=
  goals_check t n true false.

Tactic Notation "ensure_goals" "<=" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    ensure_goals <= (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

(* For a hard throw, use the harden tactic *)

(* TODO: ensure_goals tests *)
Section test.
  Goal True.
  Proof.
    Succeed ensure_goals 0 easy. 
    Fail ensure_goals 1 easy. 
    Succeed try (ensure_goals 1 easy). 
    Succeed ensure_goals <=1 easy.
    Succeed (ensure_goals 102 fail) || idtac. (* The tactic can fail itself *)
    Succeed (ensure_goals 102 idtac) || idtac. (* The tactic can fail itself *)
  Abort.

  (* TODO: Clean these tests.. *)
  Variable P : Prop.
  Goal P /\ P.  Proof. ensure_goals 2 split. Abort.
  Goal P /\ P.  Proof. ensure_goals 3 split || idtac. Abort.
  Goal P /\ P.  Proof. first [ idtac "Trying 3"; ensure_goals 3 split | idtac "Trying 2"; ensure_goals 2 split ]. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. Fail all: ensure_goals 2 split. Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. all: enter (ensure_goals 2 split). Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split. Fail all: (ensure_goals 2 (enter split)). Abort.
  Goal (P /\ P) /\ (P /\ P).  Proof.  split; enter (ensure_goals 2 split). Abort.
End test.


(* The harden tactic *)
#[local] Ltac2 assert_no_evars () : unit :=
  one_goal_assertion "assert_no_evars";
  if Constr.has_evar (Control.goal ()) then 
      panic_s "assert_no_evars" "Goal has evar" else
  let hyp_has_evar (_, body, ty) :=
    let body_evar := match body with Some b => Constr.has_evar b | _ => false end in
    Bool.or body_evar (Constr.has_evar ty) in
  List.iter (fun (name, body, ty) =>
    let body_evar := match body with Some b => Constr.has_evar b | _ => false end  in
    if body_evar then
      panic_m "assert_no_evars" (fprintf "Hyp %I body has evar" name) else
    let type_evar := Constr.has_evar ty in
    if type_evar then
      panic_m "assert_no_evars" (fprintf "Hyp %I has evar" name) else
    ()) (Control.hyps()).

Section test.
  Goal exists n, n = 2.
  Proof Mode "Ltac2". (assert_no_evars ()). eexists. Fail (assert_no_evars ()).  Abort.
  Goal True.  Proof. evar (T : Prop). Fail ltac2:(assert_no_evars ()).  Abort.
End test.

#[local] Ltac2 Type exn ::= 
  [ProgressWrap (exn)].

#[local] Ltac2 once_hard_progress (t: unit -> unit) : unit :=
  one_goal_assertion "once_hard_progress";
  let t := fun () => match Control.case t with | Err e => Control.zero (ProgressWrap e) | _ => () end in
  let t := fun () => Control.progress t in
  match Control.case t with
  | Err (ProgressWrap e) => Control.zero e
  | Err e => printf "Error: harden progress failure"; Control.throw e
  | _ => ()
  end.

Section test.
  Goal False.
  Proof Mode "Ltac2". 
    Fail once_hard_progress (fun () => ()).
    once_hard_progress (fun () => ltac1:(pose n := 4)).
  Abort.
End test.

#[local] Ltac2 assert_no_hyp_loss (t:unit -> unit) : unit :=
  one_goal_assertion "assert_no_hyp_loss";
  let names () := List.map (fun (n, _, _) => n) (Control.hyps ()) in
  let before := names () in t ();
  Control.enter (fun () => (* You will get a not focused exception *)
    let after := names () in
    if List.for_all (fun n => List.mem Ident.equal n after) before then () else
    panic_s "assert_no_hyp_loss" "Hypothesis removed or renamed").

Section test. 
  Goal True -> False.
  Proof Mode "Ltac2".
    assert_no_hyp_loss (fun ()=> ltac1:(idtac)).
    (* New: adding hypotheses is allowed. *)
    Succeed assert_no_hyp_loss (fun ()=> ltac1:(intros)).
    intros h.
    assert_no_hyp_loss (fun ()=> ltac1:(intros)).
    Fail assert_no_hyp_loss (fun ()=> ltac1:(rename h into h')).
  Abort.

  Goal True -> False /\ False. 
  Proof Mode "Ltac2".
    intros h.
    Succeed assert_no_hyp_loss (fun ()=> ltac1:(split)).
    Fail assert_no_hyp_loss (fun ()=> ltac1:(split; rename h into h')).
    Fail assert_no_hyp_loss (fun ()=> ltac1:(split; [rename h into h'|])).
  Abort.
 
End test. 


(* harden should be the one tactic-writer facing tactic. 
  Hardened tactics must be called with one focused goal
  Hardened tactics don't backtrack.
  Hardened tactics unshelve.
  Hardened tactics can fail. If they don't, 
  - they must progress
  - They should not shelve anything
  - You can assert the number of goals produced
  - You can assert whether evars are involved
  - You can assert the hypothesis names remain unchanged
  If an assertion fails, we panic. 
  Convenient syntax: harden n, harden <= n, harden ? (for Ltac2 and Ltac1)
  Use `precise_harden` when not sufficient.
*)
(* TODO: This type could be made into a record  *)
Ltac2 precise_harden (t: unit -> unit) (goals: (int * bool) option) (allow_evar_change: bool) (allow_hyps_remove : bool): unit :=
    one_goal_assertion "precise_harden";
    let t := fun () => once_hard_progress t in  (* TODO: What is the correct order? *)
    let t := fun () => Control.unshelve t in  
    let t := match goals with
             | Some (n, b) (* is_le*) =>  fun () => goals_check t n b true 
             | None => t 
             end in
    let t := if allow_evar_change then t else fun () => t(); Control.enter assert_no_evars in
    let t := if allow_hyps_remove then t else fun () => assert_no_hyp_loss t in
    t ().

(* Sugar: The default values of these bools are false *)
#[local] Ltac2 harden0 t goals :=  precise_harden t goals false false.

Ltac2 Notation "harden" n(tactic(0)) t(thunk(self)) := harden0 t (Some (n,false)).

Tactic Notation "harden" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    harden (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

Ltac2 Notation "harden" "<=" n(tactic(0)) t(thunk(self)) :=  harden0 t (Some (n,true)).

Tactic Notation "harden" "<=" integer(n) tactic0(t):=
  let f := ltac2:(tt nn |-
    harden <= (Option.get (Ltac1.to_int nn)) (Ltac1.run tt)) in
  f t n.

Ltac2 Notation "harden" "?" t(thunk(self)) :=  harden0 t None.

Tactic Notation "harden" "?" tactic0(t):=
  let f := ltac2:(tt |-
    harden ? (Ltac1.run tt)) in
  f t.


Section test.
  Goal True.
  Proof.
    Succeed harden ? easy.
    Succeed harden 0 easy.
    Succeed try (harden 100 fail).
    Succeed try (harden 1 fail).
    Fail harden 1 idtac.
    Fail try (harden 1 idtac).
  Abort.

  Variable P : Prop.
  Goal P /\ P.  
  Proof. 
    Succeed harden 2 split. 
    Succeed harden ? intuition. 
  Abort.
End test.

(*  
    If t is a tactic that takes in a hypothesis, 
    this tactic will apply the top hypothesis on it
    The top hypothesis might go away. I'm not doing any hardening. 
    Maybe worth doing a goals_check? TODO
*)
Tactic Notation "toph" tactic(t) := (let f := fresh in (move=> f); t f). 

(* This is a little hacky because you don't you are doing trial and error.. 
   Maybe better to specialize *)
Tactic Notation "someh" tactic(t) := match goal with H : _ |- _ => t H end.

Section test.
  Ltac t H := apply H.
  Goal False -> False.  Proof.  toph t. Abort.
  Goal False -> False.  Proof.  move=> *. someh t . Abort.
End test.

Ltac evar_spec h :=  
  let t := unshelve (move: h; let t := open_constr:(_) in let f := fresh in pose f := t=> /(_ f); subst f) in
  let f := ltac2:(tt |- precise_harden 
                (fun () => Ltac1.run(tt)) 
                (Some (2,false))
                true
                true) in(* You're moving h away *)
  f t. 


Section test.
  Variable P : nat -> Prop.
  Variable Q : Prop.
  Goal (P 5 -> Q) -> (forall n, P n) -> Q.
  Proof.
    Succeed move=> x i; (evar_spec i); cycle 1; exact x.
    Succeed move=> x; (toph evar_spec); cycle 1; exact x.
    move=> x. unshelve toph evar_spec. 2: exact x. (* Applying to second goal solves the first goal. *)
  Qed.
End test.


Ltac2 revert_hyp_type (dependent: bool) (ty : constr) :=
  let t := fun () =>
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
    | [] => panic_m "revert_hyp_type" (fprintf "No hypothesis of type %t" ty)
    | _ => panic_m "revert_hyp_type" (fprintf "Multiple hypotheses of type %t" ty)
    end in
 precise_harden t (Some (1, false)) false true.

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

(* TODO: Maybe worth generalizing the CBNEQ thing.. *)
Ltac2 Notation "cbn_eq" t(thunk(constr)) :=
  let t := t () in
  let t' := eval cbn in $t in
  exact ($t = $t').

(* Does the #[refine] attibute make this obsolete? *)
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


(* section_vars *)
  (* TODO: You could do some preprocessing. Check if id's are really in hypotheses *)
#[local] Ltac2 rec exfalso_move_some_hack (ids : ident list) : ident * bool :=
  exfalso;
  match ids with
  | [] => panic_s "move_some" "nothing movable"
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
      | _ =>  panic_s "section_vars" "move_some failed unexpectedly"
      end in
    let result := loop remaining [] in
    Control.zero (SectionVarsResult result))
  with
  | Err (SectionVarsResult l) => l
  | _ => panic_s "section_vars" "unexpected control flow"
  end.

Section test.
  Variables A B : Prop.
  Goal False.
  Proof.
    ltac2:(let svs := section_vars () in
      if Int.equal (List.length svs) 2 then ()
      else panic_m "section_vars" (fprintf "expected 2 section vars, got %i" (List.length svs))).
  Abort.

  Variables C : Prop.

  Goal False.
  Proof.
    ltac2:(let svs := section_vars () in
      if Int.equal (List.length svs) 3 then ()
      else panic_m "section_vars" (fprintf "expected 2 section vars, got %i" (List.length svs))).
  Abort.
End test.

(* goal_hygiene *)
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
    panic_s "cleanup_id" "empty identifier" else
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

  (* t, dest, allow_hyps_remove *)
  #[abstract] Ltac2 Type cook_tac := ((unit -> unit) * (string) * bool).
  #[abstract] Ltac2 Type cookbook := cook_tac list.

  Ltac2 create_new_cookbook () : cookbook := [].
  Ltac2 mutable curr_cookbook () : cookbook := [].
  Ltac2 curr_stirbook () : cookbook := 
    List.filter (fun (_, _, allow_hyps_remove) => Bool.neg allow_hyps_remove) (curr_cookbook ()).
  Ltac2 mutable cook_debug : bool := false.

  #[local] Ltac2 print_cookbook0 (l : cookbook) : unit :=
    List.iteri (fun i p =>
      let (_, desc, dhc) := p in
      printf "%i: %s [allow_hyps_remove=%s]" i desc (if dhc then "true" else "false")) (l).

  Ltac2 Notation "print_cookbook" l(tactic(0)) :=  print_cookbook0 (l ()).

  #[local] Ltac2 keep_only0 (l : cookbook) (names : string list) : cookbook :=
    let mem s := List.exist (String.equal s) names in
    List.filter (fun (_,desc,_) => mem desc) l.

  Ltac2 Notation "keep_only" l(tactic(0)) names(thunk(tactic(0))) :=
    fun () => keep_only0 (l ()) (names ()).

  #[local] Ltac2 delete0 (l : cookbook) (names : string list) : cookbook :=
    let mem s := List.exist (String.equal s) names in
    List.filter (fun (_,desc,_)=> Bool.neg (mem desc)) l.

  Ltac2 Notation "delete" l(tactic(0)) names(thunk(tactic(0))) :=
    fun () => delete0 (l ()) (names ()).

  (* TODO: Maybe check that there is no name duplication in the future? Throw a warning if this is the case *)
  #[local] Ltac2 append_tac0 (t: unit -> unit) (desc: string) (goals: (int * bool) option) (allow_hyps_remove: bool) (l : cookbook) : cookbook :=
    let hardened := fun () => precise_harden t goals false allow_hyps_remove in 
    (hardened, desc, allow_hyps_remove) :: l.

  (* TODO: This desc() is sus *)
  Ltac2 Notation "add_cookstep" n(tactic(0)) t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) (Some (n,false)) true (l ()).

  Ltac2 Notation "add_cookstep" "<=" n(tactic(0)) t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) (Some (n,true)) true (l ()).

  Ltac2 Notation "add_cookstep" "?" t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) None true (l ()).

  Ltac2 Notation "add_stirstep" n(tactic(0)) t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) (Some (n,false)) false (l ()).

  Ltac2 Notation "add_stirstep" "<=" n(tactic(0)) t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) (Some (n,true)) false (l ()).

  Ltac2 Notation "add_stirstep" "?" t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) None false (l ()).

  (* TODO: PROOF_STYLE.md is going to be very different *)
  #[local] Ltac2 join_cookbooks0 (l1: cookbook)(l2 : cookbook) : cookbook := List.append l1 l2.

  Ltac2 Notation "join_cookbooks" l1(tactic(0)) l2(tactic(0)) := fun () => join_cookbooks0 (l1 ()) (l2 ()).

  #[local] Ltac2 cook_step (only_stir : bool) : unit :=
    one_goal_assertion "cook_stir_step";
    let book := if only_stir then curr_stirbook () else  curr_cookbook () in
    let rec go i l :=
      match l with
      | [] => softfail_s "cook_stir_step" "all tactics failed"
      | (t, desc, _) :: rest =>
       if Bool.neg cook_debug then () else printf "Trying: cook_stir_step[%i]: %s" i desc;
        match Control.case t with
        (* It is the client's responsibility to put harden. If the client does not put it, then the thing will spin forever! *)
        | Val ((),_) => if Bool.neg cook_debug then () else printf "cook_stir_step[%i]: %s success" i desc
        | Err _ => go (Int.add i 1) rest
        end
      end in
    go 0 book.

  Tactic Notation "cook_step" := ltac2:(cook_step false); goal_hygiene.
  Tactic Notation "stir_step" := ltac2:(cook_step true).

  (* 
    - Singleton hintdatabase with cook_step. 
    Clients are not allowed to touch this database
  *)
  Create HintDb __cook_step. (* TODO: Does #[local] help *)
  Hint Extern 100  => ltac2:(cook_step false) : __cook_step. 

  Ltac2 mutable cook_auto_dbs () : ident list := [].
  Ltac2 mutable cook_auto_depth : int := 5.

  #[local] Ltac2 cook_auto () : unit :=
    let dbs := List.append (cook_auto_dbs ()) [@__cook_step] in
    let dbg := if cook_debug then Std.Debug else Std.Off in
    Std.auto dbg (Some cook_auto_depth) [] (Some dbs).

  Tactic Notation "cook_auto" := ltac2:(cook_auto ()). 

  (* For every focued goal, it runs cook_step one by one. (dfs strategy)  *)
  #[local] Ltac2 cook (only_stir: bool) (gas : int option) : unit :=
    let rec go (gas : int option) : unit :=
      (* Gas check *)
      if match gas with Some n => Int.equal n 0 | None => false end then () else

      let gls := Control.numgoals () in
      if cook_debug then printf "cook: numgoals = %i" gls else ();
      (* Goals check: TODO: What happens if we throw or assert? *)
      if Int.equal gls 0 then () else

      (* Run the first goal *)
      (Control.focus 1 1 (fun () =>
        match Control.case (fun () => cook_step only_stir) with
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
  
  Tactic Notation "cook" := ltac2:(cook false None); goal_hygiene.
  Tactic Notation "stir" := ltac2:(cook true None). 
  Tactic Notation "cook" integer(n) :=
    let f := ltac2:(nn |- cook false (Some (Option.get (Ltac1.to_int nn)))) in
    f n; goal_hygiene.
  Tactic Notation "stir" integer(n) :=
    let f := ltac2:(nn |- cook true (Some (Option.get (Ltac1.to_int nn)))) in
    f n.

  (* TODO: You need to have a lot of tests here.. TODO: Maybe claude can help *)

End Cook.

Section usage.
  Import Cook.
  Ltac2 mutable db := create_new_cookbook.
  Ltac2 Set db as old := add_cookstep 1 ltac1:(progress idtac) "desc" old.
  Ltac2 Set db as old := join_cookbooks old old.
  Ltac2 Eval print_cookbook db.
End usage.  Fail Ltac2 Check db.


Section test.
  Import Cook.

  Section progfail.
    Ltac2 this_cookbook_ :=
      add_stirstep 1 ltac1:(idtac) "dummy" create_new_cookbook.
    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()). (* Maybe keep only 1 *)
    Goal False. Proof. Fail cook.  Abort.
  End progfail.
  
  (* bad stir *)
  Section bad_stir.
    Ltac2 this_cookbook_ :=
      add_stirstep 1 ltac1:(lazymatch goal with H: True |- _ => clear H end ) "dummy" create_new_cookbook.
    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()). (* Maybe keep only 1 *)
    Goal True -> False. Proof. Fail cook.  Abort.
  End bad_stir.
  
  (* stir vs cook *)
  Section stir_vs_cook.
    Ltac2 this_cookbook_ :=
      add_cookstep 1 ltac1:(pose n := 5) "pose" create_new_cookbook.
    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()). (* Maybe keep only 1 *)
    Goal False. Proof. progress cook. Fail progress stir. Abort.
  End stir_vs_cook.
End test.
