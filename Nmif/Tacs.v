From Ltac2 Require Import Ltac2 Printf. (* TODO: Hygiene *)
Require Import ssreflect ssrmatching.

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

(* ssrpatternarg lets you parse X in X... However, you need to delimit with [ ]
  With uconstr, you don't need to, but you can't use X in .
  TODO: cpattern *)
Tactic Notation "pattern_eq_2" "[" ssrpatternarg(p1) "]" "[" ssrpatternarg(p2) "]" :=
  let a := fresh "_e1" in
  let b := fresh "_e2" in
  ssrpattern p1; move=> a;
  ssrpattern p2; move=> b;
  have: a = b; subst a b.

(* uconstr means you can use [] *)
Tactic Notation "pattern_eq" "[" ssrpatternarg(p1) "]" "with" uconstr(c) :=
  let a := fresh "_e1" in
  ssrpattern p1; move=> a;
  have: a = c; subst a.

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

#[local] Ltac2 assert_no_hyp_change (t:unit -> unit) : unit :=
  one_goal_assertion "assert_no_hyp_change";
  let hyp_eq (n1, b1, t1) (n2, b2, t2) :=
    Bool.and (Ident.equal n1 n2)
    (Bool.and
      (match b1, b2 with
       | None, None => true
       | Some c1, Some c2 => Constr.equal c1 c2
       | _, _ => false
       end)
      (Constr.equal t1 t2)) in
  let before := Control.hyps () in t ();
  Control.enter (fun () =>
    let after := Control.hyps () in
    if Int.equal (List.length before) (List.length after) then
      (if List.for_all2 hyp_eq before after then ()
       else panic_s "assert_no_hyp_change" "Hypothesis changed")
    else panic_s "assert_no_hyp_change" "Hypothesis added or removed").

Section test. 
  Goal True -> False.
  Proof Mode "Ltac2".
    assert_no_hyp_change (fun ()=> ltac1:(idtac)).
    Fail assert_no_hyp_change (fun ()=> ltac1:(intros)).
    intros h.
    assert_no_hyp_change (fun ()=> ltac1:(intros)).
    Fail assert_no_hyp_change (fun ()=> ltac1:(rename h into h')).
    Fail assert_no_hyp_change (fun ()=> ltac1:(pose proof I)).
    ltac1:(pose proof (p := I)).
    assert_no_hyp_change (fun ()=> ltac1:(move: p=> p)).
    Fail assert_no_hyp_change (fun ()=> ltac1:(move: h=> h)). (* The order of hyps matters too! *)
  Abort.

  Goal True -> False /\ False. 
  Proof Mode "Ltac2".
    intros h.
    Succeed assert_no_hyp_change (fun ()=> ltac1:(split)).
    Fail assert_no_hyp_change (fun ()=> ltac1:(split; rename h into h')).
    Fail assert_no_hyp_change (fun ()=> ltac1:(split; [rename h into h'|])).
  Abort.
 
End test. 


(* harden should be the one tactic-writer facing tactic. 
  Hardened tactics: 
  - must be called with one focused goal
  - can't backtrack.
  - unshelve.
  - can fail. 
  If a hardened tactic succeeds,
  - they must progress
  - They should not shelve anything  !!
  - You can assert the number of goals produced
  - You can assert the hypothesis names remain unchanged
  If an assertion fails, we panic. 
  Convenient syntax: harden n, harden <= n, harden ? (for Ltac2 and Ltac1)
  Use `precise_harden` when not sufficient.
*)
(* TODO: This type could be made into a record  *)
Ltac2 precise_harden (t: unit -> unit) (goals: (int * bool) option) (allow_hyps_change : bool): unit :=
    one_goal_assertion "precise_harden";
    let t := fun () => once_hard_progress t in  (* TODO: What is the correct order? *)
    let t := fun () => Control.unshelve t in  
    let t := match goals with | Some (n, b) (* is_le*) =>  fun () => goals_check t n b true | None => t end in
    let t := if allow_hyps_change then t else fun () => assert_no_hyp_change t in
    t ().

(* Sugar: The default values of these bools are false *)
#[local] Ltac2 harden0 t goals :=  precise_harden t goals false.

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


Ltac evar_spec_toph :=  
  let t := unshelve ( let t := open_constr:(_) in let f := fresh in pose f := t=> /(_ f); subst f) in
  let f := ltac2:(tt |- precise_harden 
                (fun () => Ltac1.run(tt)) 
                (Some (2,false))  true) in(* You're moving h away *)
  f t. 


Section test.
  Variable P : nat -> Prop.
  Variable Q : Prop.
  Goal (P 5 -> Q) -> (forall n, P n) -> Q.
  Proof.
    Succeed move=> x; (evar_spec_toph) ; cycle 1; exact x.
    move=> x. unshelve evar_spec_toph. 2: exact x. (* Applying to second goal solves the first goal. *)
  Qed.
End test.

(* Revert hyp *)
#[local] Ltac2 Type exn ::= [ RevertHypProbe ].

Ltac2 revert_hyp_single_pat (pt : preterm) : unit :=
  let elaborate_thunk () :=
    Constr.Pretype.pretype
      Constr.Pretype.Flags.open_constr_flags_no_tc
      Constr.Pretype.expected_without_type_constraint
      pt in
  let matches hty :=
    match Control.case (fun () =>
        let ty := elaborate_thunk () in
        Std.unify hty ty;
        Control.zero RevertHypProbe) with
    | Err RevertHypProbe => true
    | Err _ => false
    | _ => panic_s "revert_hyp_single_pat" "Unexpected control flow"
    end in
  let hyps := List.filter (fun (_, _, hty) => matches hty) (Control.hyps ()) in
  let revert_tac h :=
    match Control.case (fun () => ltac1:(x |- revert x) (Ltac1.of_constr h)) with
    | Val _ => ()
    | Err e => Control.throw e
    end in
  match hyps with
  | [(h, _, _)] => revert_tac (Control.hyp h)
  | [] => panic_s "revert_hyp_single_pat" "No matching hypothesis"
  | _ => panic_s "revert_hyp_single_pat" "Multiple matching hypotheses"
  end.

Ltac2 revert_hyp_pat (pts : preterm list) : unit :=
  List.iter revert_hyp_single_pat (List.rev pts).

Tactic Notation "revert_hyp_pat" "[" ne_uconstr_list_sep(pats, ",") "]" :=
  let f := ltac2:(pats |-
    revert_hyp_pat
      (List.map (fun u => Option.get (Ltac1.to_preterm u))
                (Option.get (Ltac1.to_list pats)))) in
  f pats.

Tactic Notation "revert_hyp_pat" uconstr(ty) :=
  let f := ltac2:(ty |- revert_hyp_pat [Option.get (Ltac1.to_preterm ty)]) in
  f ty.

Section test.
  Goal nat -> False. Proof. move=> *.  revert_hyp_pat nat. Abort.
  Goal nat -> nat -> False. Proof. move=> *.  Fail revert_hyp_pat nat. Abort.
  Variable P : nat -> Prop.
  Goal forall n, P n -> False. 
  Proof. 
    Succeed move=> *; revert_hyp_pat [nat, (P _)]. 
    Fail move=> *; revert_hyp_pat [ (P _), nat]. 
  Abort.

  Goal nat -> False. Proof. move=> n. revert_hyp_pat (_ -> Prop). Abort.
  Goal 1 = 2 -> True. Proof. move=> h. revert_hyp_pat (_ = _). Abort.
  Goal option nat -> True.  Proof. move=> a. revert_hyp_pat (option _). Abort.
  Goal option nat -> option bool -> True.  Proof. move=> a b. Fail revert_hyp_pat (option _). Abort.
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


Module Cook.

  (* t, desc *)
  #[abstract] Ltac2 Type cook_tac := ((unit -> unit) * (string)).
  #[abstract] Ltac2 Type cookbook := cook_tac list.

  Ltac2 create_new_cookbook () : cookbook := [].
  Ltac2 mutable curr_cookbook () : cookbook := [].
  (* 0 = silent, 1 = info (print successes + auto info),
     2 = full (also print attempts, numgoals, FW/BW failures, auto debug) *)
  Ltac2 mutable cook_debug : int := 0.

  (* Print [msg ()] when cook_debug is at least [lvl]. *)
  #[local] Ltac2 cook_dbg (lvl : int) (msg : unit -> unit) : unit :=
    if Int.ge cook_debug lvl then msg () else ().

  #[local] Ltac2 print_cookbook0 (l : cookbook) : unit :=
    List.iteri (fun i p =>
      let (_, desc) := p in
      printf "%i: %s" i desc) (l).

  Ltac2 Notation "print_cookbook" l(tactic(0)) :=  print_cookbook0 (l ()).

  #[local] Ltac2 check_all_present (fn_name : string) (l : cookbook) (names : string list) : unit :=
    let descs := List.map (fun (_, desc) => desc) l in
    let in_book s := List.exist (String.equal s) descs in
    List.iter (fun n =>
      if in_book n then () else panic_m fn_name (fprintf "name not in cookbook: %s" n))
      names.

  #[local] Ltac2 keep_only0 (l : cookbook) (names : string list) : cookbook :=
    check_all_present "keep_only" l names;
    let mem s := List.exist (String.equal s) names in
    List.filter (fun (_,desc) => mem desc) l.

  Ltac2 Notation "keep_only" l(tactic(0)) names(thunk(tactic(0))) :=
    fun () => keep_only0 (l ()) (names ()).

  #[local] Ltac2 delete0 (l : cookbook) (names : string list) : cookbook :=
    check_all_present "delete" l names;
    let mem s := List.exist (String.equal s) names in
    List.filter (fun (_,desc)=> Bool.neg (mem desc)) l.

  Ltac2 Notation "delete" l(tactic(0)) names(thunk(tactic(0))) :=
    fun () => delete0 (l ()) (names ()).


  (* TODO: Maybe check that there is no name duplication in the future? Throw a warning if this is the case *)
  #[local] Ltac2 append_tac0 (t: unit -> unit) (desc: string) (l : cookbook) : cookbook :=
    let hardened := fun () => precise_harden t (Some (1, true)) false in
    (hardened, desc) :: l.

  (* TODO: This desc() is sus *)
  Ltac2 Notation "add_cookstep" t(thunk(tactic(0))) desc(thunk(tactic(0))) l(tactic(0)) :=
    fun () => append_tac0 t (desc ()) (l ()).

  (* TODO: PROOF_STYLE.md is going to be very different *)
  #[local] Ltac2 join_cookbooks0 (l1: cookbook)(l2 : cookbook) : cookbook := List.append l1 l2.

  Ltac2 Notation "join_cookbooks" l1(tactic(0)) l2(tactic(0)) := fun () => join_cookbooks0 (l1 ()) (l2 ()).

  #[local] Ltac2 cook_step () : unit :=
    one_goal_assertion "cook_step";
    let rec go i l :=
      match l with
      | [] => softfail_s "cook_step" "all tactics failed"
      | (t, desc) :: rest =>
        cook_dbg 2 (fun () => printf "Trying: cook_step[%i]: %s" i desc);
        match Control.case t with
        | Val ((),_) => cook_dbg 1 (fun () => printf "cook_step[%i]: %s success" i desc)
        | Err e =>
            cook_dbg 2 (fun () => printf "cook_step[%i]: %s failed: %a" i desc (fun () e' => Message.of_exn e') e);
            go (Int.add i 1) rest
        end
      end in
    go 0 (curr_cookbook ()).

  Tactic Notation "cook_step" := ltac2:(cook_step ()).

  (* 
    - Singleton hintdatabase with cook_step. 
    Clients are not allowed to touch this database
  *)
  Create HintDb cook_step. (* TODO: Does #[local] help *)
  Hint Extern 100  => cook_step: cook_step.

  (* For every focued goal, it runs cook_step one by one. (dfs strategy)  *)
  #[local] Ltac2 cook (gas : int option) : unit :=
    let rec go (gas : int option) : unit :=
      (* Gas check *)
      if match gas with Some n => Int.equal n 0 | None => false end then () else

      let gls := Control.numgoals () in
      cook_dbg 1 (fun () => printf "cook: numgoals = %i" gls);
      (* Goals check: TODO: What happens if we throw or assert? *)
      if Int.equal gls 0 then () else

      (* Run the first goal *)
      (Control.focus 1 1 (fun () =>
        match Control.case (fun () => cook_step ()) with
        | Val ((), _) => ()
        | Err _ =>
              cook_dbg 2 (fun () => printf "cook: cook_step failed, shelving goal");
              Control.shelve ()
        end);
       let next_gas := match gas with | Some n => Some (Int.sub n 1) | None => None end in
       go next_gas) in
    unshelve (go gas).

  Tactic Notation "cook" := ltac2:(cook None).
  Tactic Notation "cook" integer(n) :=
    let f := ltac2:(nn |- cook (Some (Option.get (Ltac1.to_int nn)))) in
    f n.

  (* TODO: You need to have a lot of tests here.. TODO: Maybe claude can help *)

End Cook.

Section usage.
  Import Cook.
  Ltac2 mutable db := create_new_cookbook.
  Ltac2 Set db as old := add_cookstep ltac1:(progress idtac) "desc" old.
  Ltac2 Set db as old := join_cookbooks old old.
  Ltac2 Eval print_cookbook db.
End usage.  Fail Ltac2 Check db.


Section test.
  Import Cook.

  Section progfail.
    Ltac2 this_cookbook_ :=
      add_cookstep ltac1:(idtac) "dummy" create_new_cookbook.
    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()). (* Maybe keep only 1 *)
    Goal False. Proof. Fail cook.  Abort.
  End progfail.

  (* clears hyp *)
  Section bad_cook.
    Ltac2 this_cookbook_ :=
      add_cookstep ltac1:(lazymatch goal with H: True |- _ => clear H end ) "dummy" create_new_cookbook.
    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()). (* Maybe keep only 1 *)
    Goal True -> False. Proof. move=> *. Fail cook.  Abort.
  End bad_cook.
End test.
