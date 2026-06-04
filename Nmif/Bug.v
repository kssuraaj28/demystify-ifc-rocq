From Stdlib Require ssreflect ssrmatching.
Import ssreflect ssrmatching.

From Ltac2 Require Import Ltac2.

Set Default Proof Mode "Classic".


Parameter T : Type.
Parameter t1 t2 : T.
Parameter f : T -> T.

Parameter lemma:
  forall t,
    f t = t.

(* Inlined from Tacs.v *)
Tactic Notation "pattern_eq" "[" ssrpatternarg(p1) "]" "with" uconstr(c) :=
  let a := fresh "_e1" in
  ssrpattern p1; move=> a;
  have: a = c; subst a.

(* Inlined from Tacs.v *)
Ltac2 clone_constr (c : constr) : constr :=
  let no_red : Std.red_flags := {
    Std.rStrength := Std.Norm;
    Std.rBeta := false; Std.rMatch := false; Std.rFix := false;
    Std.rCofix := false; Std.rZeta := false; Std.rDelta := false;
    Std.rConst := []
  } in
  Std.eval_cbn no_red c.

Ltac2 trigger_leak (pat : Ltac1.t) (u : preterm) : unit :=
  let wf_partial_tac := ltac1:(p v |- pattern_eq [p] with v) pat in
  let captured : constr ref := { contents := constr:(True) } in
  (* Probe: pretype, pattern_eq, close goal 1 via apply, snapshot v, rollback. *)
  match Control.case (fun () =>
    let v := Constr.Pretype.pretype
               Constr.Pretype.Flags.open_constr_flags_with_tc
               Constr.Pretype.expected_without_type_constraint u in
    wf_partial_tac (Ltac1.of_constr v);
    Control.focus 1 1 (fun () =>
      ltac1:(apply lemma);
      captured.(contents) := clone_constr v;
      Control.zero (Tactic_failure None)))
  with
  | Val _ => ()
  | Err _ =>
    (* Replay with the captured constr. *)
    wf_partial_tac (Ltac1.of_constr (captured.(contents)));
    Control.focus 1 1 (fun () => ltac1:(apply lemma))
  end.

Tactic Notation "trigger" "[" ssrpatternarg(p) "]" "with" uconstr(u) :=
  let g := ltac2:(p u |- trigger_leak p (Option.get (Ltac1.to_preterm u))) in
  g p u.

Parameter test : forall {U}, U.

Lemma bug (P : T -> Prop) (myb : bool) :
  P (f (if myb then t1 else t2)).
Proof.
  trigger [f (if myb then t1 else t2)] with (if _ then _ else _).
  exact test.
Qed.
