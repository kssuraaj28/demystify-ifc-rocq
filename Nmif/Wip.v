From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util.
Import Tacs Util.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Parameter T : Type.
Parameter t1 t2 t3 : T.
Axiom a1 : t1 = t2.
Axiom a2 : t1 = t3.

(* TODO: Eventually, we should have a pattern that let's us not have these versions for optional cmd and so on *)
Ltac wf_finisher_arms :=
    (idtac "1"; apply: a1 + idtac "2"; apply: a2).

Ltac wf_finisher_close := 
  lazymatch goal with
  |- ?G => 
    tryif has_evar G then 
      first [eassumption | symmetry; eassumption] else
      first [assumption | reflexivity] (* Never do reflexivity when G has evars *)
  end; enter (throw). (* Should never come here. TODO: Message *)

(* TODO: We don't need n I think *)
Ltac wf_finisher_rec n :=
  lazymatch n with
  | 0 => throw (* We really don't want to recurse so much*)
  | S ?m =>
    first [
      wf_finisher_close |
      lazymatch goal with |- _ = _ => idtac | |- _ => fail end; 
        (idtac + symmetry);
        wf_finisher_arms; 
        wf_finisher_rec m]
  end.

Ltac wf_finisher :=
  harden 0 (wf_finisher_rec 5).

(* Snapshot a constr: substitute resolved evars into a standalone term that
   doesn't reference the evar map. eval_cbn with empty flags walks the term
   and rebuilds it through the current evar map but performs no reduction. *)
Ltac2 clone_constr (c : constr) : constr :=
  let no_red : Std.red_flags := {
    Std.rStrength := Std.Norm;
    Std.rBeta := false; Std.rMatch := false; Std.rFix := false;
    Std.rCofix := false; Std.rZeta := false; Std.rDelta := false;
    Std.rConst := []
  } in
  Std.eval_cbn no_red c.

Section clone_constr_test.
  (* No reduction: 1 + 1 stays as 1 + 1. *)
  Goal True.
  Proof.
    ltac2:(
      let c := clone_constr constr:(1 + 1) in
      if Constr.equal c constr:(1 + 1) then () else
      Control.throw (Tactic_failure (Some (Message.of_string "clone_constr reduced 1 + 1")))
    ).
    ltac2:(
      let c := clone_constr constr:(1 + 1) in
      if Constr.equal c constr:(2) then
      Control.throw (Tactic_failure (Some (Message.of_string "clone_constr reduced to 2"))) else ()
    ).
    (* Resolved evar gets substituted. *)
    ltac2:(
      let v := open_constr:(_) in
      ltac1:(v |- unify v (5 + 5)) (Ltac1.of_constr v);
      let c := clone_constr v in
      if Constr.equal c constr:(5 + 5) then () else
      Control.throw (Tactic_failure (Some (Message.of_string "clone_constr did not substitute evar")))
    ).
    exact I.
  Qed.
End clone_constr_test.

Ltac2 wf_finisher_guess0 (p : Ltac1.t) : unit :=
  let acc : constr list ref := { contents := [] } in
  match Control.case (fun () =>
    let v := open_constr:(_) in
    ltac1:(p v |- pattern_eq [p] with v) p (Ltac1.of_constr v);
    Control.focus 1 1 (fun () =>
      ltac1:(wf_finisher);
      acc.(contents) := clone_constr v :: acc.(contents);
      Control.zero (Tactic_failure None)
    )
  ) with
  | Val _ => panic_s  "temp" "Not possible"
  | Err _ => List.iter (fun c => Message.print (Message.concat (Message.of_string "saw v = ") (Message.of_constr c))) (acc.(contents))
  end.
  

(* TODO: Eventually, have an assert that ensures that there is a unique guess *)
Tactic Notation "wf_finisher_guess" "[" ssrpatternarg(p) "]" :=
  let f := ltac2:(p |- wf_finisher_guess0 p) in
  f p.


Goal 5 = 5. wf_finisher.  Abort.  (* TODO!!!  assert_fails also succeeds!!  WHAT *)

Section test.
  Parameter P : T -> Prop.
  Goal P t1.
  Proof.
    wf_finisher_guess [t1]. Undo.
    wf_finisher_guess [t1]. Undo.
  Abort.
End test.
