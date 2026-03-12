From Stdlib Require List ssreflect.
Import List ListNotations ssreflect.

From Ltac2 Require Ltac2.

Require VarValStore Syntax Attacker Tacs Util.
Import VarValStore Syntax Attacker Util.List. (* TODO: When to  import? *)

Section cleanstep.
  Context `{!VarPrm, !ValPrm}.

  Notation Continuation := Prog.

  Definition clean_cmd_step (c: Cmd) (s: Store) : (Store * Continuation) := 
    match c with
    | skip => (s, [])
    | assign comp => (comp s, [])
    | cond tst b1 b2 => 
        (s, if (tst s) is true then 
              b1
            else 
              b2)
    | while tst b =>
        (s, if (tst s) is true then 
              (b ++ [while tst b]) 
            else 
              [])
    end.

End cleanstep.

Section cont.
  Context `{!VarPrm, !ValPrm}.

  Inductive AtkCmd :=
    mk_cstep (is_attacked: bool) (cmd : Cmd).

  Definition Continuation := list AtkCmd.

  Notation pure_atk := (mk_cstep true skip).
  Notation pure_cmd := (mk_cstep false).

  Fixpoint prog_zip (p: Prog) (atk_steps: nat) : Continuation :=
    match p, atk_steps with
    | cmd :: p', S atk_steps' =>
          (mk_cstep true cmd) :: (prog_zip p' atk_steps')

    | [], _ => 
        nlist pure_atk atk_steps

    | _ , 0 =>  
        map pure_cmd p
    end.

  Lemma prog_zip_noprg: forall n, prog_zip [] n = nlist pure_atk n. Proof.
    by [].
  Qed.

  Lemma prog_zip_noatk: forall p, prog_zip p 0 = map pure_cmd p. Proof.
    Fail by [].
    by case.
  Qed.

  Section check.
    Variables c1 c2 c3 : Cmd.
    Compute prog_zip [c1 ; c2 ; c3] 5.
    Compute prog_zip [c1 ; c2 ; c3] 0.
    Compute prog_zip [c1 ; c2 ; c3] 1.
    Compute prog_zip [c1 ; c2 ; c3] 3.
  End check.
End cont.


Section atk_cmd_step.
  Import VarValStore.Notations. (* TODO: Import practice? *)

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvSMPrm}.

  Definition atk_cmd_step 
      (c : AtkCmd) (s : Store) (atkst : AtkStates) : 
      (Store * AtkStates * Continuation * option LeakVals) := 

        let: mk_cstep is_atk c := c in 

        (* Part1 of adversary runs *)
        let: s := if is_atk is false then s else
          ⟨ (corruptor atkst ⟨s⟩) → s ⟩
        in

        (* Run your computation *)
        let: (s, pcont) := clean_cmd_step c s in

        (* Part2a of adversary runs. *)
        let: atkst := if is_atk is false then atkst else learner atkst ⟨s⟩ in

        (* Part2b of adversary runs. *)
        let: (substeps, optleak) :=
          if is_atk is false then
            (0, None)
          else
            (substeps atkst, Some (leaker atkst))
        in

        (s, atkst, prog_zip pcont substeps, optleak).

End atk_cmd_step.

Section cfg.
  Import Ltac2.Ltac2 Ltac2.Printf.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvSMPrm}.

  Definition Cfg := (Continuation * Store * AtkStates)%type.

  Definition step (c : Cfg) : Cfg :=
    let: (cont, store, atkst) := c in
    if cont isn't (atk_cmd :: cont') then (cont, store, atkst) else
    let: (store', atkst', extra_cont, _) := atk_cmd_step atk_cmd store atkst in (* _ is wrong. Need to have event!! *)
    (extra_cont ++ cont', store', atkst'). 

End cfg.

(* 
  What are the different ways we can define events?
  We could

TODO: Define configuration. 
                step,
                events,
                behavior
*)
