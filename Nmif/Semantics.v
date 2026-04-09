From Stdlib Require List ssreflect.
Import List ListNotations ssreflect.

Require Tacs Util VarValStore Attacker Syntax. 
Import Tacs Util VarValStore Attacker Syntax. 
(* TODO: Order seems to matter. Syntax before fails *)

Section cleanstep.
  Context `{!VarPrm, !ValPrm}.

  Notation Continuation := Syntax.Prog.

  Definition clean_cmd_step (c: Cmd) (s: Store) : (Store * Continuation) := 
    match c with
    | assign comp => ( comp s, [])
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

  Lemma clean_assign_nocont: forall comp s s' c,
    clean_cmd_step (assign comp) s = (s', c) ->
    c = [].
  Proof.
    move=> > /= [] //.
  Qed.

End cleanstep.

Section cont.
  Import Util.List. (* When to import? TODO *)
  Context `{!VarPrm, !ValPrm}.
  
  (* 
    When executing, steps are like  
    (enabled?) attack - (enabled?) prog 
  *)
  Record AtkCmd :=
    mk_cstep {is_attacked: bool; cmd : option Cmd}.

  Definition pure_atk := (mk_cstep true None).
  Definition pure_cmd c := (mk_cstep false (Some c)).

  Definition Continuation := list AtkCmd.

  (*  *)
  Fixpoint prog_zip (p: Prog) (atk_steps: nat) : Continuation :=
    match p, atk_steps with
    | cmd :: p', S atk_steps' =>
          (mk_cstep true (Some cmd)) :: (prog_zip p' atk_steps')

    | [], _ => 
        nlist pure_atk atk_steps

    | _ , 0 =>  
        map pure_cmd p
    end.

  Lemma prog_zip_noprg: forall n, prog_zip [] n = nlist pure_atk n. Proof.
    move=> //.
  Qed.

  Lemma prog_zip_noatk: forall p, prog_zip p 0 = map pure_cmd p. Proof.
    Fail move=> //; fail.
    case=>//.
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

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Context  {AtkStates : Type} (atksm: AdvStateMachine AtkStates).

  Definition optcmd_step c s :=
        if c isn't (Some c) then (s, []) else
        clean_cmd_step c s.

  (* I think that eventually, you'd want to put the observations here also.. *)
  Definition atk_cmd_step 
      (c : AtkCmd) (s : Store) (atkst : AtkStates) : 
      (Store * AtkStates * Continuation * option LeakVals) := 

        let: mk_cstep is_atk c := c in 

        (* Part1 of adversary runs *)
        let: s := if is_atk is false then s else
          corruptor atksm atkst s
        in

        (* Run your computation *)
        let: (s, pcont) := optcmd_step c s in

        (* Part2a of adversary runs. *)
        let: atkst := if is_atk is false then atkst else learner atksm atkst s  in

        (* Part2b of adversary runs. *)
        let: (substeps, optleak) :=
          if is_atk is false then
            (0, None)
          else
            (substeps atksm atkst, Some (leaker atksm atkst))
        in

        (s, atkst, prog_zip pcont substeps, optleak).

End atk_cmd_step.

Section cfg.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Context (AtkStates : Type).

  (* Only trusted store view *)
  Definition Observation := (StoreView * option LeakVals)%type.

  Definition ObservationTrace := list Observation.

  (* It is useful to put everything in Cfg for bisimulation proofs *)
  Definition Cfg := (Continuation * Store * AtkStates * ObservationTrace)%type.
End cfg.

Section init_cfg.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Context {AtkStates : Type}.

  Definition initial_cfg (p: Prog) (atksm : AdvStateMachine AtkStates) (s: Store) : Cfg AtkStates :=
    let: atkst := init_state atksm ⟨s | is_public⟩ in
    let: init_cont := prog_zip p (init_substeps atksm atkst) in
    (init_cont, s, atkst, []).
End init_cfg.

Section cfg_step.
  Import VarValStore.Notations. 
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Context {AtkStates : Type} (atksm : AdvStateMachine AtkStates). (* TODO: unify *)

  Notation Cfg := (Cfg AtkStates).

  Definition step (c : Cfg) : Cfg :=
    let: (cont, store, atkst, trace) := c in

    let: (cont', store', atkst', optlk) := 
      if cont isn't (atk_cmd :: cont') then (cont, store, atkst, None) else (* TODO: How to handle termination correctly *)
      let: (store', atkst', extra_cont, optlk) := atk_cmd_step atksm atk_cmd store atkst in 
      (extra_cont ++ cont', store', atkst', optlk)
    in 

    (cont', store', atkst', ( ⟨ store' | is_trusted ⟩, optlk) :: trace).

  (* Man, testing this might be painful.. *)
  Fixpoint multistep (gas: nat) (c : Cfg) : Cfg :=
    match gas with
    | 0 => c
    | S gas => step (multistep gas c) 
    end.

  Definition extract_trace (c : Cfg) : ObservationTrace :=
    let: (_,_,_,cfg) := c in
    cfg.
End cfg_step.

Section program_sem.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Definition Behavior := Store -> nat -> ObservationTrace.

  Context {AtkStates : Type} (atksm : AdvStateMachine AtkStates).

  (* Simulating coinduction... *)
  Definition prog_behavior {AtkStates} (p : Prog) (atksm : AdvStateMachine AtkStates) : Behavior :=
                          fun init_store gas =>
                            let: init_cfg := initial_cfg p atksm init_store in
                            extract_trace (multistep atksm gas init_cfg).

End program_sem.

Module Notations.
  Notation "⟦ p ☠︎︎ a ⟧" := (prog_behavior p a).
End Notations.
