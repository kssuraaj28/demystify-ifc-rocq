From Stdlib Require List ssreflect.
Import List ListNotations ssreflect.

Require VarValStore Syntax Attacker Tacs Util.
Import VarValStore Syntax Attacker.

Section cleanstep.
  Context `{!VarPrm, !ValPrm}.

  Notation Continuation := Prog.

  Definition clean_cmd_step (c: Cmd) (s: Store) : (Store * Continuation) := 
    match c with
    | skip => (s, [])
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

End cleanstep.

Section cont.
  Import Util.List. (* When to import? TODO *)
  Context `{!VarPrm, !ValPrm}.

  Inductive AtkCmd :=
    mk_cstep (is_attacked: bool) (cmd : Cmd).

  Definition Continuation := list AtkCmd.

  Notation pure_atk := (mk_cstep true skip) (only parsing).
  Notation pure_cmd := (mk_cstep false) (only parsing).

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
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvSMPrm}.

  Definition Cfg := (Continuation * Store * AtkStates)%type.
End cfg.

Section init_cfg.
  Import VarValStore.Notations. Check ⟨ _ ⟩.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvSMPrm}.

  Variables (p : Prog) (s : Store).

  Definition initial_cfg : Cfg :=
    let: atkst := init_state ⟨s⟩ in
    let: init_cont := prog_zip p (init_substeps atkst) in
    (init_cont, s, atkst).
End init_cfg.

Section obs.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Definition Observation := (StoreView is_trusted * option LeakVals)%type.

  Definition ObservationTrace := list Observation.
End obs.


Section cfg_step.
  Import VarValStore.Notations. Check ⟨ _ ⟩.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvSMPrm}.
  (* Maybe it is worth separating AdvSMPrm.. We only care about the states type*)

  Definition step (c : Cfg) : Cfg * Observation :=
    let: (cont, store, atkst) := c in
    let: (cont', store', atkst', optlk) := 
      if cont isn't (atk_cmd :: cont') then (cont, store, atkst, None) else (* TODO: How to handle termination correctly *)
      let: (store', atkst', extra_cont, optlk) := atk_cmd_step atk_cmd store atkst in 
      (extra_cont ++ cont', store', atkst', optlk)
    in 
    (cont', store', atkst', ( ⟨ store' ⟩, optlk)).

  (* Man, testing this might be painful.. *)
  Fixpoint multistep (gas: nat) (c : Cfg) : Cfg * ObservationTrace :=
    match gas with
    | 0 => 
        (c, [])

    | S gas => 
        let: (c', tr) := multistep gas c in
        let: (c'', obs) := step c' in
        (c'', obs :: tr)
    end.

  Ltac done ::= eauto; fail.

  Goal forall g c, 
      length (snd (multistep g c)) = g.
  Proof.
    elim=> //= ?+c=> /(_ c).
    by case: multistep step=> ??[??] /= ->.
  Qed.

  Goal forall g c, exists o,
      o :: (snd (multistep g c)) = 
      (snd (multistep (S g) c)).
  Proof.
    case=> > /=; first by case: step=> //=.
    move: multistep {-3}step=> [??] [??] /=.
    by case: step => /=.
  Qed.
  

End cfg_step.


Section program_sem.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Context (p: Prog) `(!AdvSMPrm).

  (* Simulating coinduction... *)
  Definition Behavior := Store -> nat -> ObservationTrace.

  Definition prog_behavior : Behavior :=
    fun init_store gas =>
      let: init_cfg := initial_cfg p init_store in
      let: (_, ret) := multistep gas init_cfg in
      ret.

End program_sem.

Module Notations.
  Notation "⟦ p ☠︎︎ a ⟧" := (prog_behavior p a).
End Notations.
