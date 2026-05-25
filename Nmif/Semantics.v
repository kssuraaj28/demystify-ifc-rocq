From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

Fail Ltac2 Check Attacker.this_cookbook_.
#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section exp.
  Context `{!VarPrm, !ValPrm}.
  Definition eval_val_exp (st: Store) (e: ValExp) : Vals :=
    let: (v1, v2, comp) := e in 
    let: vl1 := st v1 in
    let: vl2 := st v2 in
    comp vl1 vl2.

  Definition eval_bool_exp (st: Store) (e: BoolExp) : bool :=
    let: (v, comp) := e in 
    let: vl := st v in
    comp vl.
End exp.

Section cleanstep.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Notation Continuation := Syntax.Prog.

  Definition clean_cmd_stp_store (c: Cmd) (s: Store) : Store :=
    match c with
    | assign dst exp => 
      let: vl := eval_val_exp s exp in update_to_store s dst vl
    | _ =>  s
    end.
  
  (* TODO: Have examples below this *)
  Definition optcmd_stp_store := oapp clean_cmd_stp_store id.


  Definition clean_cmd_stp_cnt (c: Cmd) (s: Store) : Continuation :=
    match c with
    | cond exp b1 b2 => 
      let: tst := eval_bool_exp s exp in 
      if tst is true then b1 else b2
    | while exp b =>
      let: tst := eval_bool_exp s exp in 
      if tst is true then (b ++ [c]) else []
    | _ =>  []
    end.

  (* TODO: Have examples below this *)
  Definition optcmd_stp_cnt := oapp clean_cmd_stp_cnt (fun _ => []).

  (* The option is epsilon  *)
  Definition CmdEvent := option (Vars * Vals).

  Definition clean_cmd_evnt (c: Cmd) (s: Store) : CmdEvent :=
    match c with
    | assign dst exp => 
      let: vl := eval_val_exp s exp in
      if (is_trusted dst) is false then None else
      Some (dst, vl) 
    | _ => None
    end.

  (* TODO: Have examples below this *)
  Definition optcmd_evnt := oapp clean_cmd_evnt (fun _ => None).

  Fact optcmd_stp_store_simpl c s: ltac2:(cbn_eq (optcmd_stp_store (Some c) s)). Proof. done. Qed.
  Fact optcmd_stp_cnt_simpl c s: ltac2:(cbn_eq (optcmd_stp_cnt (Some c) s)). Proof. done. Qed.

  Lemma clean_cmd_stp_cnt_idem c s :
    clean_cmd_stp_cnt c (clean_cmd_stp_store c s) = clean_cmd_stp_cnt c s.
  Proof. case: c => //=. Qed.

  Fact optcmd_stp_cnd_idem c s : (* TODO: This should be rewrite step *)
    optcmd_stp_cnt c (optcmd_stp_store c s) = optcmd_stp_cnt c s.
  Proof. case: c=> //= *. exact: clean_cmd_stp_cnt_idem. Qed.
End cleanstep.

(* TODO: All autorewrite-ish tactics should do rewrite -> in * *)
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> optcmd_stp_store_simpl) "optcmd_stp_store_simpl" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> optcmd_stp_cnt_simpl) "optcmd_stp_cnt_simpl" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> optcmd_stp_cnd_idem) "optcmd_stp_cnd_idem" old.

Section test.
  Context `{!VarPrm, !ValPrm}.
  Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()). (* Maybe keep only 1 *)

  Goal forall (P: _ -> Prop) c s, P (optcmd_stp_store (Some c) s).
  Proof. move=> *. cook. Abort.
End test.

Section acmd.
  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm} {AtkStates : Type}.
  Variable (adv: AdvNextStep AtkStates).
  Record AtkCmd := mk_atkcmd {is_attacked: bool; ocmd : option Cmd}.
  Definition State := (Store * AtkStates)%type.

  Definition acmd_step (ac: AtkCmd) (s: State): Prog * State * nat :=
    let: mk_atkcmd isatk cmd := ac in
    let: (store, atk_st) := s in
    let: st := if isatk is true then pre_cmd_action adv atk_st store else store in
    let: (prog, st) := (optcmd_stp_cnt cmd st,  optcmd_stp_store cmd st) in

    let: atk_pst := (post_cmd_action adv atk_st st) in
    let: atk_st := if isatk is true then atk_pst.1 else atk_st in
    let: steps := if isatk is true then atk_pst.2 else 0 in

    (prog, (st, atk_st), steps).

  Fact acmd_step_atk cmd store atk_st :
    acmd_step (mk_atkcmd true cmd) (store, atk_st) =
      let pre_st := pre_cmd_action adv atk_st store in
      let st'    := optcmd_stp_store cmd pre_st in
      let pst    := post_cmd_action adv atk_st st' in
      (optcmd_stp_cnt cmd pre_st, (st', pst.1), pst.2).
  Proof. done. Qed.

  Fact acmd_step_noatk cmd store atk_st :
    acmd_step (mk_atkcmd false cmd) (store, atk_st) =
      (optcmd_stp_cnt cmd store, (optcmd_stp_store cmd store, atk_st), 0).
  Proof. done. Qed.
End acmd.

Section twocfg.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable (adv1: AdvNextStep AtkStates1) (adv2: AdvNextStep AtkStates2).

  Notation State1 := (State (AtkStates:=AtkStates1)).
  Notation State2 := (State (AtkStates:=AtkStates2)).

  Definition TwoCfg := (list (AtkCmd * AtkCmd) * State1 * State2)%type.

  Definition step (c: TwoCfg): TwoCfg :=
    let: (c2lst, s1, s2) := c in
    if c2lst isn't (ac1, ac2) :: rest then c else
    let: (p1, st1, steps1) := (acmd_step adv1 ac1 s1) in
    let: (p2, st2, steps2) := (acmd_step adv2 ac2 s2) in

    let: cont := combine_extend4
                   (map Some p1) (repeat true steps1)
                   (map Some p2) (repeat true steps2)
                   None false None false in
    let: cont := map (fun '(oc1, a1, oc2, a2) => (mk_atkcmd a1 oc1, mk_atkcmd a2 oc2)) cont in
    (cont ++ rest, st1, st2).
End twocfg.


(*
Section cont.
  Import Util.List. (* When to import? TODO *)
  Context `{!VarPrm, !ValPrm}.
  
  (* 
    When executing, steps are like  
    (enabled?) attack - (enabled?) prog 
  *)
  Record AtkCmd :=
    mk_cstep {is_attacked: bool; get_cmd : option Cmd}.

  Definition pure_atk := (mk_cstep true None).
  Definition pure_cmd c := (mk_cstep false (Some c)).

  Definition Continuation := list AtkCmd.



  (*  *)
  Fixpoint prog_zip (p: Prog) (atk_steps: nat) : Continuation :=
    match p, atk_steps with
    | cmd :: p', S atk_steps' =>
          (mk_cstep true (Some cmd)) :: (prog_zip p' atk_steps')

    | [], _ => 
        repeat pure_atk atk_steps

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

  Context  {AtkStates : Type} (atksm: AdvNextStep AtkStates).
    init_substeps: AtkStates -> nat; (* We allow atkstates because this can depend on the public store. You could force adv to run  cou *)


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
            (substeps atksm atkst, leaker atksm atkst)
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

  Definition initial_cfg (p: Prog) (atksm : AdvNextStep AtkStates) (s: Store) : Cfg AtkStates :=
    let: atkst := init_state atksm ⟨s | is_public⟩ in
    let: init_cont := prog_zip p (init_substeps atksm atkst) in
    (init_cont, s, atkst, []).
End init_cfg.

Section cfg_step.
  Import VarValStore.Notations. 
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Context {AtkStates : Type} (atksm : AdvNextStep AtkStates). (* TODO: unify *)

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

  Context {AtkStates : Type} (atksm : AdvNextStep AtkStates).

  (* Simulating coinduction... *)
  Definition prog_behavior {AtkStates} (p : Prog) (atksm : AdvNextStep AtkStates) : Behavior :=
                          fun init_store gas =>
                            let: init_cfg := initial_cfg p atksm init_store in
                            extract_trace (multistep atksm gas init_cfg).

End program_sem.

Module Notations.
  Notation "⟦ p ☠︎︎ a ⟧" := (prog_behavior p a).
End Notations.
*)

Ltac2 this_cookbook () := this_cookbook_ ().
