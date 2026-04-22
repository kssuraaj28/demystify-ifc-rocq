From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt.
Import Tacs Util VarValStore Attacker Syntax. 
(* TODO: Order seems to matter. Syntax before fails *)

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

  (* The option is epsilon  *)
  Definition CmdEvent := option (Vars * Vals).

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

End cleanstep.

(* TODO: Maybe elsewere *)
Definition PcLbl := Lattice4pt.Label.

(* TODO: Static Analysis. *)
Section sa.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Import Lattice4pt.Notations.

  Notation WellFormedProg' WellFormedCmd pclbl prog :=
    (Forall (WellFormedCmd pclbl) prog) (only parsing).

  (* TODO: How would a parameterized thing look like, as opposed to indexed? *)
  (* WellTyped? *)
  Unset Elimination Schemes.
  Inductive WellFormedCmd : PcLbl -> Cmd -> Prop := 
  | wf_assign: 
     forall dst src1 src2 comp pclbl, 
       let: dstlbl := var_lbl dst in
       let: s1lbl := var_lbl src1 in
       let: s2lbl := var_lbl src2 in
       s1lbl ⊑ dstlbl -> s2lbl ⊑ dstlbl -> pclbl ⊑ dstlbl -> (* Using ssrbool coercion *)
       _ pclbl (assign dst (src1, src2, comp))

  | wf_cond: 
     forall gvar comp pclbl b1 b2, 
       let: gvarlbl := var_lbl gvar in
       WellFormedProg' WellFormedCmd gvarlbl b1 ->
       WellFormedProg' WellFormedCmd pclbl b1 ->
       WellFormedProg' WellFormedCmd gvarlbl b2 ->
       WellFormedProg' WellFormedCmd pclbl b2 -> (* This bad? *)
       _ pclbl (cond (gvar,comp) b1 b2)

  | wf_while: 
     forall gvar comp pclbl wbody,
       let: gvarlbl := var_lbl gvar in
       WellFormedProg' WellFormedCmd gvarlbl wbody ->
       WellFormedProg' WellFormedCmd pclbl wbody -> (* Forall_and might be useful *)
       _ pclbl (while (gvar,comp) wbody).
  Set Elimination Schemes.

  Section ind.
    Variable P : PcLbl -> Cmd -> Prop.
    (* TODO: I have no idea what I did.  Is this the right IH? *)
    (* TODO Define the induction principle.. Do we even need this? 
      I suspect that  we might be able to do this without induction also.. 
    *)
    Hypothesis hyp_assign : 
        forall dst src1 src2  comp pclbl,
          let: dstlbl := var_lbl dst in
          let: s1lbl := var_lbl src1 in
          let: s2lbl := var_lbl src2 in
          s1lbl ⊑ dstlbl -> s2lbl ⊑ dstlbl -> pclbl ⊑ dstlbl ->
          P pclbl (assign dst (src1, src2, comp)).

    Hypothesis hyp_cond : 
        forall gvar comp pclbl b1 b2,
         let: gvarlbl := var_lbl gvar in
         Forall (WellFormedCmd gvarlbl) b1 -> Forall (P gvarlbl) b1 ->
         Forall (WellFormedCmd pclbl) b1 -> Forall (P pclbl) b1 ->
         Forall (WellFormedCmd gvarlbl) b2 -> Forall (P gvarlbl) b2 ->
         Forall (WellFormedCmd pclbl) b2 -> Forall (P pclbl) b2 ->
         P pclbl (cond (gvar, comp) b1 b2).

    Hypothesis hyp_while : 
        forall gvar comp pclbl wbody,
         let: gvarlbl := var_lbl gvar in
         Forall (WellFormedCmd gvarlbl) wbody -> Forall (P gvarlbl) wbody ->
         Forall (WellFormedCmd pclbl) wbody -> Forall (P pclbl) wbody ->
         P pclbl (while (gvar, comp) wbody).

    Fixpoint WellFormedCmd_ind :
      forall p c, WellFormedCmd p c -> P p c. 
    Proof.  Abort.


  End ind.
End sa.


Fail.

Section cmb_cmd.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  (* The simulator state will not be here. I'm doing some big brain intuition*)

  #[local] Set Primitive Projections. (* TODO: All records need to have this? Maybe in prelude? *)

  Record CmbCmd : Type := mk_cmbcmd {
    real_cmd : option Cmd ;
    real_atk_bit : bool ;
    ideal_cmd : option Cmd ;
    pc_lbl : PcLbl ;
  }.

  Notation State := (
    Store *      (* real store *)
    Store *      (* ideal store *)
    Store *      (* simulator store *)
    AtkStates  (* attacker state *)
  )%type.

  Definition zip 
              (real_cont: list Cmd)
              (ideal_cont: list Cmd)
              (atk_steps: nat)
              (is_trusted: bool)
              (is_public: bool)
              : list CmbCmd :=
    let: real_cont := map Some real_cont in
    let: ideal_cont := map Some ideal_cont in
    let: atk_steps := repeat true atk_steps in
    let: comb := List.combine_extend3 real_cont ideal_cont atk_steps None None false in
    map (fun '(rc, ic, abit) => mk_cmbcmd rc abit ic is_public is_trusted) comb.

  Section cmb_step.
    Variable (adv: AdvStateMachine AtkStates). (* TODO: Not holemode *)
  
    Notation corruptor := (corruptor adv).
    Notation learner := (learner adv).
    Notation atk_substeps := (substeps adv).
  
    Definition cmbcmd_step (c: CmbCmd) (s: State) : (State * list CmbCmd) := 
      let: mk_cmbcmd real_cmd real_atk_bit ideal_cmd pc_secret pc_public := c in
      let: (real_st, ideal_st, sim_st, atk_st) := s in
  
      (* Corruption first. TODO: When there is endorsement, there will need to be an update to the ideal store as well *)
      let: real_st := if real_atk_bit is true then corruptor atk_st real_st else real_st in 
      let: sim_st := if real_atk_bit is true then corruptor atk_st sim_st else sim_st in  
  
      let: real_cnt :=  optcmd_stp_cnt real_cmd real_st in (* TODO: Does the order matter? It shouldn't. *)
      let: real_st := optcmd_stp_store real_cmd real_st in
  
      (* If pc is secret, then there will not be any change to public vars, so this is okay! 
         The simulator will not have access to real_cmd in a secret branch
      *)
      let: sim_st := if pc_secret is true then sim_st else optcmd_stp_store real_cmd sim_st in  
  
      (* Why is there no untrusted? Untrusted will show up when you have the invariant involved?? *)
  
      let: ideal_cnt :=  optcmd_stp_cnt ideal_cmd ideal_st in (* TODO: Does the order matter? *)
      (* I think that this will change if there is downgrading.. TODO *)
      let: ideal_st := optcmd_stp_store ideal_cmd ideal_st in
  
      let: atk_st := if real_atk_bit is true then learner atk_st real_st else atk_st in (* This could be sim_st as well, right? TODO: You need to think about whether the attacker is active, right? *)
      let: atk_substeps := atk_substeps atk_st in
      (* For zip, you have the following 
      pc_secret, ?? maybe you should just check for the real? Why don't you check for the ideal? 
      pc_public ??
      *)
      ((real_st, ideal_st, sim_st, atk_st), zip real_cnt ideal_cnt atk_substeps true true). (* TODO: This true true thing is hardcoded..*)
  End cmb_step.
  (* TODO: Prove invariant? and show things? 
    Need to have type system.
    First, have Cmd Invariant.
    Then, show other things 
  *)
  
End cmb_cmd.

(*  The step should consume this, and give you a new list of this. It should also *)

(* The idea now is going to be that we define step for something 
combined.
*)

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

  Context  {AtkStates : Type} (atksm: AdvStateMachine AtkStates).
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
