From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

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
End cmb_cmd.

Section new_pc.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Definition compute_new_pc (old_pc : PcLbl) (cmd: Cmd): PcLbl :=
    match cmd with
    | cond (gvar,_) _ _ => var_lbl gvar ⊔ old_pc (* Can this be refactored w/ static analysis? *)
    | while (gvar,_) _ => var_lbl gvar ⊔ old_pc
    | _ => old_pc
    end.

  Definition compute_new_pc_opt (old_pc : PcLbl) (cmd: option Cmd): PcLbl :=
    if cmd isn't Some cmd then old_pc else
    compute_new_pc old_pc cmd.
End new_pc.

Section thms.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Lemma compute_new_pc_untr:
    forall p c, exists p',
      compute_new_pc (mk_lbl true p) c = (mk_lbl true p').
  Proof.
    move=> p [dst exp| [g cmp] b1 b2 | [g cmp] b]; cbn; eauto.
    1-2: case: (var_lbl g) => u pg. (* TODO: This could be a lemma *)
    1-2: exists (pg && p); case: u; done.
  Qed.

 Lemma untr_compute_new_pc p c: 
   untrusted (compute_new_pc (mk_lbl true p) c).
 Proof.
   case: c=> //=; case=> * ; rewrite untr_join //.
 Qed.

  Lemma tr_cmd_cnt:
    forall p c,
      let: lbl := mk_lbl false p in
      let: new_lbl := (compute_new_pc lbl c) in
      WellFormedCmd lbl c ->
      untrusted new_lbl = false ->
      forall st1 st2,
        ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
        clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof.
    move=> >. move e: (mk_lbl _ _)=> l; move: e=> /[swap].
    case=> //= > => [_ _| _] <- untrg *.
    1-2: set gr := (X in _ = (if X then _ else _)); set gl := (X in (if X then _ else _) = _).
    1-2: suff: gl = gr; [move=> -> //|subst gl gr]; congr (_ _).
    1-2: apply/storeview_eq; [eassumption|].
    1-2: move: untrg; rewrite Bool.orb_false_r /is_trusted/is_untrusted=> -> //.
  Qed.

  Lemma step_soundness c pc:
      WellFormedCmd pc c ->
      forall st,
        WellFormedProg (compute_new_pc pc c) (clean_cmd_stp_cnt c st).
  Proof.
    move=> + > => - []=> * //=; enter if_easy_goals.
    apply/Forall_app. split=> //.
    constructor 2=> //.
    constructor 3. apply/Forall_impl; [| eassumption]; clear=> *.
    rewrite -join_assoc join_idem=> //.
  Qed.
End thms.

Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1   ltac1:(rewrite -> untr_compute_new_pc in * ) "untr_compute_new_pc" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep 1
    ltac1:(lazymatch goal with
           |- context [compute_new_pc (mk_lbl true ?p) ?c] =>
              move: ([elaborate compute_new_pc_untr p c])=> [] ? /[dup] ? ->
           end)
    "compute_new_pc_untr" old.

Section test.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()).

  Goal forall (P: _ -> Prop) p c, P (compute_new_pc (mk_lbl true p) c).
  Proof. cook. Abort.

End test.

Section cmb_step.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.

  Definition zip (real_cont: list Cmd) (ideal_cont: list Cmd) (atk_steps: nat) (pc_lbl: PcLbl): list CmbCmd :=
    let: real_cont := map Some real_cont in
    let: ideal_cont := map Some ideal_cont in
    let: atk_steps := repeat true atk_steps in
    let: comb := List.combine_extend3 real_cont ideal_cont atk_steps None None false in
    map (fun '(rc, ic, abit) => mk_cmbcmd rc abit ic pc_lbl) comb.


  Section comb_state. 
    #[local] Set Primitive Projections. (* TODO: All records need to have this? Maybe in prelude? *)

    Record CmbState : Type := mk_cmbstate {
      real_store : Store;
      ideal_store : Store;
      sim_store : Store;
      atk_st : AtkStates
    }.

    Definition Cfg := (CmbState * list CmbCmd)%type.
  End comb_state.


  Section step.
    Variable (adv: AdvStateMachine AtkStates). 
    Notation corruptor := (corruptor adv).
    Notation learner := (learner adv).
    Notation atk_substeps := (substeps adv).

    Definition cmbcmd_step (c: CmbCmd) (s: CmbState) : Cfg :=
      let: mk_cmbcmd real_cmd real_atk_bit ideal_cmd pc_lbl := c in
      let: mk_cmbstate real_st ideal_st sim_st atk_st := s in
    
      (* Corruption first. TODO: When there is endorsement, there will need to be an update to the ideal store as well *)
      let: real_st := if real_atk_bit is true then corruptor atk_st real_st else real_st in 
      let: sim_st := if real_atk_bit is true then corruptor atk_st sim_st else sim_st in  
    
      let: real_cnt :=  optcmd_stp_cnt real_cmd real_st in (* TODO: Does the order matter? It shouldn't. *)
      let: real_st := optcmd_stp_store real_cmd real_st in
    
      (* If pc is secret, then there will not be any change to public vars, so this is okay! 
         The simulator will not have access to real_cmd in a secret branch
      *)
      let: sim_st := if (Lattice4pt.public pc_lbl) is false then sim_st else optcmd_stp_store real_cmd sim_st in   (* TODO: This Lattice4pt is stupid *)
    
      (* Why is there no untrusted? Untrusted will show up when you have the invariant involved?? *)
    
      let: ideal_cnt :=  optcmd_stp_cnt ideal_cmd ideal_st in (* TODO: Does the order matter? *)
      (* I think that this will change if there is downgrading.. TODO *)
      let: ideal_st := optcmd_stp_store ideal_cmd ideal_st in
    
      let: atk_st := if real_atk_bit is true then learner atk_st real_st else atk_st in (* This could be sim_st as well, right? TODO: You need to think about whether the attacker is active, right? *)
      let: atk_substeps := atk_substeps atk_st in

      let: new_pc := compute_new_pc_opt pc_lbl real_cmd in
      (mk_cmbstate real_st ideal_st sim_st atk_st, zip real_cnt ideal_cnt atk_substeps new_pc). 

    Definition cfg_step (cfg: Cfg) : Cfg := 
      let: (st, cmdlst) := cfg in
      if cmdlst isn't (cmd :: cmdlst') then cfg else
      let: (st', cmdlst'') := cmbcmd_step cmd st in
      (st', cmdlst'' ++ cmdlst').
  End step.
End cmb_step.


Section inv.
  Import VarValStore.Notations Util.List.

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable (adv: AdvStateMachine AtkStates). 
  Notation CmbState := (CmbState (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation cfg_step := (cfg_step adv).
  Notation cmbcmd_step := (cmbcmd_step adv).


  Definition CmbCmdCoreInv '(rcmd,icmd,pclbl) : Prop :=
    pclbl ⊢ rcmd /\ 
    (if (untrusted pclbl) is true 
      then (mk_lbl true true) ⊢ icmd  (* icmd is still a good public untrusted *)
      else rcmd = icmd). (* The rcmd is still well typed *)

  Definition CmbCmdInv (cmb_cmd: CmbCmd) : Prop :=
    let: mk_cmbcmd rcmd _ icmd pclbl := cmb_cmd in (* TODO: is_atk does not make an appearance... *)
    CmbCmdCoreInv (rcmd, icmd, pclbl).

  Definition StateInv (s: CmbState): Prop :=
    let: mk_cmbstate real_st ideal_st sim_st _ := s in
    ⟨ real_st | is_trusted ⟩ = ⟨ ideal_st | is_trusted ⟩ /\
    ⟨ real_st | is_public ⟩ = ⟨ sim_st | is_public ⟩.

  Definition Invariant (c : Cfg): Prop :=
    let: (cmbst, cmdlst) := c in
    Forall CmbCmdInv cmdlst /\
    StateInv cmbst.
End inv.

Section thm.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Import VarValStore.Notations Util.List.
   Lemma Forall_CmbCmd_zip:
     forall l1 l2 substeps pc_lbl,
       (* TODO: I didn't have fst and snd before, and that wait painful. How to solve? *)
       Forall (fun p => CmbCmdCoreInv (p.1, p.2, pc_lbl))  (combine_extend2 (map Some l1) (map Some l2) None None) ->
       Forall CmbCmdInv (zip l1 l2 substeps pc_lbl).
   Proof.
     move=> *; rewrite /zip.
     apply/Forall_map/Forall_combine2_ind1;[|eassumption|]=> //= => [[] [] > //|].
     if_easy_goals.
   Qed.

End thm.

Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1
    ltac1:(lazymatch goal with
           | |- Forall _ (zip _ _ _ _) => apply/Forall_CmbCmd_zip
           end)
    "Forall_CmbCmd_zip" old.

Section invprf.
  Import Attacker Util Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable (adv: AdvStateMachine AtkStates). 
  Notation CmbState := (CmbState (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation cfg_step := (cfg_step adv).
  Notation cmbcmd_step := (cmbcmd_step adv).

  Section cook.
    Import VarValStore.Notations.

    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()).
    Ltac2 Set curr_cookbook as old := join_cookbooks Semantics.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks TypeSystem.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Attacker.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.List.this_cookbook old.


    Ltac2 Eval print_cookbook curr_cookbook.
    Ltac2 Eval print_cookbook curr_stirbook.

    Hint Extern 10 => lazymatch goal with |- _ => apply:pubuntr_wf_cont end: core.
    Hint Extern 10 => lazymatch goal with |- _ => apply:step_soundness end: core.
    Ltac2 Set cook_auto_dbs := fun () => [@trickbag].

(*    Hint Extern 100 => lazymatch goal with _ =>  cbn end : trickbag. *)

(* TODO 3 debug levels *)
    Ltac2 Set cook_debug := false. (* TODO: Why can't I access this? *)
    Ltac2 Set cook_auto_depth := 4.
    (* TODO: Why does cook make this extremely slow? *)
    (* TODO: Set Ltac Profiling *)
    Lemma cmbcmd_step_inv: 
      forall c st, 
        CmbCmdInv c ->
        StateInv st ->
        let: (st', clst') := cmbcmd_step c st in
        StateInv st' /\ Forall CmbCmdInv clst'.
    Proof. 
      case; rewrite {}/CmbCmdInv=> - []; cycle 1. 

      - move=>>[]_; rewrite/StateInv=> + [].
        (case pce: (untrusted _))=> [* /= | <- /= <- *]; repeat split; cook.
         { revert_hyp_type_dep (option Cmd); case => /= *; cook. }
        move=> /=. 
        apply/Forall_and; [stir|]. 
        rewrite-/(WellFormedProg _ _).
        revert_hyp_type_dep (option Cmd); case=> /= *; cook.

      - rewrite /CmbCmdCoreInv=> > []; rewrite /(_⊢_)/cmbcmd_step/StateInv=> ? ? [>]; repeat split; stir.
          { revert_hyp_type bool; case; stir.
          1-2: revert_hyp_type_dep PcLbl; case=> [[] ?] /=; stir. 
          1-2: revert_hyp_type_dep (option Cmd); case=> /= *; cook.  }
          { revert_hyp_type_dep PcLbl; case=> [+ []] /==> *; stir. }
        move=> /=.  
        apply/Forall_and; stir.
        revert_hyp_type_dep PcLbl; case=> [[] ?] /= >. {
           move=> *; stir.
           revert_hyp_type_dep (option Cmd)=> - [] //= >.
           rewrite -/(WellFormedProg _ _).
           move=> /step_soundness=> snd.
           apply/flows_to_subtype_prog;[|apply/snd].
           stir. } 
        move=> /= ? <- /=.
        move ?: (compute_new_pc _ _)=> [[] ?] /=; cycle 1. 
           {erewrite tr_cmd_cnt; [apply/Forall_combine2_same/Forall_map/Forall_forall => // | eassumption |..]. 
           1-2: stir. }
        stir.
        rewrite-/(WellFormedProg _ _). (* TODO: lift that weakening thing to wf prog also*)
        revert_hyp_type_dep Cmd=> ? /step_soundness snd newpce.
        apply/flows_to_subtype_prog; [|apply/snd].
        stir.
    Qed. 
  End cook.

  Theorem cfg_step_inv: forall c, Invariant c ->  Invariant (cfg_step c).
  Proof.
    case=> + [] //.
    rewrite/Invariant/cfg_step=> > []; toph Forall_inv.
    case e: (cmbcmd_step _ _)=> h1 ? h2. 
    move: (cmbcmd_step_inv _ _ h1 h2); rewrite {}e=> - [] *.
    split=> //; apply/Forall_app=> //.
  Qed.

  Print Assumptions cfg_step_inv.
End invprf.
