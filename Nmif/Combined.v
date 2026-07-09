From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade WfFinisher.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade WfFinisher Tacs.Cook.

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
    pc_lbl : Label ;
  }.

  Fact real_cmd_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (real_cmd (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.

  Fact real_atk_bit_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (real_atk_bit (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.

  Fact ideal_cmd_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (ideal_cmd (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.

  Fact pc_lbl_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (pc_lbl (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.
End cmb_cmd.

Section cmb_step.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).
  Notation AdvInit := (AdvInit (AtkStates := AtkStates)).

  Definition zip (real_cont: list Cmd) (ideal_cont: list Cmd) (atk_steps: nat) (pc_lbl: Label): list CmbCmd :=
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

  Section init.
    Import VarValStore.Notations.
    Variable (prog: Prog) (advinit : AdvInit) (init_store: Store).

    Definition init_cfg : Cfg := 
      (mk_cmbstate 
        init_store 
        init_store 
        ( let: blank := fun _ => val_ne in 
          let: pubsv := ⟨ init_store | is_public ⟩ in
          ⟨ pubsv → blank ⟩ )
        (init_fn advinit init_store), 
      map (fun c => mk_cmbcmd (Some c) true (Some c) ptlbl) prog). 
  End init.


  Section step.
    Variable (adv: AdvNextStep).
    Notation pre_cmd_action := (pre_cmd_action adv).
    Notation post_cmd_action := (post_cmd_action adv).

    Definition cmbcmd_step (c: CmbCmd) (s: CmbState) : Cfg :=
      let: mk_cmbcmd real_cmd real_atk_bit ideal_cmd pc_lbl := c in
      let: mk_cmbstate real_st ideal_st sim_st atk_st := s in

      (* Corruption first. TODO: When there is endorsement, there will need to be an update to the ideal store as well *)
      let: real_st := if real_atk_bit is false then real_st else pre_cmd_action atk_st real_st in
      let: (real_cnt, real_st ) := (optcmd_stp_cnt real_cmd real_st,  optcmd_stp_store real_cmd real_st) in (* TODO: The proof breaks when you update real_st before real_cnt. Why? *)


      let: sim_st := if real_atk_bit is false then sim_st else pre_cmd_action atk_st sim_st in
      (* If pc is secret, then there will not be any change to public vars, so this is okay!    The simulator will not have access to real_cmd in a secret branch *)
      let: sim_st := if (public pc_lbl) is false then sim_st else optcmd_stp_store real_cmd sim_st  in


      (* Controlled ideal corruption *)
      let: ideal_st :=  if oapp extract_controlled_endorse None real_cmd isn't Some (from, to) then ideal_st else
                          update_to_store ideal_st from (sim_st from) in (* get the value of from from sim_st, then update to ideal_st *)
      let: (ideal_cnt, ideal_st) :=  (optcmd_stp_cnt ideal_cmd ideal_st, optcmd_stp_store ideal_cmd ideal_st) in


      let: sim_st := if oapp extract_controlled_declassify None real_cmd isn't Some (from, to) then sim_st else
                      update_to_store sim_st to (ideal_st to) in (* Controlled ideal read *)


      let: atk_pst := (post_cmd_action atk_st real_st) in (* Not having this was quite painful. TODO *)
      let: atk_st := if real_atk_bit is false then atk_st else atk_pst.1 in
      let: atk_substeps := if real_atk_bit is false then 0 else atk_pst.2 in

      let: new_pc := compute_new_pc_opt pc_lbl real_cmd in
      (mk_cmbstate real_st ideal_st sim_st atk_st, zip real_cnt ideal_cnt atk_substeps new_pc).

    Definition cfg_step (cfg: Cfg) : Cfg :=
      let: (st, cmdlst) := cfg in
      if cmdlst isn't (cmd :: cmdlst') then cfg (*, blank_event *) else
      let: (st', cmdlst'' (*, evnt *)) := cmbcmd_step cmd st in
      (st', cmdlst'' ++ cmdlst').

    Definition cmb_event (c: Cfg) : Event :=
      let: (st, cmdlst) := c in
      if cmdlst isn't (mk_cmbcmd real_cmd real_atk_bit _ _ :: _) then blank_event else
      let: atk_st := atk_st st in
      let: store := real_store st in
      event_gen adv (mk_atkcmd real_atk_bit real_cmd) store atk_st.
  End step.
End cmb_step.

Section sim_active.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Definition sim_active' (rcmd: option Cmd) (ratk: bool) (is_pubpc: bool) : bool :=
    ratk || (is_pubpc && if rcmd is None then false else true).

  (* This is bidirectional; we only state/use the forward direction. *)
  Lemma sim_active'_false rcmd ratk pub :
    sim_active' rcmd ratk pub = false ->
    ratk = false /\ (pub = false \/ rcmd = None).
  Proof.
    rewrite /sim_active'.
    case: ratk=> //=.
    case: pub=> //=; [| move=> _; repeat constructor; done ].
    case: rcmd=> [c | ] //=.
    move=> _; repeat constructor; done.
  Qed.

  Definition sim_active (c: CmbCmd) : bool :=
    sim_active' (real_cmd c) (real_atk_bit c) (public (pc_lbl c)).
End sim_active.

Section erase_filters.
  Context `{!VarPrm, !ValPrm}.
  Definition real_active (c: CmbCmd) : bool := 
    let: mk_cmbcmd rl rltak _ _ := c in
    isSome rl || rltak.

  Definition ideal_active (c: CmbCmd) : bool := 
    let: mk_cmbcmd _ _ idl _ := c in
    isSome idl || sim_active c.
End erase_filters.

Section erase_extract.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.

  Notation CombCfg := (Combined.Cfg (AtkStates:= AtkStates)).


  Definition erase_filter_cfg (is_left : bool) (c : CombCfg) : CombCfg :=
    let test := fun c => (if is_left then real_active c else ideal_active c) in
    let: (st,cmdlst) := c in
    (st,  filter test cmdlst).

End erase_extract.

Section inv.
  Import VarValStore.Notations Util.List.

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).
  Variable (adv: AdvNextStep). 
  Notation CmbState := (CmbState (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation cfg_step := (cfg_step adv).
  Notation cmbcmd_step := (cmbcmd_step adv).

  Definition ActiveInv '(rcmd, icmd, isatk) : Prop :=
    isatk || isSome (rcmd : option Cmd) || isSome (icmd : option Cmd). 

  Definition TypeInv '(rcmd, icmd,pclbl) : Prop :=
    pclbl ⊢ rcmd /\ 
    (if (untrusted pclbl) is true 
      then (mk_lbl true true) ⊢ icmd  (* icmd is still a good public untrusted *)
      else rcmd = icmd). (* The rcmd is still well typed *)

  Definition CmbCmdInv (cmb_cmd: CmbCmd) : Prop :=
    let: mk_cmbcmd rcmd isatk icmd pclbl := cmb_cmd in (* TODO: is_atk does not make an appearance... *)
    TypeInv (rcmd, icmd, pclbl) /\ ActiveInv (rcmd, icmd, isatk).

  Definition StateInv (s: CmbState): Prop :=
    let: mk_cmbstate real_st ideal_st sim_st _ := s in
    ⟨ real_st | is_trusted ⟩ = ⟨ ideal_st | is_trusted ⟩ /\
    ⟨ real_st | is_public ⟩ = ⟨ sim_st | is_public ⟩.

  Definition CombinedInvariant (c : Cfg): Prop :=
    let: (cmbst, cmdlst) := c in
    Forall CmbCmdInv cmdlst /\
    StateInv cmbst.
End inv.

Section thm.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Import VarValStore.Notations Util.List.

  Lemma ActiveInv_combine_extend3 l1 l2 n: 
    Forall ActiveInv  (combine_extend3 (map Some l1) (map Some l2) (repeat true n) None
     None false).
  Proof.
    rewrite/ActiveInv.
    apply: Forall_impl.
      { case. case=> >. instantiate (1 := fun '(a,b,c) => is_true a \/ is_true b \/ is_true c)=> /= h.
      apply/ orP. case: h=> [| []] *; constructor; try apply/orP; try constructor; done. }
    apply/Forall_combine3_disj; clear. 
    1: move: l1. 2: move: l2. 3: move: n.
    1,2,3:elim=> //= *; constructor; done.
  Qed.

   Lemma Forall_CmbCmd_zip l1 l2 substeps pc_lbl:
       (* TODO: I didn't have fst and snd before, and that wait painful. How to solve? *)
       Forall (fun p => TypeInv (p.1, p.2, pc_lbl))  (combine_extend2 (map Some l1) (map Some l2) None None) ->
       Forall CmbCmdInv (zip l1 l2 substeps pc_lbl).
   Proof.
     move=> *. rewrite /zip.
     rewrite/CmbCmdInv. apply: Forall_and.
       { apply/Forall_map/Forall_combine2_ind1;[|eassumption|]=> //= => [[] [] > //|].
       move: (X in if X then _ else _)=> ?; if_easy_goals. } 
     rewrite Forall_map.
     apply: Forall_impl; [case; case=> > h; exact h|].
     exact: ActiveInv_combine_extend3.
   Qed.
End thm.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> real_cmd_mk ) "real_cmd_mk" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> real_atk_bit_mk ) "real_atk_bit_mk" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> ideal_cmd_mk) "ideal_cmd_mk" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> pc_lbl_mk) "pc_lbl_mk" old.

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac local_cook := ltac2:(cook this_cookbook).

Section init_inv.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Notation AdvInit := (AdvInit (AtkStates := AtkStates)).
    
  Theorem init_inv p (advinit : AdvInit) init_store: 
    WellFormedProg ptlbl p ->
    CombinedInvariant (init_cfg p advinit init_store).
  Proof.
    move=> wf.
    rewrite/CombinedInvariant/init_cfg; split; cycle 1.
      { rewrite/StateInv. split=>//.
      rewrite /⟨_→_⟩.
      apply:storeview_eq_ext=> > e. (* TODO: lemma *)
      rewrite /⟨_|_⟩ e //. }
    rewrite Forall_map.
    move: wf. exact: Forall_impl.
  Qed.
End init_inv.

Section invprf.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).
  Variable (adv: AdvNextStep).

  Notation CmbState := (CmbState (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation cfg_step := (cfg_step adv).
  Notation cmbcmd_step := (cmbcmd_step adv).

  Section cook.
    Import DecEq DecEq.Notations.
    Import VarValStore.Notations.

    Ltac2 mutable curr_cookbook () :=  this_cookbook_ ().
    Ltac2 Set curr_cookbook as old := join_cookbooks Semantics.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks TypeSystem.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Attacker.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.List.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks VarValStore.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Syntax.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Lattice4pt.this_cookbook old.

    Ltac2 Eval print_cookbook curr_cookbook.

    Hint Extern 10 => lazymatch goal with
           |- context [compute_new_pc (mk_lbl true ?p) ?c] =>
              move: ([elaborate compute_new_pc_untr p c])=> [] + ->
           end: core.
    Hint Extern 10 => lazymatch goal with |- _ => apply:step_soundness end: core.

(*    Hint Extern 100 => lazymatch goal with _ =>  cbn end : trickbag. *)

(* TODO 3 debug levels *)
    Ltac2 Set cook_debug := 0. (* TODO: Why can't I access this? *)
    (* TODO: Why does cook make this extremely slow? *)
    (* TODO: Set Ltac Profiling *)

    Ltac cook := ltac2:(cook curr_cookbook).

    Lemma cmbcmd_step_inv:
      forall c st,
        CmbCmdInv c ->
        StateInv st ->
        let: (st', clst') := cmbcmd_step c st in
        StateInv st' /\ Forall CmbCmdInv clst'.
    Proof.
      case; rewrite {}/CmbCmdInv=>  -  [] ; cycle 1.
        { move=>>  [] + _=>- [] _ . rewrite/StateInv=> + [].
        case pce: (untrusted _); cycle 1.
        1: move=> <- /= <- *.
        2: move=> * /=. 
        1,2: repeat split; cook.
        1,2,5: enter (idtac; wf_finisher).
          {apply: Forall_CmbCmd_zip; cook. } 
          {  wf_finisher_guess [RHS] with ⟨ ideal_store _ | is_trusted ⟩=> ->. cook.
          wf_finisher_guess [LHS] with ⟨ real_store _ | is_trusted ⟩=> ->. cook. }
        apply: Forall_CmbCmd_zip; cook.
        move=> /=. 
        apply/Forall_and; cook; auto with trickbag.
        rewrite-/(WellFormedProg _ _).
        revert_hyp_pat [(option Cmd), (_ ⊢ _)]; case=> /==> [|* //] >.
        apply: step_soundness_pubuntr=> //. } 
      rewrite /TypeInv=>   > [] + _=> - []; rewrite /(_⊢_)/cmbcmd_step/StateInv=> ? ? [>].
      repeat split; cook.
        { move x: (extract_controlled_endorse _)=> x'; move: x' x. 
        case=> [[>]/extr_endorse_eq [] + [] |noend]. (* TODO move to case? *)
          { move=>e; rewrite -> e in *=> {e} /[dup] ? /[swap] /[dup] ? /[swap].
          revert_hyp_pat (WellFormedCmd _ _)=> /wf_endorse_pc /[apply] /[apply] e; rewrite -> e in *=> {e}.
          revert_hyp_pat (if _ then _ else _)=>  <-. cook.

          apply: wf_endorse_st_int; cook. (* TODO: Clean this up *)
            { symmetry. apply: endorse_pre_read_eq; cook. wf_finisher. }
          apply: update_untr_keep_view; cook. 
          wf_finisher_guess [RHS] with _=> ->. wf_finisher. } 

        revert_hyp_pat bool; case.
        1-2: revert_hyp_pat [Label, (WellFormedCmd _ _), (if _ then _ else _)]; case=> [[] ?] /=.
        2,4: enter (move=> ? <- /=; wf_finisher_guess [RHS] with ⟨clean_cmd_stp_store _ _ | is_trusted ⟩=> ->; wf_finisher).
        1,2: revert_hyp_pat (option _); case=> /= *. 
        (* When I have time, I'd like to automate this *)
        1,2: wf_finisher_guess [LHS] with ⟨clean_cmd_stp_store _ (real_store _) | is_trusted ⟩=> ->. 
        1,3: wf_finisher_guess [RHS] with ⟨ ideal_store _ | is_trusted ⟩=> ->.
        1-4: wf_finisher_guess [LHS] with ⟨clean_cmd_stp_store _ (ideal_store _) | is_trusted ⟩=> ->.
        1-4: enter (idtac;wf_finisher). }

        { move x: (extract_controlled_declassify _)=> x'; move: x' x. case=> [[>]/extr_decl_eq [] + []|nodecl]; cycle 1.
          { revert_hyp_pat [Label, (WellFormedCmd _ _), (if _ then _ else _)]; case=> [+ []] /==> *.
          2: wf_finisher_guess [LHS] with ⟨if _ then _ else _ |is_public⟩=> ->. 
          1,2: case: (X in if X then _ else _); enter (idtac; wf_finisher). }
        move=> e; rewrite -> e in *=> {e} /[dup] ? /[swap] /[dup] ? /[swap].
        revert_hyp_pat (WellFormedCmd _ _)=> /wf_declassify_pc /[apply] /[apply] e; rewrite -> e in *=> {e} /=.
        revert_hyp_pat (if _ then _ else _)=> /= <- /=.
        (* TODO: Need automation here *)
        apply/storeview_eq_ext=> *; rewrite /clean_assign_stp_store /update_to_store /=. rewrite dec_eq_refl. (* TODO: Eventually this should be a rewrite rule also *)
        case e1: (_ =? _). 
          { unshelve apply: storeview_eq; [exact: is_trusted|..]; cook.
          wf_finisher_guess [LHS] with _=> -> //. }
        apply/storeview_eq; [|eassumption]; cook. wf_finisher. }
      move=> /=.  
      apply/Forall_CmbCmd_zip/Forall_and; cook; auto.
      revert_hyp_pat [Label, (WellFormedCmd _ _), (if _ then _ else _)].
      case=> [[] ?] /= >.
         { move=> *; cook.
         revert_hyp_pat [(option _), (_ ⊢ _)]; case=> //= >.
         rewrite -/(WellFormedProg _ _).
         move=> /step_soundness=> snd.
         apply/flows_to_subtype_prog;[|apply/snd]; auto. }
      move=> /= ? <- /=.
      move ?: (compute_new_pc _ _)=> [[] ?] /=; cycle 1. 
        { move x: (extract_controlled_endorse _)=> x'; move: x' x. case=> [[>]/extr_endorse_eq [] + [] |noend]; cycle 1.
           { pattern_eq_2  [clean_cmd_stp_cnt _ _] [clean_cmd_stp_cnt _ _]; [|move=>->; cook; apply Forall_forall=> //].
           wf_finisher_guess [RHS] with (clean_cmd_stp_cnt _ (real_store _))=> ->. cook. wf_finisher. }
        move=> e;rewrite -> e in *=> {e}; done. }
      cook. rewrite-/(WellFormedProg _ _). (* TODO: lift that weakening thing to wf prog also*)
      revert_hyp_pat [Cmd, (WellFormedCmd _ _), (compute_new_pc _ _ = _)].
      move=> ? /step_soundness snd newpce.
      apply/flows_to_subtype_prog; [|apply/snd].
      auto with trickbag.
    Qed. 
  End cook.

  Theorem cfg_step_inv: forall c, CombinedInvariant c ->  CombinedInvariant (cfg_step c).
  Proof.
    case=> + [] //.
    rewrite/CombinedInvariant/cfg_step=> cst ccmd rst  []. Forall_inv_toph=> cmdinv restinv stinv.
    move:cmbcmd_step_inv=> /(_ ccmd cst cmdinv stinv).
    case: cmbcmd_step=> > [] *. 
    split=> //; apply/Forall_app=> //.
  Qed.

  Print Assumptions cfg_step_inv.
End invprf.

Section invfilter.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.

  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation CmbState := (CmbState (AtkStates := AtkStates)).

  Variable (adv: AdvNextStep).


  Theorem erase_filter_inv (c :Cfg) b:
    CombinedInvariant c ->
    CombinedInvariant (erase_filter_cfg  b c).
  Proof.
    case: c=> >.
    rewrite/CombinedInvariant/erase_filter_cfg=> - [] + + /ltac:(split;auto).
    move=> + _. rewrite/CmbCmdInv=> ?.
    exact: Forall_filter.
  Qed.
End invfilter.
