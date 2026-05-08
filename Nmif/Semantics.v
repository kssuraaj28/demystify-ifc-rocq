From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.


Require Tacs Util VarValStore Attacker Syntax Lattice4pt.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Tacs.Dominate.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable dom_list_ () : dominate_taclist := [].

Ltac done_dstep := assert_goals 0 done.
Ltac2 Set dom_list_ as old := append_tac ltac1:(done_dstep) "done_dstep" old.

Ltac subst_dstep := assert_goals 1 (progress subst).
Ltac2 Set dom_list_ as old := append_tac ltac1:(subst_dstep) "subst_dstep" old.

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
Ltac optcmd_stp_store_simpl_dstep :=
   assert_goals 1
   (idtac;
   let e := fresh in let v := fresh in 
   move e: (optcmd_stp_store (Some _) _)=> v;
   rewrite/optcmd_stp_store/oapp/id in e; rewrite -{}e {v}).
Ltac2 Set dom_list_ as old := append_tac ltac1:(optcmd_stp_store_simpl_dstep) "optcmd_stp_store_simpl_dstep" old.

(* This is a decent forward reasoning tactic *)
Ltac if_easy_goals_dstep:=
  ensure_goals <= 1
  (
  idtac;
  (* In Ltac, doing match goals will do focus *)
  match goal with
  |- context [if ?b then _ else _] =>  
      let e := fresh in let v := fresh in 
      move e: b=> v; move: v e;
      (* TODO: Goal hygiene after every step *)
      case=> ?; try done (* TODO parameterize? *)
  end).

Ltac2 Set dom_list_ as old := append_tac ltac1:(if_easy_goals_dstep) "if_easy_goals_dstep" old.

Ltac rewrite_if_hyp_eq_dstep :=
  assert_goals 1
  (idtac;
  match goal with  (* rewriting obviously *)
  | H: ?x = (?b :> bool) |- context [if ?x then _ else _] =>
    is_constructor b; rewrite H
  end).

Ltac2 Set dom_list_ as old := append_tac ltac1:(rewrite_if_hyp_eq_dstep) "rewrite_if_hyp_eq_dstep" old.

Ltac if_same_dstep :=
  assert_goals 1
    (idtac;
    let x := fresh in
    set x := if _ then ?[B] else ?B;
    let t := eval cbv delta [x] in x in
    lazymatch t with
    | if ?b then ?b1 else _ =>
      have  {x} ->: x = b1; [destruct b; subst; done|]
    end).

Ltac2 Set dom_list_ as old := append_tac ltac1:(if_same_dstep) "if_same_dstep" old.

Ltac forall_map_dstep := assert_goals 1 (idtac; rewrite Forall_map).

Ltac2 Set dom_list_ as old := append_tac ltac1:(forall_map_dstep) "forall_map_dstep" old.


(* TODO: Maybe elsewere *)
Definition PcLbl := Lattice4pt.Label.

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
       let: newpc := gvarlbl ⊔ pclbl in
       WellFormedProg' WellFormedCmd newpc b1 -> (* TODO: How might things look without ⊔ *)
       WellFormedProg' WellFormedCmd newpc b2 ->
       _ pclbl (cond (gvar,comp) b1 b2)

  | wf_while: 
     forall gvar comp pclbl wbody,
       let: gvarlbl := var_lbl gvar in
       let: newpc := gvarlbl ⊔ pclbl in
       WellFormedProg' WellFormedCmd newpc wbody ->
       _ pclbl (while (gvar,comp) wbody).
  Set Elimination Schemes.
  
  Definition WellFormedProg pclbl prog := WellFormedProg' WellFormedCmd pclbl prog.

  Section ind.
    Variable P : PcLbl -> Cmd -> Prop.
    (* This is the right IH, I think because I made another toy example without nested inductive types *)
    (* 
       However, do we even need induction? Maybe we don't need it at all.. 
       So, can we do something weaker than inductively defining this then?
    *)

    Hypothesis hyp_assign : 
        forall dst src1 src2  comp pclbl,
          let: dstlbl := var_lbl dst in
          let: s1lbl := var_lbl src1 in
          let: s2lbl := var_lbl src2 in
          s1lbl ⊑ dstlbl -> s2lbl ⊑ dstlbl -> pclbl ⊑ dstlbl ->
          P pclbl (assign dst (src1, src2, comp)).

    (* I have no idea whether this is the right thing *)
    Hypothesis hyp_cond : 
        forall gvar comp pclbl b1 b2,
         let: gvarlbl := var_lbl gvar in
         let: newpc := gvarlbl ⊔ pclbl in
         Forall (WellFormedCmd newpc) b1 -> Forall (P newpc) b1 ->
         Forall (WellFormedCmd newpc) b2 -> Forall (P newpc) b2 ->
         P pclbl (cond (gvar, comp) b1 b2).

    Hypothesis hyp_while : 
        forall gvar comp pclbl wbody,
         let: gvarlbl := var_lbl gvar in
         let: newpc := gvarlbl ⊔ pclbl in
         Forall (WellFormedCmd newpc) wbody -> Forall (P newpc) wbody ->
         P pclbl (while (gvar, comp) wbody).

    Fixpoint WellFormedCmd_ind :
      forall p c, WellFormedCmd p c -> P p c. 
    Proof.
      move=> > []; [apply:hyp_assign|..]=> *.
      1-2: (apply: hyp_cond; clear hyp_cond) || (apply: hyp_while; clear hyp_while)=>//.
      1-3: lazymatch goal with
             H: Forall _ ?b |- Forall _ ?b => elim: H=> // *
            end.
      1-3: constructor 2=> //; auto.
    Qed.
  End ind.

  (* TODO: Importing Lattice4pt.Notations breaks. Why? *)
  Import Lattice4pt.
  Lemma flows_to_subtype_cmd c l1 l2:
      l2 ⊑ l1 -> (* TODO: I don't know whether this is true *)
      WellFormedCmd l1 c ->
      WellFormedCmd l2 c.
  Proof. 
    (* TODO: What does elim do? Is it just apply? *)  
    move: l2=> ++ h; elim: h=> *; [constructor=> //; eauto using flows_to_trans|..].
    1-2: constructor; (apply/Forall_impl;[ |eassumption])=> /= >; auto using join_mono_r.
  Qed.

  Lemma flows_to_subtype_prog :
    forall p l1 l2,
      l2 ⊑ l1 -> (* TODO: I don't know whether this is true *)
      WellFormedProg l1 p ->
      WellFormedProg l2 p.
  Proof. 
    rewrite/WellFormedProg=> *.
    apply/Forall_impl;[|eassumption].
    eauto using flows_to_subtype_cmd.
  Qed.
End sa.

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
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Definition compute_new_pc (old_pc : PcLbl) (cmd: Cmd): PcLbl :=
    match cmd with
    | cond (gvar,_) _ _ => var_lbl gvar ⊔ old_pc (* Can this be refactored w/ static analysis? *)
    | while (gvar,_) _ => var_lbl gvar ⊔ old_pc
    | _ => old_pc
    end.

  Definition compute_new_pc_opt (old_pc : PcLbl) (cmd: option Cmd): PcLbl :=
    if cmd isn't Some cmd then old_pc else
    compute_new_pc old_pc cmd.

  Lemma compute_new_pc_untr:
    forall p c, exists p',
      compute_new_pc (mk_lbl true p) c = (mk_lbl true p').
  Proof.
    move=> p [dst exp| [g cmp] b1 b2 | [g cmp] b]; cbn; eauto.
    1-2: case: (var_lbl g) => u pg. (* TODO: This could be a lemma *)
    1-2: exists (pg && p); case: u; done.
  Qed.
End new_pc.

Ltac compute_new_pc_untr_dstep :=
  assert_goals 1
    (
    idtac;
    lazymatch goal with
    |- context [compute_new_pc (mk_lbl true ?p) ?c] =>
       move: ([elaborate compute_new_pc_untr p c])=> [] ? /[dup] ? ->
    end).
(* TODO: Test.. *)

Ltac2 Set dom_list_ as old := append_tac ltac1:(compute_new_pc_untr_dstep) "compute_new_pc_untr_dstep" old.

Section cmb_step.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Definition zip (real_cont: list Cmd) (ideal_cont: list Cmd) (atk_steps: nat) (pc_lbl: PcLbl): list CmbCmd :=
    let: real_cont := map Some real_cont in
    let: ideal_cont := map Some ideal_cont in
    let: atk_steps := repeat true atk_steps in
    let: comb := List.combine_extend3 real_cont ideal_cont atk_steps None None false in
    map (fun '(rc, ic, abit) => mk_cmbcmd rc abit ic pc_lbl) comb.


  Import VarValStore.Notations.
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
    move=> + > => - []=> * //=; if_easy_goals_dstep.
    apply/Forall_app. split=> //.
    constructor 2=> //.
    constructor 3. apply/Forall_impl; [| eassumption]; clear=> *.
    rewrite -join_assoc join_idem=> //.
  Qed.

  Context {AtkStates : Type}.

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

    (* mstep == multistep *)
    Definition cfg_step (cfg: Cfg) : Cfg := 
      let: (st, cmdlst) := cfg in
      if cmdlst isn't (cmd :: cmdlst') then cfg else
      let: (st', cmdlst'') := cmbcmd_step cmd st in
      (st', cmdlst'' ++ cmdlst').
  End step.
End cmb_step.


Section inv.
  Import Lattice4pt.
  Import VarValStore.Notations.

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable (adv: AdvStateMachine AtkStates). 
  Notation CmbState := (CmbState (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation cfg_step := (cfg_step adv).
  Notation cmbcmd_step := (cmbcmd_step adv).

  Definition WellFormedOptCmd (pc: PcLbl) (ocmd : option Cmd): Prop :=
    if ocmd isn't Some cmd then True else WellFormedCmd pc cmd.

  (* TODO: Notation location *)
  Notation "pc ⊢ ocmd" := (WellFormedOptCmd pc ocmd) (at level 20).

  Definition CmbCmdCoreInv '(rcmd,icmd,pclbl) : Prop :=
    pclbl ⊢ rcmd /\ 
    (if (untrusted pclbl) is true 
      then (mk_lbl true true) ⊢ icmd  (* icmd is still a good public untrusted *)
      else rcmd = icmd). (* The rcmd is still well typed *)

  Definition CmbCmdInv (cmb_cmd: CmbCmd) : Prop :=
    let: mk_cmbcmd rcmd _ icmd pclbl := cmb_cmd in (* TODO: is_atk does not make an appearance... *)
    CmbCmdCoreInv (rcmd, icmd, pclbl).

  Lemma wt_cmd_st_conf c l st1 st2:
      WellFormedCmd l c ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof. 
    move=> [] // d s1 s2 ? ?. 
    case de: ([elaborate is_public d])=> fs1d fs2d _ pubeq /=; [| rewrite !update_storeview_nochange //].
    move: (flows_to_pub _ _ de fs1d)=> {fs1d} ps1. (* TODO: Tactic *)
    move: (flows_to_pub _ _ de fs2d)=> {fs2d} ps2.
    set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
    set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
    suff: v1 = v2; [move=> ->; apply/update_same_varval=> //|subst v1 v2].
    f_equal; eauto using storeview_eq. 
  Qed.

  (* In a secret context, the public view is constant *)
  Lemma wt_cmd_st_conf_sec:
    forall c i st, 
      WellFormedCmd (mk_lbl i false) c ->
      ⟨ clean_cmd_stp_store c st | is_public ⟩ =
      ⟨ st | is_public ⟩.
  Proof. 
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap]. 
    case=> //= > +++e; rewrite -{}e=> _ _ flw.
    rewrite update_storeview_nochange=> //.
    rewrite/is_public. 
    apply/negbTE/flows_from_sec; rewrite/secret; eauto; done.
  Qed.

  Lemma wt_cmd_st_int c l st1 st2: 
      WellFormedCmd l c ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof.  
    move=> [] // d s1 s2 ? ?. 
    case de: ([elaborate is_untrusted d])=> fs1d fs2d _ treq /=;
      [do 2 (rewrite update_storeview_nochange{1}/is_trusted; [rewrite de //|])=> //|].  
    rewrite/is_trusted/is_untrusted/= in de.
    move: de=>/untrusted_false td. (* TODO: Automation *)
    move: (flows_to_tr _ _ td fs1d)=> {fs1d} ts1. (* TODO: Tactic *)
    move: (flows_to_tr _ _ td fs2d)=> {fs2d} ts2.
    set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
    set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
    suff: v1 = v2; [move=> ->; apply/update_same_varval=> //|subst v1 v2].
    f_equal; eauto using storeview_eq.
  Qed.

  Lemma wt_cmd_st_int_untr:
    forall p c st, 
    WellFormedCmd (mk_lbl true p) c ->
    ⟨ clean_cmd_stp_store c st | is_trusted ⟩ =
    ⟨ st | is_trusted ⟩.
  Proof. 
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap]. 
    case=> //= > +++e; rewrite -{}e=> _ _ flw.
    rewrite update_storeview_nochange=> //.
    rewrite/is_trusted/is_untrusted negbF //.
    apply/flows_from_untr; eauto; done.
  Qed.

  Ltac wt_cmd_st_int_untr_dstep :=
    assert_goals 1
    (idtac; unshelve erewrite wt_cmd_st_int_untr;[..|eassumption]).
  Ltac2 Set dom_list_ as old := append_tac ltac1:(wt_cmd_st_int_untr_dstep) "wt_cmd_st_int_untr_dstep" old.

  Ltac wt_cmd_st_conf_sec_dstep :=
    assert_goals 1
    (idtac; unshelve erewrite wt_cmd_st_conf_sec;[..|eassumption]).
  Ltac2 Set dom_list_ as old := append_tac ltac1:(wt_cmd_st_conf_sec_dstep) "wt_cmd_st_conf_sec_dstep" old.

  Ltac wt_cmd_st_int_dstep :=
    assert_goals 1
    (idtac; apply/wt_cmd_st_int; [eassumption|]).
  Ltac2 Set dom_list_ as old := append_tac ltac1:(wt_cmd_st_int_dstep) "wt_cmd_st_int_dstep" old.

  Ltac wt_cmd_st_conf_dstep :=
    assert_goals 1
    (idtac; apply/wt_cmd_st_conf; [eassumption|]).
  Ltac2 Set dom_list_ as old := append_tac ltac1:(wt_cmd_st_conf_dstep) "wt_cmd_st_conf_dstep" old.

   Import Util.List.
   Lemma Forall_zip:
     forall l1 l2 substeps pc_lbl,
       (* TODO: I didn't have fst and snd before, and that wait painful. How to solve? *)
       Forall (fun p => CmbCmdCoreInv (p.1, p.2, pc_lbl))  (combine_extend2 (map Some l1) (map Some l2) None None) ->
       Forall CmbCmdInv (zip l1 l2 substeps pc_lbl).
   Proof.
     move=> *; rewrite /zip.
     apply/Forall_map/Forall_combine2_ind1;[|eassumption|]=> //= => [[] [] > //|].
     if_easy_goals_dstep.
   Qed.

   Ltac forall_zip_dstep :=
     assert_goals 1
     (idtac;
     match goal with
     | |- Forall _ (zip _ _ _ _) => apply/Forall_zip
     end).
   Ltac2 Set dom_list_ as old := append_tac ltac1:(forall_zip_dstep) "forall_zip_dstep" old.

   Ltac forall_combine2_ind_dstep :=
     assert_goals 2
     (idtac;
     match goal with
     | |- Forall _ (combine_extend2 _ _ _ _) => apply/Forall_combine2_ind1; [move=> ?; apply|..]
     | |- Forall _ (combine_extend2 _ _ _ _) => apply/Forall_combine2_ind2; [move=> ?; apply|..]
     end).
   Ltac2 Set dom_list_ as old := append_tac ltac1:(forall_combine2_ind_dstep) "forall_combine2_ind_dstep" old.


  Lemma pubuntr_wf_cont: 
    forall c st, 
      WellFormedCmd (mk_lbl true true) c -> 
      WellFormedProg (mk_lbl true true) (clean_cmd_stp_cnt c st).
  Proof. 
    rewrite/WellFormedProg=> >;  move l: (mk_lbl _ _)=> ?; move: l=> /[swap].
    case=> //= >; rewrite  -!/(WellFormedProg _ _)=>>. 
    1: move=> ++ e; rewrite -{}e => *.
    2: move=> + e; rewrite -{}e => *.
    1-2: case: (X in if X then _ else _) => //. (* all is antipattern *)
    3: apply/Forall_app; split;[|repeat constructor=>//]; 
        rewrite -/(WellFormedProg _ _).
    1-3: apply/flows_to_subtype_prog;[|eassumption].
    1-3: case: (var_lbl)=> [[] []]=> //. (* TODO: This should be lemma *)
  Qed.


  Definition StateInv (s: CmbState): Prop :=
    let: mk_cmbstate real_st ideal_st sim_st _ := s in
    ⟨ real_st | is_trusted ⟩ = ⟨ ideal_st | is_trusted ⟩ /\
    ⟨ real_st | is_public ⟩ = ⟨ sim_st | is_public ⟩.

  Definition Invariant (c : Cfg): Prop :=
    let: (cmbst, cmdlst) := c in
    Forall CmbCmdInv cmdlst /\
    StateInv cmbst.


  Section dom.
    Ltac2 Set curr_dom_list := (fun () => dom_list_ ()).
    Ltac2 Set curr_dom_list as old := join_tacs Attacker.dom_list old.

    Ltac2 Eval print_domlist (keep_only curr_dom_list [1;3]).
    Ltac2 Eval print_domlist (delete curr_dom_list [1;3]).
    Ltac2 Eval print_domlist curr_dom_list.
    Ltac2 Set dom_debug := false. (* TODO: Why can't I access this? *)

    Hint Resolve pubuntr_wf_cont : core.
    (* TODO: Why can I not add resolve? *)
    Hint Extern 10 => lazymatch goal with |- _ => apply:step_soundness end: core.
    Hint Extern 10 => lazymatch goal with H : _ = _ |- _ => rewrite H end : trickbag. (* TODO: This should go somewhere good *)
    Hint Extern 10 => lazymatch goal with H : _ = _ |- _ => rewrite -H end : trickbag. (* TODO: This should go somewhere good *)
    Hint Extern 10 => lazymatch goal with _ =>  apply/Forall_forall end : trickbag.
(*    Hint Extern 100 => lazymatch goal with _ =>  cbn end : trickbag. *)
    Ltac2 Set dom_auto_dbs := fun () => [@trickbag].

    Lemma cmbcmd_step_inv: 
      forall c st, 
        CmbCmdInv c ->
        StateInv st ->
        let: (st', clst') := cmbcmd_step c st in
        StateInv st' /\ Forall CmbCmdInv clst'.
    Proof. 
      case; rewrite {}/CmbCmdInv=> - []; cycle 1. 

      - move=>>[]_; rewrite/StateInv=> + [].
        (case pce: (untrusted _))=> [* /= | <- /= <- *]; repeat split; dominate. 
          { revert_hyp_type_dep (option Cmd); case => /=; dominate. }
        move=> /=; dominate. (* This is automatable Forall True /\ ..*)
        apply/Forall_and; dominate. 
        rewrite-/(WellFormedProg _ _).
        revert_hyp_type_dep (option Cmd); case=> * /=; dominate.

      - rewrite /CmbCmdCoreInv=> > []; rewrite /(_⊢_)/cmbcmd_step/StateInv=> ? ? [>]; repeat split; dominate.
          { revert_hyp_type bool; case; dominate.
          1-2: revert_hyp_type_dep PcLbl; case=> [[] ?] /=; dominate. 
          1-2: revert_hyp_type_dep (option Cmd); case=> /=; dominate. } 
          { revert_hyp_type_dep PcLbl; case=> [+ []] /==> *; dominate. }
        move=> /=.  
        apply/Forall_and; dominate.
        revert_hyp_type_dep PcLbl. case=> [[] ?] /=.
          { dominate.
           revert_hyp_type_dep (option Cmd); case=> //= >.
           rewrite -/(WellFormedProg _ _).
           move=> /step_soundness=> snd.
           apply/flows_to_subtype_prog;[|apply/snd].
           dominate. }
        move=> /= ? <- /=.
        move ?: (compute_new_pc _ _)=> [[] ?] /=; cycle 1. 
           {erewrite tr_cmd_cnt; [apply/Forall_combine2_same/Forall_map/Forall_forall => // | eassumption |..] ; dominate.
             }
        dominate.
        rewrite-/(WellFormedProg _ _). (* TODO: lift that weakening thing to wf prog also*)
        revert_hyp_type_dep Cmd=> ? /step_soundness snd newpce.
        apply/flows_to_subtype_prog; [|apply/snd].
        dominate.
    Qed. 

  End dom.


  Import Util.List.
  Theorem cfg_step_inv: forall c, Invariant c ->  Invariant (cfg_step c).
  Proof.
    case=> + [] //.
    rewrite/Invariant/cfg_step=> > []; toph Forall_inv.
    case e: (cmbcmd_step _ _)=> h1 ? h2. 
    move: (cmbcmd_step_inv _ _ h1 h2); rewrite {}e=> - [] *.
    split=> //; apply/Forall_app=> //.
  Qed.

  Print Assumptions cfg_step_inv.

End inv.


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
*)
