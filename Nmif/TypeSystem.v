From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

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
  | wf_endorse: 
     forall from to,
       let: ptlbl := mk_4ptlbl false true in let: pulbl := mk_4ptlbl true true in
       var_lbl from = pulbl -> var_lbl to = ptlbl ->
       _ ptlbl (assign (endorse from to))

  | wf_declassify: 
     forall from to,
       let: ptlbl := mk_4ptlbl false true in let: stlbl := mk_4ptlbl false false in
       var_lbl from = stlbl -> var_lbl to = ptlbl ->
       _ ptlbl (assign (declassify from to))

  | wf_assign: 
     forall dst src1 src2 comp pclbl, 
       let: dstlbl := var_lbl dst in
       let: s1lbl := var_lbl src1 in
       let: s2lbl := var_lbl src2 in
       s1lbl ⊑ dstlbl -> s2lbl ⊑ dstlbl -> pclbl ⊑ dstlbl -> (* Using ssrbool coercion *)
       _ pclbl (assign (exp_assign (src1, src2, comp) dst))

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
       _ pclbl (while (gvar,comp) wbody)

  (* A "harmless" endorse / declassify whose projected flow is the ordinary
     assignment flow (from ⊑ to and pc ⊑ to). These do not actually cross the
     attacker (the real downgrade is wf_endorse / wf_declassify, where from ⋢ to).
     They let every full-lattice downgrade project to the 4-point system. *)
  | wf_endorse_safe:
     forall from to pclbl,
       var_lbl from ⊑ var_lbl to -> pclbl ⊑ var_lbl to ->
       _ pclbl (assign (endorse from to))

  | wf_declassify_safe:
     forall from to pclbl,
       var_lbl from ⊑ var_lbl to -> pclbl ⊑ var_lbl to ->
       _ pclbl (assign (declassify from to)).

  Set Elimination Schemes.
  
  Definition WellFormedProg pclbl prog := WellFormedProg' WellFormedCmd pclbl prog.

  Section ind.
    Variable P : PcLbl -> Cmd -> Prop.

    (* 
       However, do we even need induction? Maybe we don't need it at all.. 
       So, can we do something weaker than inductively defining this then?
    *)
    Hypothesis hyp_endorse : 
        forall from to,
          let: ptlbl := mk_4ptlbl false true in let: pulbl := mk_4ptlbl true true in
          var_lbl from = pulbl -> var_lbl to = ptlbl ->
          P ptlbl (assign (endorse from to)).

    Hypothesis hyp_declassify : 
        forall from to,
          let: ptlbl := mk_4ptlbl false true in let: stlbl := mk_4ptlbl false false in
          var_lbl from = stlbl -> var_lbl to = ptlbl ->
          P ptlbl (assign (declassify from to)).

    Hypothesis hyp_assign : 
        forall dst src1 src2  comp pclbl,
          let: dstlbl := var_lbl dst in
          let: s1lbl := var_lbl src1 in
          let: s2lbl := var_lbl src2 in
          s1lbl ⊑ dstlbl -> s2lbl ⊑ dstlbl -> pclbl ⊑ dstlbl ->
          P pclbl (assign (exp_assign (src1, src2, comp) dst)).

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

    Hypothesis hyp_endorse_safe :
        forall from to pclbl,
          var_lbl from ⊑ var_lbl to -> pclbl ⊑ var_lbl to ->
          P pclbl (assign (endorse from to)).

    Hypothesis hyp_declassify_safe :
        forall from to pclbl,
          var_lbl from ⊑ var_lbl to -> pclbl ⊑ var_lbl to ->
          P pclbl (assign (declassify from to)).

    Fixpoint WellFormedCmd_ind p c (H : WellFormedCmd p c) {struct H} : P p c.
    Proof.
      case: H.
      - exact: hyp_endorse.
      - exact: hyp_declassify.
      - exact: hyp_assign.
      - move=> gvar comp pclbl b1 b2 H1 H2. apply: hyp_cond.
        + exact: H1.
        + elim: H1 => // *; constructor 2 => //; auto.
        + exact: H2.
        + elim: H2 => // *; constructor 2 => //; auto.
      - move=> gvar comp pclbl wbody H1. apply: hyp_while.
        + exact: H1.
        + elim: H1 => // *; constructor 2 => //; auto.
      - exact: hyp_endorse_safe.
      - exact: hyp_declassify_safe.
    Qed.
  End ind.
  Definition WellFormedOptCmd (pc: PcLbl) (ocmd : option Cmd): Prop :=
    if ocmd isn't Some cmd then True else WellFormedCmd pc cmd.

  Fact WellFormedOptCmd_Some pc c :
    ltac2:(cbn_eq (WellFormedOptCmd pc (Some c))).
  Proof. done. Qed.
End sa.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> WellFormedOptCmd_Some) "WellFormedOptCmd_Some" old.

Section test.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["WellFormedOptCmd_Some"]) ().
  Goal forall pc c (P : _ -> Prop), P (WellFormedOptCmd pc (Some c)).
  Proof. move=> *. cook. Abort.
End test.

Notation "pc ⊢ ocmd" := (WellFormedOptCmd pc ocmd) (at level 20).


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

  Fact compute_new_pc_opt_some pc cmd :
    ltac2:(cbn_eq (compute_new_pc_opt pc (Some cmd))).
  Proof. done. Qed.

  Lemma compute_new_pc_secret untr c :
    public (compute_new_pc (mk_4ptlbl untr false) c) = false.
  Proof. case: c=> // - []  *; rewrite pub_join //.  Qed.

  Fact compute_new_pc_opt_secret untr c :
    public (compute_new_pc_opt (mk_4ptlbl untr false) c) = false.
  Proof.
    rewrite /compute_new_pc_opt.
    case: c => [c | ] //.
    rewrite compute_new_pc_secret //.
  Qed.
End new_pc.

Ltac2 Set this_cookbook_ as old :=  add_cookstep ltac1:(rewrite -> compute_new_pc_opt_some) "compute_new_pc_opt_some" old.
Ltac2 Set this_cookbook_ as old :=  add_cookstep ltac1:(rewrite -> compute_new_pc_opt_secret) "compute_new_pc_opt_secret" old.

Section test.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["compute_new_pc_opt_some"]) ().
  Goal forall pc c (P: _ -> Prop), P (compute_new_pc_opt pc (Some c)). 
  Proof. move=> *. cook. Abort.
End test.

Section test.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["compute_new_pc_opt_secret"]) ().
  Goal forall untr c (P: _ -> Prop), P (public (compute_new_pc_opt (mk_4ptlbl untr false) c)).
  Proof. move=> *. cook. Abort.
End test.

Section flow_to_subtype.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Lemma flows_to_subtype_cmd c l1 l2:
      l2 ⊑ l1 -> (* TODO: I don't know whether this is true *)
      WellFormedCmd l1 c ->
      WellFormedCmd l2 c.
  Proof.
    move=> Hl2 H; move: l2 Hl2; elim: H.
    - move=> from to Hfrom Hto l2 /flows_to_pt ->. exact: (wf_endorse _ _ Hfrom Hto).
    - move=> from to Hfrom Hto l2 /flows_to_pt ->. exact: (wf_declassify _ _ Hfrom Hto).
    - move=> dst src1 src2 comp pclbl Hs1 Hs2 Hpc l2 Hl2.
      apply: wf_assign; [exact: Hs1 | exact: Hs2 | exact: (flows_to_trans _ _ _ Hl2 Hpc)].
    - move=> gvar comp pclbl b1 b2 _ IH1 _ IH2 l2 Hl2. apply: wf_cond.
      + move: IH1; apply/Forall_impl => co Hco. exact: (Hco _ (join_mono_r _ _ _ Hl2)).
      + move: IH2; apply/Forall_impl => co Hco. exact: (Hco _ (join_mono_r _ _ _ Hl2)).
    - move=> gvar comp pclbl wbody _ IH l2 Hl2. apply: wf_while.
      + move: IH; apply/Forall_impl => co Hco. exact: (Hco _ (join_mono_r _ _ _ Hl2)).
    - move=> from to pclbl Hfrom Hpc l2 Hl2.
      apply: wf_endorse_safe; [exact: Hfrom | exact: (flows_to_trans _ _ _ Hl2 Hpc)].
    - move=> from to pclbl Hfrom Hpc l2 Hl2.
      apply: wf_declassify_safe; [exact: Hfrom | exact: (flows_to_trans _ _ _ Hl2 Hpc)].
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
End flow_to_subtype.

Section downgrading.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  (* An endorse is now typed either by the real rule (canonical PU→PT, pc=PT) or
     by the harmless rule (ordinary assignment flow). Inversion gives the
     disjunction. *)
  Lemma wf_endorse_inv pc from to:
    WellFormedCmd pc (assign (endorse from to)) ->
    (pc = mk_4ptlbl false true /\
     var_lbl from = mk_4ptlbl true true /\
     var_lbl to = mk_4ptlbl false true)
    \/ (var_lbl from ⊑ var_lbl to /\ pc ⊑ var_lbl to).
  Proof. inversion 1; subst; tauto. Qed.

  Lemma wf_declassify_inv pc from to:
    WellFormedCmd pc (assign (declassify from to)) ->
    (pc = mk_4ptlbl false true /\
     var_lbl from = mk_4ptlbl false false /\
     var_lbl to = mk_4ptlbl false true)
    \/ (var_lbl from ⊑ var_lbl to /\ pc ⊑ var_lbl to).
  Proof. inversion 1; subst; tauto. Qed.
End downgrading.

Section ni.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Lemma ni_cmd_st_conf c l st1 st2:
      WellFormedCmd l c ->
      ~~ is_declassify c ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof.
    move=> H; case: H.
    - (* endorse (canonical PU→PT) *)
      move=> from to Hfrom _ _ peq /=.
      apply: update_to_store_storeview_eq; [rewrite /is_public Hfrom // | exact: peq].
    - (* declassify : excluded by ~~ is_declassify *)
      move=> from to _ _ Hd _; discriminate Hd.
    - (* assign *)
      move=> dst src1 src2 comp pclbl Hs1 Hs2 _ _ peq /=.
      case dp: ([elaborate is_public dst]); [| rewrite !update_storeview_nochange //].
      move: (flows_to_pub _ _ dp Hs1)=> ps1.
      move: (flows_to_pub _ _ dp Hs2)=> ps2.
      set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
      set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
      suff: v1 = v2; [move=> ->; apply/update_same_varval; exact: peq | subst v1 v2].
      rewrite /get_assign_val /eval_val_exp /=.
      f_equal; eauto using storeview_eq.
    - (* cond *) move=> gvar comp pclbl b1 b2 _ _ _ peq /=; exact: peq.
    - (* while *) move=> gvar comp pclbl wbody _ _ peq /=; exact: peq.
    - (* endorse_safe (harmless: from ⊑ to) *)
      move=> from to pclbl Hft _ _ peq /=.
      rewrite /clean_assign_stp_store /get_assign_dest /get_assign_val /=.
      case dp: ([elaborate is_public to]); [| rewrite !update_storeview_nochange //].
      apply: update_to_store_storeview_eq; [exact: (flows_to_pub _ _ dp Hft) | exact: peq].
    - (* declassify_safe : excluded by ~~ is_declassify *)
      move=> from to pclbl _ _ Hd _; discriminate Hd.
  Qed.

  Lemma ni_cmd_st_conf_atk {AtkStates} (adv : AdvNextStep AtkStates)
    ast l c s1 s2 :
    WellFormedCmd l c ->
    ~~ is_declassify c ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (clean_cmd_stp_store c (pre_cmd_action adv ast s1)) =
    post_cmd_action adv ast (clean_cmd_stp_store c (pre_cmd_action adv ast s2)).
  Proof.
    move=> *.
    apply: post_cmd_wf.
    apply: ni_cmd_st_conf=> //; [eassumption|].
    apply: pre_cmd_wf_conf=> //.
  Qed.

  (* ni_cmd_st_conf_atk with an option-Cmd store-step. *)
  Lemma ni_optcmd_st_conf_atk {AtkStates} (adv : AdvNextStep AtkStates)
    ast l oc s1 s2 :
    l ⊢ oc ->
    ~~ oapp is_declassify false oc ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s1)) =
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s2)).
  Proof.
    move=> wt nodecl ?.
    apply: post_cmd_wf.
    case: oc wt nodecl => [c | ] wt /= ?.
    - apply: (ni_cmd_st_conf _ _ _ _ wt)=> //. apply: pre_cmd_wf_conf=> //.
    - apply: pre_cmd_wf_conf=> //.
  Qed.

  (* In a secret context, the public view is constant *)
  Lemma ni_sec_cmd_st_conf:
    forall c i st,
      WellFormedCmd (mk_4ptlbl i false) c ->
      ⟨ clean_cmd_stp_store c st | is_public ⟩ =
      ⟨ st | is_public ⟩.
  Proof.
    move=> c i st H.
    move E: (mk_4ptlbl i false) H => p H.
    move: E; case: H => //=.
    - (* assign *) move=> dst src1 src2 comp pclbl _ _ Hpc E.
      have Hsec : is_public dst = false.
      { rewrite /is_public; apply/negbTE; apply: (flows_from_sec pclbl _ _ Hpc).
        rewrite -E /secret /= //. }
      rewrite /clean_assign_stp_store /get_assign_dest /= update_storeview_nochange //.
    - (* endorse_safe *) move=> from to pclbl _ Hpc E.
      have Hsec : is_public to = false.
      { rewrite /is_public; apply/negbTE; apply: (flows_from_sec pclbl _ _ Hpc).
        rewrite -E /secret /= //. }
      rewrite /clean_assign_stp_store /get_assign_dest /= update_storeview_nochange //.
    - (* declassify_safe *) move=> from to pclbl _ Hpc E.
      have Hsec : is_public to = false.
      { rewrite /is_public; apply/negbTE; apply: (flows_from_sec pclbl _ _ Hpc).
        rewrite -E /secret /= //. }
      rewrite /clean_assign_stp_store /get_assign_dest /= update_storeview_nochange //.
  Qed.

  (* In a secret context the command's store-step is invisible to post:
     it can only move secret state, and post_cmd_action sees only the
     public view. So `optcmd_stp_store oc` drops out entirely. *)
  Lemma ni_sec_optcmd_st_conf_atk {AtkStates} (adv : AdvNextStep AtkStates)
    ast i oc s :
    mk_4ptlbl i false ⊢ oc ->
    post_cmd_action adv ast (optcmd_stp_store oc s) =
    post_cmd_action adv ast s.
  Proof.
    case: oc => [? | ] ? //.
    apply/post_cmd_wf /ni_sec_cmd_st_conf. eassumption.
  Qed.

  Lemma ni_cmd_st_int c l st1 st2:
      WellFormedCmd l c ->
      ~~ is_endorse c ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof.
    move=> H; case: H.
    - (* endorse : excluded by ~~ is_endorse *)
      move=> from to _ _ He _; discriminate He.
    - (* declassify (canonical ST→PT) *)
      move=> from to Hfrom _ _ treq /=.
      apply: update_to_store_storeview_eq; [rewrite /is_trusted /is_untrusted Hfrom // | exact: treq].
    - (* assign *)
      move=> dst src1 src2 comp pclbl Hs1 Hs2 _ _ treq /=.
      case dt: ([elaborate is_trusted dst]); [| rewrite !update_storeview_nochange //].
      move: (flows_to_tr _ _ dt Hs1)=> ts1.
      move: (flows_to_tr _ _ dt Hs2)=> ts2.
      set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
      set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
      suff: v1 = v2; [move=> ->; apply/update_same_varval; exact: treq | subst v1 v2].
      rewrite /get_assign_val /eval_val_exp /=.
      f_equal; eauto using storeview_eq.
    - (* cond *) move=> gvar comp pclbl b1 b2 _ _ _ treq /=; exact: treq.
    - (* while *) move=> gvar comp pclbl wbody _ _ treq /=; exact: treq.
    - (* endorse_safe : excluded by ~~ is_endorse *)
      move=> from to pclbl _ _ He _; discriminate He.
    - (* declassify_safe (harmless: from ⊑ to) *)
      move=> from to pclbl Hft _ _ treq /=.
      rewrite /clean_assign_stp_store /get_assign_dest /get_assign_val /=.
      case dt: ([elaborate is_trusted to]); [| rewrite !update_storeview_nochange //].
      apply: update_to_store_storeview_eq; [exact: (flows_to_tr _ _ dt Hft) | exact: treq].
  Qed.

  Lemma ni_untr_cmd_st_int:
    forall p c st,
    WellFormedCmd (mk_4ptlbl true p) c ->
    ⟨ clean_cmd_stp_store c st | is_trusted ⟩ =
    ⟨ st | is_trusted ⟩.
  Proof.
    move=> p c st H.
    move E: (mk_4ptlbl true p) H => l H.
    move: E; case: H => //=.
    - (* assign *) move=> dst src1 src2 comp pclbl _ _ Hpc E.
      have Hut : is_trusted dst = false.
      { have Hu : is_untrusted dst.
        { rewrite /is_untrusted; apply: (flows_from_untr pclbl _ _ Hpc); rewrite -E /= //. }
        rewrite /is_trusted Hu //. }
      rewrite /clean_assign_stp_store /get_assign_dest /= update_storeview_nochange //.
    - (* endorse_safe *) move=> from to pclbl _ Hpc E.
      have Hut : is_trusted to = false.
      { have Hu : is_untrusted to.
        { rewrite /is_untrusted; apply: (flows_from_untr pclbl _ _ Hpc); rewrite -E /= //. }
        rewrite /is_trusted Hu //. }
      rewrite /clean_assign_stp_store /get_assign_dest /= update_storeview_nochange //.
    - (* declassify_safe *) move=> from to pclbl _ Hpc E.
      have Hut : is_trusted to = false.
      { have Hu : is_untrusted to.
        { rewrite /is_untrusted; apply: (flows_from_untr pclbl _ _ Hpc); rewrite -E /= //. }
        rewrite /is_trusted Hu //. }
      rewrite /clean_assign_stp_store /get_assign_dest /= update_storeview_nochange //.
  Qed.

  Lemma ni_tr_cmd_cnt:
    forall p c st1 st2,
      let: lbl := mk_4ptlbl false p in
      let: new_lbl := (compute_new_pc lbl c) in
      WellFormedCmd lbl c ->
      untrusted new_lbl = false ->
        ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
        clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof.
    move=> >. move e: (mk_4ptlbl _ _)=> l; move: e=> /[swap].
    case=> //= > => [_ _| _] <- untrg *.
    1-2: set gr := (X in _ = (if X then _ else _)); set gl := (X in (if X then _ else _) = _).
    1-2: suff: gl = gr; [move=> -> //|subst gl gr]; congr (_ _).
    1-2: apply/storeview_eq; [eassumption|].
    1-2: move: untrg; rewrite Bool.orb_false_r /is_trusted/is_untrusted=> -> //.
  Qed.
End ni.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(erewrite ni_untr_cmd_st_int;[..|eassumption]) "ni_untr_cmd_st_int" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(erewrite ni_sec_cmd_st_conf;[..|eassumption]) "ni_sec_cmd_st_conf" old.

(*
Ltac2 Set this_cookbook_ as old := (* Maybe this should be unshelve erewrite also *)
  add_cookstep ltac1:(erewrite ni_cmd_st_int; only 2-4: eassumption)  "ni_cmd_st_int" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(erewrite ni_cmd_st_conf; only 2-4: eassumption) "ni_cmd_st_conf" old.
  *)

Ltac2 Set this_cookbook_ as old := (* Maybe this should be unshelve erewrite also *)
  add_cookstep ltac1:(apply/ni_cmd_st_int; [eassumption| assumption|])  "ni_cmd_st_int" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(apply/ni_cmd_st_conf; [eassumption| assumption|]) "ni_cmd_st_conf" old.

Section test.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["ni_cmd_st_conf"]) ().
  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->    ~~ is_declassify c ->
    ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof. move=> *. cook. Abort.
End test.

Section test.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["ni_cmd_st_int"]) ().
  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->    ~~ is_endorse c ->
    ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof. move=> *. cook. Abort.
End test.

Section test.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["ni_sec_cmd_st_conf"]) ().
  Goal forall i c st1 (P : _ -> Prop), WellFormedCmd (mk_4ptlbl i false) c ->
    P ⟨ clean_cmd_stp_store c st1 | is_public ⟩.
  Proof. move=> *. cook. Abort.
End test.

Section test.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["ni_untr_cmd_st_int"]) ().
  Goal forall p c st1 (P : _ -> Prop), WellFormedCmd (mk_4ptlbl true p) c ->
    P ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩.
  Proof. move=> *. cook. Abort.
End test.

Section step_soundness.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Lemma compute_new_pc_untr p c:
    exists p',
      compute_new_pc (mk_4ptlbl true p) c = (mk_4ptlbl true p').
  Proof.
  case: c; eauto; cbn; case=> *.
    1-2: case: (var_lbl _) => u pg. (* TODO: This could be a lemma *)
    1-2: exists (pg && p); case: u; done.
  Qed.

 Fact untr_compute_new_pc p c:
   untrusted (compute_new_pc (mk_4ptlbl true p) c).
 Proof.
   case: c=> //=; case=> * ; rewrite untr_join //.
 Qed.

  Lemma step_soundness c pc:
      WellFormedCmd pc c ->
      forall st,
        WellFormedProg (compute_new_pc pc c) (clean_cmd_stp_cnt c st).
  Proof.
    move=> + > => - []=> * //=.
    1-2: move: (X in if X then _ else _)=> ?; if_easy_goals.
    apply/Forall_app. split=> //.
    constructor 2=> //.
    apply/wf_while /Forall_impl; [| eassumption]; clear=> *.
    rewrite -join_assoc join_idem=> //.
  Qed.

  Lemma step_soundness_pubuntr:
    forall c st,
      WellFormedCmd (mk_4ptlbl true true) c ->
      WellFormedProg (mk_4ptlbl true true) (clean_cmd_stp_cnt c st).
  Proof.
    rewrite/WellFormedProg=> >;  move l: (mk_4ptlbl _ _)=> ?; move: l=> /[swap].
    case=> //= >; rewrite  -!/(WellFormedProg _ _)=>>.
    1: move=> ++ e; rewrite -{}e => *.
    2: move=> + e; rewrite -{}e => *.
    1-2: case: (X in if X then _ else _) => //. (* all is antipattern *)
    3: apply/Forall_app; split;[|repeat constructor=>//];
        rewrite -/(WellFormedProg _ _).
    1-3: apply/flows_to_subtype_prog;[|eassumption].
    1-3: case: (var_lbl)=> [[] []]=> //. (* TODO: This should be lemma *)
  Qed.
End step_soundness.


(* TODO: rewrite -> vs rewrite  *)
Ltac2 Set this_cookbook_ as old :=  add_cookstep  ltac1:(rewrite -> untr_compute_new_pc) "untr_compute_new_pc" old.

Section test.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac2 Set curr_cookbook := fun () => (keep_only this_cookbook_ ["untr_compute_new_pc"]) ().
  Goal forall p c (P : _ -> Prop), P (untrusted (compute_new_pc (mk_4ptlbl true p) c)).
  Proof. move=> *. cook. Abort.
End test.


Ltac2 this_cookbook () := this_cookbook_ ().
