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
       let: ptlbl := mk_lbl false true in let: pulbl := mk_lbl true true in
       var_lbl from = pulbl -> var_lbl to = ptlbl ->
       _ ptlbl (endorse from to) 

  | wf_declassify: 
     forall from to,
       let: ptlbl := mk_lbl false true in let: stlbl := mk_lbl false false in
       var_lbl from = stlbl -> var_lbl to = ptlbl ->
       _ ptlbl (declassify from to)

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

    (* 
       However, do we even need induction? Maybe we don't need it at all.. 
       So, can we do something weaker than inductively defining this then?
    *)
    Hypothesis hyp_endorse : 
        forall from to,
          let: ptlbl := mk_lbl false true in let: pulbl := mk_lbl true true in
          var_lbl from = pulbl -> var_lbl to = ptlbl ->
          P ptlbl (endorse from to). 

    Hypothesis hyp_declassify : 
        forall from to,
          let: ptlbl := mk_lbl false true in let: stlbl := mk_lbl false false in
          var_lbl from = stlbl -> var_lbl to = ptlbl ->
          P ptlbl (declassify from to).

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
      move=> > []; [apply:hyp_endorse|apply:hyp_declassify|apply:hyp_assign|..]=> *.
      1-2: (apply: hyp_cond; clear hyp_cond) || (apply: hyp_while; clear hyp_while)=>//.
      1-3: lazymatch goal with
             H: Forall _ ?b |- Forall _ ?b => elim: H=> // *
            end.
      1-3: constructor 2=> //; auto.
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
    public (compute_new_pc (mk_lbl untr false) c) = false.
  Proof. case: c=> // - []  *; rewrite pub_join //.  Qed.

  Fact compute_new_pc_opt_secret untr c :
    public (compute_new_pc_opt (mk_lbl untr false) c) = false.
  Proof.
    rewrite /compute_new_pc_opt.
    case: c => [c | ] //.
    rewrite compute_new_pc_secret //.
  Qed.
End new_pc.

Ltac2 Set this_cookbook_ as old :=  add_cookstep ltac1:(rewrite -> compute_new_pc_opt_some) "compute_new_pc_opt_some" old.
Ltac2 Set this_cookbook_ as old :=  add_cookstep ltac1:(rewrite -> compute_new_pc_opt_secret) "compute_new_pc_opt_secret" old.

Section flow_to_subtype.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Lemma flows_to_subtype_cmd c l1 l2:
      l2 ⊑ l1 -> (* TODO: I don't know whether this is true *)
      WellFormedCmd l1 c ->
      WellFormedCmd l2 c.
  Proof. 
    (* TODO: What does elim do? Is it just apply? *)  
    move: l2=> ++ h. elim: h=> *; [| |constructor=> //; eauto using flows_to_trans|..].
    1-2: revert_hyp_pat  (is_true (_ ⊑ _))=> /flows_to_pt ->; constructor=> //.
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
End flow_to_subtype.

Section ni.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Lemma ni_cmd_st_conf c l st1 st2:
      WellFormedCmd l c ->
      ~~ is_declassify c ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof.
    move=> [] // d s1 s2 ? ?.
      { apply: update_to_store_storeview_eq. rewrite /is_public s2 //. }
    case de: ([elaborate is_public d])=> fs1d fs2d _ _ pubeq /=; [| rewrite !update_storeview_nochange //].
    move: (flows_to_pub _ _ de fs1d)=> {fs1d} ps1. (* TODO: Tactic *)
    move: (flows_to_pub _ _ de fs2d)=> {fs2d} ps2.
    set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
    set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
    suff: v1 = v2; [move=> ->; apply/update_same_varval=> //|subst v1 v2].
    f_equal; eauto using storeview_eq.
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

  (* In a secret context the command's store-step is invisible to post:
     it can only move secret state, and post_cmd_action sees only the
     public view. So `optcmd_stp_store oc` drops out entirely. *)
  Lemma ni_sec_optcmd_st_conf_atk {AtkStates} (adv : AdvNextStep AtkStates)
    ast i oc s :
    mk_lbl i false ⊢ oc ->
    post_cmd_action adv ast (optcmd_stp_store oc s) =
    post_cmd_action adv ast s.
  Proof.
    case: oc => [? | ] ? //.
    apply/post_cmd_wf /ni_sec_cmd_st_conf. eassumption.
  Qed.

  Lemma ni_cmd_st_int c l st1 st2:
      WellFormedCmd l c ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof.
    move=> [] // d s1 s2 ? ?.
    1-2: admit.
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
  Admitted.

  Lemma ni_untr_cmd_st_int:
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

  Lemma ni_tr_cmd_cnt:
    forall p c st1 st2,
      let: lbl := mk_lbl false p in
      let: new_lbl := (compute_new_pc lbl c) in
      WellFormedCmd lbl c ->
      untrusted new_lbl = false ->
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
End ni.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(unshelve erewrite ni_untr_cmd_st_int;[..|eassumption]) "ni_untr_cmd_st_int" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(unshelve erewrite ni_sec_cmd_st_conf;[..|eassumption]) "ni_sec_cmd_st_conf" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(apply/ni_cmd_st_int; [eassumption|])  "ni_cmd_st_int" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(apply/ni_cmd_st_conf; [eassumption|]) "ni_cmd_st_conf" old.

Section step_soundness.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Lemma compute_new_pc_untr p c:
    exists p',
      compute_new_pc (mk_lbl true p) c = (mk_lbl true p').
  Proof.
  case: c; eauto; cbn; case=> *.
    1-2: case: (var_lbl _) => u pg. (* TODO: This could be a lemma *)
    1-2: exists (pg && p); case: u; done.
  Qed.

 Fact untr_compute_new_pc p c:
   untrusted (compute_new_pc (mk_lbl true p) c).
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
    constructor 5. apply/Forall_impl; [| eassumption]; clear=> *.
    rewrite -join_assoc join_idem=> //.
  Qed.

  Lemma step_soundness_pubuntr:
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
End step_soundness.


(* TODO: rewrite -> vs rewrite  *)
Ltac2 Set this_cookbook_ as old :=  add_cookstep  ltac1:(rewrite -> untr_compute_new_pc) "untr_compute_new_pc" old.


Ltac2 this_cookbook () := this_cookbook_ ().
