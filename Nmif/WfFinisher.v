From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section ni.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Lemma wf_cmd_st_conf_ni c l st1 st2:
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
    rewrite /get_assign_val /eval_val_exp /=.
    f_equal; eauto using storeview_eq.
  Qed.

  
  (* In a secret context, the public view is constant *)
  Lemma wf_sec_cmd_st_conf_ni:
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

  Lemma wf_cmd_st_int_ni c l st1 st2:
      WellFormedCmd l c ->
      ~~ is_endorse c ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof.
    move=> [] // d s1 s2 ? ?.
      { apply: update_to_store_storeview_eq. rewrite /is_trusted /is_untrusted s2 //. } (* declassify *)
    case de: ([elaborate is_untrusted d])=> fs1d fs2d _ _ treq /=;
      [do 2 (rewrite update_storeview_nochange{1}/is_trusted; [rewrite de //|])=> //|].
    rewrite/is_trusted/is_untrusted/= in de.
    move: de=>/untrusted_false td. (* TODO: Automation *)
    move: (flows_to_tr _ _ td fs1d)=> {fs1d} ts1. (* TODO: Tactic *)
    move: (flows_to_tr _ _ td fs2d)=> {fs2d} ts2.
    set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
    set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
    suff: v1 = v2; [move=> ->; apply/update_same_varval=> //|subst v1 v2].
    rewrite /get_assign_val /eval_val_exp /=.
    f_equal; eauto using storeview_eq.
  Qed.


  Fact wf_optcmd_st_conf_ni l oc st1 st2:
      l ⊢ oc ->
      ~~ oapp is_declassify false oc ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ optcmd_stp_store oc st1 | is_public ⟩ = ⟨ optcmd_stp_store oc st2 | is_public ⟩.
  Proof.
    case: oc => //= c wf nodecl pubeq.
    exact: wf_cmd_st_conf_ni wf nodecl pubeq.
  Qed.

  Fact wf_sec_optcmd_st_conf_ni i oc s:
    mk_lbl i false ⊢ oc ->
    ⟨ optcmd_stp_store oc s | is_public ⟩ = ⟨ s | is_public ⟩.
  Proof. case: oc => //= c wf. exact: wf_sec_cmd_st_conf_ni wf. Qed.

  Lemma wf_untr_cmd_st_int_ni:
    forall p c st,
    WellFormedCmd (mk_lbl true p) c ->
    ⟨ clean_cmd_stp_store c st | is_trusted ⟩ = ⟨ st | is_trusted ⟩.
  Proof.
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap].
    case=> //= > +++e; rewrite -{}e=> _ _ flw.
    rewrite update_storeview_nochange=> //.
    rewrite/is_trusted/is_untrusted negbF //.
    apply/flows_from_untr; eauto; done.
  Qed.

  Fact wf_untr_optcmd_st_int_ni p oc s:
    mk_lbl true p ⊢ oc ->
    ⟨ optcmd_stp_store oc s | is_trusted ⟩ = ⟨ s | is_trusted ⟩.
  Proof. case: oc => //= c wf. exact: wf_untr_cmd_st_int_ni wf. Qed.

  Lemma wf_tr_cmd_cnt_ni:
    forall p p' c st1 st2,
      WellFormedCmd (mk_lbl false p) c ->
      compute_new_pc (mk_lbl false p) c = mk_lbl false p' ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof.
    move=> p p' c st1 st2 wf hyp treq.
    have untrg: untrusted (compute_new_pc (mk_lbl false p) c) = false by rewrite hyp.
    move: wf untrg treq.
    move e: (mk_lbl _ _)=> l; move: e=> /[swap].
    case=> //= > => [_ _| _] <- untrg *.
    1-2: set gr := (X in _ = (if X then _ else _)); set gl := (X in (if X then _ else _) = _).
    1-2: suff: gl = gr; [move=> -> //|subst gl gr]; congr (_ _).
    1-2: apply/storeview_eq; [eassumption|].
    1-2: move: untrg; rewrite Bool.orb_false_r /is_trusted/is_untrusted=> -> //.
  Qed.

  Lemma wf_untr_cmd_evnt_ni pc c s:
    untrusted pc -> WellFormedCmd pc c -> clean_cmd_evnt c s = None.
  Proof.
    move=> /[swap]. case=> // > _ _ /[swap].
    rewrite/clean_cmd_evnt/clean_assign_evnt/get_assign_dest=> *.
    pattern_eq [is_trusted _] with false=> [|-> //].
    rewrite/is_trusted/is_untrusted.
    erewrite flows_from_untr; eauto.
  Qed.

  Fact wf_untr_optcmd_evnt_ni pc oc s:
    untrusted pc -> pc ⊢ oc -> optcmd_evnt oc s = None.
  Proof. case: oc=> //= c untr wf.   eauto using wf_untr_cmd_evnt_ni. Qed.

  Lemma wf_cmd_evnt_int_ni c l st1 st2:
      WellFormedCmd l c ->
      ~~ is_endorse c ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      clean_cmd_evnt c st1 = clean_cmd_evnt c st2.
  Proof.
    move=> wf noend treq.
    case: wf noend => //=.
    - move=> from to e1 e2 _.
      rewrite /clean_cmd_evnt /clean_assign_evnt /get_assign_dest /get_assign_val /=.
      have ->: is_trusted to.
      { rewrite /is_trusted /is_untrusted e2 //. }
      have ->: st1 from = st2 from.
      { apply: storeview_eq; [exact: treq | rewrite /is_trusted /is_untrusted e1 // ]. }
      done.
    - move=> dst src1 src2 comp pclbl fs1 fs2 _ _.
      rewrite /clean_cmd_evnt /clean_assign_evnt /get_assign_dest /get_assign_val /eval_val_exp /=.
      case te: (is_trusted dst)=> //.
      have ->: st1 src1 = st2 src1.
      { apply: storeview_eq; [exact: treq | exact: flows_to_tr te fs1 ]. }
      have ->: st1 src2 = st2 src2.
      { apply: storeview_eq; [exact: treq | exact: flows_to_tr te fs2 ]. }
      done.
  Qed.

  Fact wf_optcmd_evnt_int_ni l oc st1 st2:
      l ⊢ oc ->
      ~~ oapp is_endorse false oc ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      optcmd_evnt oc st1 = optcmd_evnt oc st2.
  Proof.
    case: oc => //= c wf noend treq.
    exact: wf_cmd_evnt_int_ni wf noend treq.
  Qed.

  Lemma wf_cmd_st_end c l st1 st2:
      WellFormedCmd l c ->
      is_endorse c ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof.
    move=> wf isend pubeq.
    case: wf isend => //= from to e1 e2 _.
    rewrite /clean_cmd_stp_store /get_assign_dest /get_assign_val /=.
    apply: update_to_store_storeview_eq; [rewrite /is_public e1 // | exact: pubeq].
  Qed.

  Lemma wf_cmd_evnt_end c l st1 st2:
      WellFormedCmd l c ->
      is_endorse c ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      clean_cmd_evnt c st1 = clean_cmd_evnt c st2.
  Proof.
    move=> wf isend pubeq.
    case: wf isend => //= from to e1 e2 _.
    rewrite /clean_cmd_evnt /clean_assign_evnt /get_assign_dest /get_assign_val /=.
    have ->: is_trusted to.
    { rewrite /is_trusted /is_untrusted e2 //. }
    have ->: st1 from = st2 from.
    { apply: storeview_eq; [exact: pubeq | rewrite /is_public e1 // ]. }
    done.
  Qed.

  Fact wf_optcmd_evnt_end l oc st1 st2:
      l ⊢ oc ->
      oapp is_endorse false oc ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      optcmd_evnt oc st1 = optcmd_evnt oc st2.
  Proof.
    case: oc => //= c wf isend pubeq.
    exact: wf_cmd_evnt_end wf isend pubeq.
  Qed.

  Lemma wf_cmd_evnt_decl c l st1 st2:
      WellFormedCmd l c ->
      is_declassify c ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      clean_cmd_evnt c st1 = clean_cmd_evnt c st2.
  Proof.
    move=> wf isdecl treq.
    case: wf isdecl => //= from to e1 e2 _.
    rewrite /clean_cmd_evnt /clean_assign_evnt /get_assign_dest /get_assign_val /=.
    have ->: is_trusted to.
    { rewrite /is_trusted /is_untrusted e2 //. }
    have ->: st1 from = st2 from.
    { apply: storeview_eq; [exact: treq | rewrite /is_trusted /is_untrusted e1 // ]. }
    done.
  Qed.

  Fact wf_optcmd_evnt_decl l oc st1 st2:
      l ⊢ oc ->
      oapp is_declassify false oc ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      optcmd_evnt oc st1 = optcmd_evnt oc st2.
  Proof.
    case: oc => //= c wf isdecl treq.
    exact: wf_cmd_evnt_decl wf isdecl treq.
  Qed.

End ni.

(* TODO: Eventually, we should have a pattern that let's us not have these versions for optional cmd and so on *)
Ltac wf_finisher_arms :=
    (apply: wf_cmd_st_conf_ni
   + apply: wf_optcmd_st_conf_ni
   + apply: wf_sec_cmd_st_conf_ni
   + apply: wf_sec_optcmd_st_conf_ni
   + apply: wf_cmd_st_int_ni
   + apply: wf_untr_cmd_st_int_ni
   + apply: wf_untr_optcmd_st_int_ni
   + apply: wf_tr_cmd_cnt_ni
   + apply: wf_untr_cmd_evnt_ni
   + apply: wf_untr_optcmd_evnt_ni
   + apply: wf_cmd_evnt_int_ni
   + apply: wf_optcmd_evnt_int_ni
   + apply: wf_cmd_evnt_end
   + apply: wf_optcmd_evnt_end
   + apply: wf_cmd_evnt_decl
   + apply: wf_optcmd_evnt_decl
   + apply: pre_cmd_wf_int
   + apply: pre_cmd_wf_conf
   + apply: post_cmd_wf).

Ltac wf_finisher_close := 
  lazymatch goal with
  |- ?G => 
    tryif has_evar G then 
      first [eassumption | symmetry; eassumption] else
      first [assumption | reflexivity]
  end; enter (throw). (* Should never come here. TODO: Message *)

(* TODO: We don't need n I think *)
Ltac wf_finisher_rec n :=
  lazymatch n with
  | 0 => throw (* We really don't want to recurse so much*)
  | S ?m =>
    first [
      wf_finisher_close |
      lazymatch goal with |- _ = _ => idtac | |- _ => fail end; 
        (idtac + symmetry);
        wf_finisher_arms; 
        wf_finisher_rec m]
  end.

Ltac wf_finisher :=
  harden 0 (wf_finisher_rec 5).

Ltac2 wf_finisher_guess_aux (pat : Ltac1.t) (u : preterm) : unit :=
  let wf_partial_tac := ltac1:(p v |- pattern_eq [p] with v) pat in
  let acc : constr list ref := { contents := [] } in
  match Control.case (fun () =>
    let v := Constr.Pretype.pretype Constr.Pretype.Flags.open_constr_flags_with_tc Constr.Pretype.expected_without_type_constraint u in
    wf_partial_tac (Ltac1.of_constr v);
    Control.focus 1 1 (fun () =>
      ltac1:(wf_finisher);
      acc.(contents) := clone_constr v :: acc.(contents);
      Control.zero (Tactic_failure None))
  ) with
  | Val _ => panic_s "wf_finisher_guess" "unreachable: probe loop must Control.zero"
  | Err _ =>
    let dedup := List.fold_right (fun c acc =>
      if List.exist (Constr.equal c) acc then acc else c :: acc) (acc.(contents)) [] in
    match dedup with
    | [v_single] =>
       wf_partial_tac (Ltac1.of_constr v_single); 
       Control.focus 1 1 (fun () => ltac1:(wf_finisher))
    | _ =>
      Message.print (Message.of_string "Guess list");
      List.iter (fun c => Message.print (Message.of_constr c)) dedup;
      panic_s "wf_finisher_guess" "ambiguous (or no) guess"
    end
  end.

Tactic Notation "wf_finisher_guess" "[" ssrpatternarg(p) "]" "with" uconstr(u) :=
  let f := ltac2:(p u |- wf_finisher_guess_aux p (Option.get (Ltac1.to_preterm u))) in
  f p u.



Goal 5 = 5. wf_finisher.  Abort.  (* TODO!!!  assert_fails also succeeds!!  WHAT *)

Section test.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->    ~~ is_declassify c ->
    ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st2 | is_public ⟩ = ⟨ st1 | is_public ⟩ ->    ~~ is_declassify c ->
    ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->    ~~ is_endorse c ->
    ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall i c st, WellFormedCmd (mk_lbl i false) c ->
    ⟨ clean_cmd_stp_store c st | is_public ⟩ = ⟨ st | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall p c st, WellFormedCmd (mk_lbl true p) c ->
    ⟨ clean_cmd_stp_store c st | is_trusted ⟩ = ⟨ st | is_trusted ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast l c s1 s2,
    WellFormedCmd l c ->
    ~~ is_declassify c ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (clean_cmd_stp_store c (pre_cmd_action adv ast s1)) =
    post_cmd_action adv ast (clean_cmd_stp_store c (pre_cmd_action adv ast s2)).
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast l oc s1 s2,
    l ⊢ oc ->
    ~~ oapp is_declassify false oc ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s1)) =
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s2)).
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast i oc s,
    mk_lbl i false ⊢ oc ->
    post_cmd_action adv ast (optcmd_stp_store oc s) = post_cmd_action adv ast s.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast l c s1 s2,
    WellFormedCmd l c ->
    ~~ is_endorse c ->
    ⟨ s1 | is_trusted ⟩ = ⟨ s2 | is_trusted ⟩ ->
    ⟨ clean_cmd_stp_store c (pre_cmd_action adv ast s1) | is_trusted ⟩ =
    ⟨ clean_cmd_stp_store c s2 | is_trusted ⟩.
  Proof. 
    move=> *.
    unshelve (wf_finisher_guess [RHS] with ⟨ clean_cmd_stp_store _ _ | _ ⟩ => ->). 
    wf_finisher.
    Restart.
    move=> ????? st *.
    wf_finisher_guess [LHS] with ⟨ clean_cmd_stp_store _ st | _ ⟩ => ->. 
    wf_finisher. Qed.

  Goal forall p p' c st1 st2,
    WellFormedCmd (mk_lbl false p) c ->
    compute_new_pc (mk_lbl false p) c = mk_lbl false p' ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
    clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast p p' c s1 s2,
    WellFormedCmd (mk_lbl false p) c ->
    compute_new_pc (mk_lbl false p) c = mk_lbl false p' ->
    ⟨ s1 | is_trusted ⟩ = ⟨ s2 | is_trusted ⟩ ->
    clean_cmd_stp_cnt c (pre_cmd_action adv ast s1) = clean_cmd_stp_cnt c s2.
  Proof. move=> *. wf_finisher_guess [RHS] with _=> ->. wf_finisher. Qed.

  Goal forall pc c s, untrusted pc -> WellFormedCmd pc c -> clean_cmd_evnt c s = None.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall pc oc s, untrusted pc -> pc ⊢ oc -> optcmd_evnt oc s = None.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    ~~ is_endorse c ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
    clean_cmd_evnt c st1 = clean_cmd_evnt c st2.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l oc st1 st2, l ⊢ oc ->
    ~~ oapp is_endorse false oc ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
    optcmd_evnt oc st1 = optcmd_evnt oc st2.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    is_endorse c ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
    clean_cmd_evnt c st1 = clean_cmd_evnt c st2.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l oc st1 st2, l ⊢ oc ->
    oapp is_endorse false oc ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
    optcmd_evnt oc st1 = optcmd_evnt oc st2.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    is_declassify c ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
    clean_cmd_evnt c st1 = clean_cmd_evnt c st2.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l oc st1 st2, l ⊢ oc ->
    oapp is_declassify false oc ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
    optcmd_evnt oc st1 = optcmd_evnt oc st2.
  Proof. move=> *. wf_finisher. Qed.


  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s,
    ⟨ pre_cmd_action adv ast s | is_trusted ⟩ = ⟨ s | is_trusted ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s1 s2,
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    ⟨ pre_cmd_action adv ast s1 | is_public ⟩ = ⟨ pre_cmd_action adv ast s2 | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s1 s2,
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (pre_cmd_action adv ast s1) =
    post_cmd_action adv ast (pre_cmd_action adv ast s2).
  Proof. move=> *. wf_finisher. Qed.

(* A funny test *)
  Goal forall l oc st1 st2, l ⊢ oc ->
    oapp is_declassify false oc ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
    exists something, optcmd_evnt oc st1 = something.
  Proof. move=> *. eexists. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s1 s2,
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (pre_cmd_action adv ast s1) =
    post_cmd_action adv ast (pre_cmd_action adv ast s2).
  Proof. move=> *.
  wf_finisher_guess [post_cmd_action _ _ _] with _ => -> //.
  Qed.
End test.
