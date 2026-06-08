From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.


Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade WfFinisher Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!". 
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section sim_active.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Import Combined.

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

Section cmd_map.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Import Combined.

  Definition cmd_map (lst: list CmbCmd) : list (AtkCmd * AtkCmd) :=
    let: mapfn :=
      fun cmbcmd => (
        mk_atkcmd (real_atk_bit cmbcmd) (real_cmd cmbcmd),
        mk_atkcmd (sim_active cmbcmd) (ideal_cmd cmbcmd)) in
    map mapfn lst.

  Definition cmd_map_sim (lst: list CmbCmd) : list (option Cmd * bool) :=
    let: mapfn :=
      fun cmbcmd =>
        let: ocmd := if (public (pc_lbl cmbcmd)) is false then None else
                       (real_cmd cmbcmd) in
        (ocmd, real_atk_bit cmbcmd) in
    map mapfn (filter sim_active lst).

  Fact cmd_map_cons a l :
    ltac2:(cbn_eq (cmd_map (a :: l))). 
  Proof. done. Qed.

  Fact cmd_map_sim_cons a l :
    cmd_map_sim (a :: l) =
      if sim_active a
      then ((if public (pc_lbl a) is false then None else real_cmd a),
            real_atk_bit a) :: cmd_map_sim l
      else cmd_map_sim l.
  Proof. rewrite /cmd_map_sim /=. case: (sim_active a)=> //=. Qed.

  Fact cmd_map_app l1 l2 :
    cmd_map (l1 ++ l2) = cmd_map l1 ++ cmd_map l2.
  Proof. rewrite /cmd_map map_app. done. Qed.

  Lemma cmd_map_sim_app l1 l2 :
    cmd_map_sim (l1 ++ l2) = cmd_map_sim l1 ++ cmd_map_sim l2.
  Proof. rewrite /cmd_map_sim filter_app map_app. done. Qed.

End cmd_map.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> cmd_map_cons) "cmd_map_cons" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> cmd_map_app) "cmd_map_app" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> cmd_map_sim_cons ) "cmd_map_sim_cons" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> cmd_map_sim_app ) "cmd_map_sim_app" old.

Section extract.
  Import Combined Simulator.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.

  Notation CombCfg := (Combined.Cfg (AtkStates:= AtkStates)).
  Notation CfgTwo := (TwoCfg (AtkStates1:= AtkStates) (AtkStates2:= SimStates (AtkStates:=AtkStates))).

  Definition extract_2cfg (c: CombCfg): CfgTwo :=
    let: (mk_cmbstate rst ist simst atkst, cmblst) := c in
    let: cfg2prog := cmd_map cmblst in
    let: simprog := cmd_map_sim cmblst in
    (cfg2prog, (rst, atkst), (ist, mk_simstate atkst simst simprog)).
End extract.

Section extract_step_commute.
  Import TypeSystem Simulator.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable adv : (AdvNextStep AtkStates).

  Notation CombCfg := Combined.Cfg.
  Notation comb_step := (Combined.cfg_step adv).
  Notation comb_event := (Combined.cmb_event adv).
  Notation extract_2cfg := (extract_2cfg (AtkStates := AtkStates)).
  Notation step := (twostep adv (construct_simulator adv)).
  Notation two_event := (Semantics.twoevent adv (construct_simulator adv)).

  Import Util.List Combined VarValStore.Notations.


    (* TODO: cook rules in foreign cookbooks reference lemmas by unqualified
       name (e.g. `rewrite -> WellFormedOptCmd_Some in *`). Joining the
       cookbook is not enough — the importing file must also `Import` the
       module so the bare name resolves at fire time, otherwise the rewrite
       errors and `cook` silently drops the step. Figure out a cleaner fix. *)
  Ltac2 mutable curr_cookbook () := this_cookbook_ (). Ltac cook := ltac2:(cook curr_cookbook).
  Ltac2 Set curr_cookbook as old := join_cookbooks Combined.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Semantics.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks TypeSystem.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Attacker.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Util.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Util.List.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Lattice4pt.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks VarValStore.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Syntax.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks ControlledDowngrade.this_cookbook old.


  Ltac2 Set cook_debug := 0.

  Lemma extract_step_commute_downgrade (st: CmbState) (c: CmbCmd) (restcmd: list CmbCmd)
    (from to : Vars):
    oapp extract_controlled_endorse None (real_cmd c) = Some (from, to) \/
    oapp extract_controlled_declassify None (real_cmd c) = Some (from, to) ->
    Invariant (st, c :: restcmd) ->
    step (extract_2cfg (st, c :: restcmd)) = extract_2cfg (comb_step (st, c :: restcmd)).
  Proof.
    case: c=> >.  case: st=> >.
    cook. rewrite/Invariant=> downgrade. case. cook.
    rewrite/CmbCmdInv/StateInv=> + + [].
    case: downgrade=> /[dup] downgrade=> + [] + _.
    1,2: move=> /[swap] + /[swap] + /[swap] + /[swap].
    1: move: downgrade=> /extr_endorse_opt.
    2: move: downgrade=> /extr_decl_opt.
    1,2: move=> [->]; case=> /[dup] ? /[swap] /[dup] ? /[swap].
    1,2: rewrite/TypeInv=> + + [] /ltac:(dotop [cbn]).
    1: move=> /wf_endorse_pc. 2: move/wf_declassify_pc.
    1,2: move=> /[apply] /[apply] ->.
    1,2: dotop [cbn]=> <- _ ? ?. 
    1,2: rewrite/comb_step/cmbcmd_step/extract_2cfg; cook.
    1,2: pattern_eq [sim_active  _] with true=>[| ->]; [simpl; cook|].
    1,2: rewrite/step/acmd_step.
    1,2: move=> dgeqn.
    1,2: pattern_focus[pre_cmd_action (construct_simulator _) _ _ ]=> P. 
    1,2: rewrite/pre_cmd_action/construct_simulator/sim_pre; cook. 
    1,2: subst P; cbn beta.
    1,2: pattern_focus[post_cmd_action (construct_simulator _) _ _ ]=> P. 
    1,2: rewrite/pre_cmd_action/construct_simulator; cbn [post_cmd_action sim_post sim_step]; cook; subst P; cbn beta.
    1,2: assert_fails (pattern_focus [construct_simulator _]). (* Checkpoint. TODO: Think about checkpoint practices *)
    1,2: rewrite/clean_assign_stp_store/get_assign_val/get_assign_dest; cook.
    1,2: pattern_eq_2 [post_cmd_action _ _ (update_to_store _ _ _)] [post_cmd_action _ _ (update_to_store _ _ _)]=> [|<-]; swap 2 3.
        { apply/post_cmd_wf/update_to_store_storeview_eq; cook. wf_finisher. } (* TODO : wf_finisher this *)
        { apply/post_cmd_wf. Require Import TODO. exact:declassify_pubeq. }
    1,2: rewrite/clean_assign_stp_store/get_assign_val/get_assign_dest; cook.
    1,2: move: (post_cmd_action _ _ (update_to_store _ _ _));case=> >; cook.
    1,2: rewrite/zip.
    1,2: set rhs := RHS.
    1,2: rewrite combine_extend4_swap34 /combine_extend4 combine_extend3_splitl combine_extend2_nil_r.
    1,2: rewrite combine_extend2_same combine_extend2_nil_l.
    1,2: set lhs := LHS; subst rhs.
    1,2: rewrite/cmd_map combine_extend3_splitl !combine_extend2_nil_l.
    1,2: subst lhs; rewrite !map_map /cmd_map_sim.
    1,2: rewrite/sim_active /= /sim_active'; cook.
    1,2: enter (cnstrct_eq_gl; cook; clear; [apply: map_ext=> ?; cook|]).
    1,2: rewrite filter_map_swap. 
    1,2: erewrite filter_ext; [|move=> *; rewrite /= Bool.orb_false_r; reflexivity].
    1,2: cook; rewrite map_map.
    1,2: apply: map_ext; case=> //.
  Qed.

(* TODO: All these need to go to TODO.v *)
  Lemma public_compute_new_pc_opt untr pub rcmd :
    public (compute_new_pc_opt (mk_lbl untr pub) rcmd) = ~~ is_secret_guard rcmd && pub.
  Proof.
    rewrite /compute_new_pc_opt /is_secret_guard.
    case: rcmd => [c | ] //=.
    case: c => //=; case=> *.
    1-2: rewrite /is_secret /is_public; case: var_lbl  => ug pg /=; rewrite negbK //.
  Qed.

  Lemma acmd_prestate_pubeq atkst isatk s1 s2 :
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    ⟨ (if isatk then pre_cmd_action adv atkst s1 else s1) | is_public ⟩ =
    ⟨ (if isatk then pre_cmd_action adv atkst s2 else s2) | is_public ⟩.
  Proof. move=> pe. case: isatk. - apply: pre_cmd_wf_conf. exact: pe. - exact: pe. Qed.

  Fact post_acmd_pubeq atkst isatk s1 s2 :
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv atkst (if isatk then pre_cmd_action adv atkst s1 else s1) =
    post_cmd_action adv atkst (if isatk then pre_cmd_action adv atkst s2 else s2).
  Proof. move=> pe. apply: post_cmd_wf. exact: acmd_prestate_pubeq. Qed.

  Fact post_optcmd_acmd_pubeq atkst isatk l oc s1 s2 :
    l ⊢ oc ->
    oapp extract_controlled_declassify None oc = None ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv atkst
      (optcmd_stp_store oc (if isatk then pre_cmd_action adv atkst s1 else s1)) =
    post_cmd_action adv atkst
      (optcmd_stp_store oc (if isatk then pre_cmd_action adv atkst s2 else s2)).
  Proof.
    move=> wt nodecl pe. apply: post_cmd_wf.
    move: (acmd_prestate_pubeq atkst isatk _ _ pe) => pe'.
    case: oc nodecl wt => [c | ] //= *.
    wf_finisher.
  Qed.

  Fact cnt_acmd_pubeq atkst isatk oc s1 s2 :
    is_secret_guard oc = false ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    optcmd_stp_cnt oc (if isatk then pre_cmd_action adv atkst s1 else s1) =
    optcmd_stp_cnt oc (if isatk then pre_cmd_action adv atkst s2 else s2).
  Proof.
    move=> nsg pe.
    move: (acmd_prestate_pubeq atkst isatk _ _ pe) => pe'.
    case: oc nsg => [c | ] nsg //=.
    apply: clean_cmd_stp_cnt_pub_nf => //.
  Qed.

  (* Merge a matched rst/simst subterm pair (only fires when both halves are
     present), discharging via the relevant acmd-pubeq lemma. *)
  Ltac2 Set curr_cookbook as old :=
    add_cookstep ltac1:(match goal with
      | _ : ⟨ ?rst | is_public ⟩ = ⟨ ?simst | is_public ⟩ |- _ =>
        first
          [ pattern_eq_2 [post_cmd_action _ _ (if _ then _ else rst)]
                         [post_cmd_action _ _ (if _ then _ else simst)] => [|<-];
              [apply: post_acmd_pubeq; eassumption|]
          | pattern_eq_2 [post_cmd_action _ _ (optcmd_stp_store _ (if _ then _ else rst))]
                         [post_cmd_action _ _ (optcmd_stp_store _ (if _ then _ else simst))] => [|<-];
              [apply: post_optcmd_acmd_pubeq; eassumption|] (* TODO: This will be wrong? Maybe add tests?  *)
          | pattern_eq_2 [optcmd_stp_cnt _ (if _ then _ else rst)]
                         [optcmd_stp_cnt _ (if _ then _ else simst)] => [|<-];
              [apply: cnt_acmd_pubeq; eassumption|] ]
      end) "acmd_pubeq" old.

  Theorem extract_step_commute c:
    Invariant c ->
    step (extract_2cfg c) = extract_2cfg (comb_step c).
  Proof.
    case: c. case=> rst ist simst atkst.
    case=> //. case=> rcmd isatk icmd pclbl restcmd inv.
    have [] :
      (oapp extract_controlled_endorse None rcmd = None /\ oapp extract_controlled_declassify None rcmd = None)
      \/ (exists x, oapp extract_controlled_endorse None rcmd = Some x \/
                    oapp extract_controlled_declassify None rcmd = Some x);[.. |case; case; eauto using extract_step_commute_downgrade ].
      { clear; case: rcmd=> //=; auto. case=> [ | /=|/= ]; auto. case=> *; cook; auto; case: (_ (assign _))=> *; constructor; eauto; fail. }
    case=> noend nodecl.
    rewrite /= in inv. move: inv=> []. (Forall_inv_toph)=> i1 restinv i3.
    rewrite /CmbCmdInv/TypeInv in i1. case: i1=> - + _=>- [] rwt _.
    rewrite /StateInv in i3. case: i3=> _ pubeq.
    move: pclbl rwt.
    case=> untr pub => rwt.
    rewrite/comb_step/cmbcmd_step {}/extract_2cfg. cook.
    rewrite /extract_2cfg.
    rewrite/sim_active. cook.
    rewrite/step /acmd_step.  
    pattern_eq [if _ then pre_cmd_action (construct_simulator _) _ _ else ist] with ist; [| move=> ->]. (* Ninja repair *)
      { case: sim_active'=> //; move: noend; clear. case: pub=> //.
      rewrite/pre_cmd_action/construct_simulator/sim_pre. move=> -> //. }   (* TODO: This needs to be cook!! Why does the noend rewrite not fire.. *)
    congr (_,_,_); cook.
    - set l1 := (X in map _ X = _). set l2 := (X in _ = map _ X).
      suff: l1 = map (fun c => (real_cmd c, real_atk_bit c,  ideal_cmd c, sim_active c)) l2;
        [move=> ->; rewrite map_map //| subst l1 l2]. (* TODO: This could be lemma / rewrite rule *)
      rewrite/zip.
      set new_pc := (compute_new_pc_opt _ _).
      set l1 := (map Some (optcmd_stp_cnt rcmd _)). set l2 := (map Some (optcmd_stp_cnt icmd _)). set l3 := (repeat true _).
      set c4l := (combine_extend4 _ _ _ _ _ _ _ _). set c3l := (combine_extend3 _ _ _ _ _ _).
      rewrite /cmd_map !map_map. 
      erewrite map_ext; [| case; case; cbn; rewrite/sim_active; cbn=> *; instantiate (1  := fun '(_,_,_) => (_, _, _, _ )); reflexivity].
      subst c4l c3l.
      set idlatkcont := (repeat true _). 
      rewrite combine_extend3_swap23 map_map.
      erewrite (map_ext); [|(do 2 case)=> >; instantiate (1  := fun '(_,_,_) => (_, _, _, _ )); reflexivity].
      suff: combine_extend3 l1 l3 idlatkcont None false false =
            map (fun '(c, b) => (c, b, sim_active' c b (public new_pc))) (combine_extend2 l1 l3 None false).
        { move: l1 l2 l3 new_pc idlatkcont=> >; clear=> h. 
        rewrite combine_extend4_swap34 /combine_extend4 {}h. (* TODO: combine_extend4 splitr and splitl *)
        erewrite combine_extend2_map_l; [|instantiate (1 := (None, false))=> //=;cook].
        rewrite -combine_extend3_splitr map_map.
        apply: map_ext; case;case=> //. }
      set lhs := LHS. set rhs := RHS.
      suff: map (fun '(_,_,x) => x) lhs = map (fun '(_,_,x) => x) rhs; rewrite {}/lhs {}/rhs; rewrite map_map.
      1: move=>/esym; erewrite (map_ext).
      3: symmetry; erewrite (map_ext).
      2,4: case=> >; instantiate (1 := fun '(_,_) => _); reflexivity.
        { rewrite combine_extend3_splitr. move: (combine_extend2 _ _ _ _)=> l. clear.
        move: idlatkcont=>idlatkcont. clear=> h.
        erewrite combine_extend2_map_snd; [apply: map_ext; case=> >; f_equal; instantiate (1:= fun '(_,_) => _); reflexivity|].
        rewrite h. apply: map_ext; case; case=> * //. }
      rewrite {}/new_pc {}/l1 {}/l3 {}/idlatkcont {l2}.
      case e: (sim_active' _ _ _); cycle 1; [| clear e].
        { move: (sim_active'_false _ _ _ e)=> [] -> [] -> //=.
        rewrite combine_extend3_splitr; cook. rewrite !map_map.
        apply: map_ext. cook. }
      rewrite/sim_step. cook. (* TODO: There is something wrong here *)
      set (public _) as x; move newpce: x=> newpc; subst x. (* TODO: ssr patterns are a pain *)
      rewrite public_compute_new_pc_opt in newpce. case: newpc in newpce *; cycle 1. 
        { do [move=> /negbT; rewrite negb_and negbK=> /orP] in newpce.
        case: pub in rwt newpce *; move=> /= in newpce. 
        1: move=> /=; move: newpce=> [] // ->.
        2: wf_finisher_guess [post_cmd_action _ _ (optcmd_stp_store _ _)] with (post_cmd_action _ _ (if _ then _ else _))=> ->. (* How does this even work? *)
        1-2: move=> /=; cook. 
        1-2: rewrite combine_extend3_splitl combine_extend2_same map_map. 
        1-2: erewrite combine_extend2_map_r; [|done]; rewrite map_map.
        1-2: erewrite map_ext; [|case=> ?; instantiate (1 := (fun '(_,_) => _)); reflexivity].
        1-2: apply: map_ext; case=> *; rewrite/sim_active'; cook. }
      move: newpce rwt=> /andP [] /negbTE rcmd_grd -> rwt.
      rewrite /= rcmd_grd /=. cook.
      rewrite combine_extend3_splitr. 
      rewrite -map_const combine_extend2_map_self_r map_map.
      apply: map_ext_in; case; case=> [?|]; case=> //=.
      move: (optcmd_stp_cnt _ _)=> l. move: (if _ then _ else _)=> n. 
      clear=> contra; exfalso; move: contra.
      elim: l n=> //=; [elim=> //= ? ? [] //|]. (* Damn. I used induction in the base, but not  *)
      move=> > ?; case=> //=; [|move=> > [] //; eauto].
      rewrite map_map. case=> // /in_map_iff [] ? [] []//.

    - case e: (sim_active' _ _ _); cycle 1; 
      [move: (sim_active'_false _ _ _ e)=> []  ->; case=> e'; rewrite -> e' in *=> {e'} //=; f_equal | clear e]; cook.
      1-2: rewrite /zip; cook.
      1-2: rewrite/ cmd_map_sim filter_map_swap; cook.
        { erewrite filter_ext; cycle 1.
            { case; case=> * /=. 
            rewrite compute_new_pc_opt_secret /=.
            instantiate (1:= fun '(_,_,_)=> _); reflexivity. }
          rewrite combine_extend3_nil3 filter_map_swap. cook.
          erewrite filter_ext; cycle 1.
            { case=> *. instantiate (1:= fun '(_,_)=> _); reflexivity. }
          unshelve erewrite filter_ext; [exact xpred0|apply filter_false|].
          case=> //. }
        { erewrite filter_ext; [| case; case=> * /=; instantiate (1:= fun '(_,_,_)=> _); reflexivity].
        rewrite combine_extend3_nil1 combine_extend2_nil_r !map_map filter_map_swap. cook.
        unshelve erewrite filter_ext; [exact xpred0|apply filter_false|]. cook. }
      rewrite/sim_step /=; cnstrct_eq_gl; cook.
        { case: pub rwt => rwt /=; cook; congr (_.1); [wf_finisher|].
        wf_finisher_guess [LHS] with (post_cmd_action _ _ (_ _ _ rst))=> ->. wf_finisher. } (* Classic transitivity *)
      rewrite/zip/cmd_map_sim filter_map_swap map_map. symmetry.
      erewrite map_ext; [|case; case=> * /=; instantiate (1:= fun '(_,_,_) => _); reflexivity].
      erewrite filter_ext; [|case; case=> *; rewrite /sim_active; cbn; instantiate (1:= fun '(_,_,_) => _); reflexivity].
      rewrite combine_extend3_swap23. move: (map Some (_ _ ist))=> ?.
      rewrite filter_map_swap map_map.
      erewrite map_ext; [|case; case=> * /=; instantiate (1:= fun '(_,_,_) => _); reflexivity].
      erewrite filter_ext; [|case; case=> *; cbn; instantiate (1:= fun '(_,_,_) => _); reflexivity].
      move newpce: (public _)=> newpc. (* I don't know why ssr patterns succeed here. TODO *)
      rewrite public_compute_new_pc_opt in newpce. case: newpc in newpce *; cycle 1. 
        { erewrite filter_ext; [|case; case=> ? ? ?; rewrite /sim_active' /= Bool.orb_false_r; instantiate (1 := fun '(_,_,_) => _); reflexivity].
        do [move=> /negbT; rewrite negb_and negbK=> /orP] in newpce.
        case: pub in rwt newpce *; move=> /= in newpce. 

        2: wf_finisher_guess [post_cmd_action _ _ (optcmd_stp_store _ _)] with (post_cmd_action _ _ (if _ then _ else _))=> -> /=; cook. (* How does this even work? *)
        1: move: newpce=> [] // ->.
        1: rewrite combine_extend2_nil_l.
        1: cook; set l1 := filter _ _; set l2 := repeat true _.
        1: suff: map (fun '(_,i,_) => i) l1 = l2; [move: l1 l2=> > <-; rewrite map_map; apply: map_ext=> - [] [] //|subst l1 l2].  
        1,2: move: (if _ then _ else _) (map Some _)=> ? ?.
        1,2: rewrite combine_extend3_swap23 combine_extend3_splitr filter_map_swap map_map.
        1,2: erewrite map_ext; [|case; case=> *; instantiate (1 := fun '(_, _,_)=> _); reflexivity ].
        1,2: erewrite filter_ext; [|case; case=> *; instantiate (1 := fun '(_, _,_)=> _); reflexivity ].
        1,2: enter (erewrite map_filter_combine_extend2_ind2;  only 2,3: (case=> *; instantiate (1:= fun _ => _); reflexivity); only 2: done).
        1,2: clear; revert_hyp_pat nat; elim=> * /=; cook. 
        rewrite map_id //. }
      move: newpce rwt=> /andP [] /negbTE rcmd_grd -> rwt.
      rewrite rcmd_grd. cook.
      rewrite combine_extend3_splitr. 
      move: (X in (map Some X)) (X in (repeat true X))=> *.
      erewrite map_filter_combine_extend2_ind1.
      2,3: case=> *; instantiate (1:= fun '(_,_) => _); reflexivity; done. 2: done.
      clear. erewrite map_ext; [|instantiate (1 := id); case=> //]. rewrite map_id.
      revert_hyp_pat [Prog, nat].
      elim; [elim=> //= n ?; f_equal=> //|].
      move=> > ?; case=> /= *; [| f_equal; eauto].
      rewrite !filter_map_swap.
      erewrite filter_ext; [| move=> * /=; reflexivity].
      cnstrct_eq_gl. rewrite filter_true //.
  Qed.
  Print Assumptions extract_step_commute.

  Theorem extract_step_commute_event c:
    Invariant c ->
    two_event (extract_2cfg c) = (comb_event c, comb_event c).
  Proof. 
    move=> cinv.
    rewrite/two_event extract_step_commute // /comb_event.
    set cstp := comb_step c.
    have csinv: Invariant cstp; [exact: cfg_step_inv|].
    case: c cinv cstp csinv. (* TODO: we lose info*)
    rewrite/Invariant/extract_2cfg.
    move=> ? [] // ? ? []. Forall_inv_toph.
    rewrite cmd_map_cons=> cc1i _ cs1i []. 
    move=> ? ? [] _ cs2i.
    congr (_,_).
    rewrite/event_helper.
    cnstrct_eq_gl; cycle 1.
      { rewrite/pre_cmd_event/construct_simulator/sim_evnt cmd_map_sim_cons -/(pre_cmd_event _)/sim_active.
      case e: sim_active'=> //.
      move: e=> /sim_active'_false [] -> //. }
    pattern_eq_2 [⟨_|_⟩] [⟨_|_⟩]; [move: cs2i=> [] //|].
    move: (X in ⟨X|_⟩)=> ? <- {cs2i}.
    move: cc1i cs1i. rewrite/CmbCmdInv/TypeInv/StateInv. 
    case=> + _. case. case: (pc_lbl _)=> - [] ? /= rwt=> [ |<- //].
    move=> iwt [] *.
    pattern_eq [LHS] with None=> [|->] ;[|pattern_eq [RHS] with None=> [|->]]=>//.
    1: case: (ideal_cmd _) iwt => // c //= wt.
    2: case: (real_cmd _) rwt => // c //= wt.
    1,2: case e: c=> //. 
    1,2: move: (wf_untr_cmd_dst_untr _ _ _ wt e).
    1,2: rewrite -/(is_untrusted _).
    1,2: move: (get_assign_dest _)=> > untr.
    1,2: pattern_eq [ ⟨ _ | _ ⟩ _] with None=> [|->] //. (* TODO: Could be elsewhere *)
    1,2: rewrite/⟨_|_⟩ /is_trusted untr //.
  Qed.
End extract_step_commute.
