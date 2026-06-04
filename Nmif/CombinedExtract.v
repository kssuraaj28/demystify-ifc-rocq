From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Combined Simulator.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!". 
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

Import Combined.
#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

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
    cmd_map (a :: l) =
      (mk_atkcmd (real_atk_bit a) (real_cmd a),
       mk_atkcmd (sim_active a) (ideal_cmd a)) :: cmd_map l.
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
  Notation extract_2cfg := (extract_2cfg (AtkStates := AtkStates)).
  Notation step := (step adv (construct_simulator adv)).

  Import Util.List Combined VarValStore.Notations.


    (* TODO: cook rules in foreign cookbooks reference lemmas by unqualified
       name (e.g. `rewrite -> WellFormedOptCmd_Some in *`). Joining the
       cookbook is not enough — the importing file must also `Import` the
       module so the bare name resolves at fire time, otherwise the rewrite
       errors and `cook` silently drops the step. Figure out a cleaner fix. *)
  Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()).
  Ltac2 Set curr_cookbook as old := join_cookbooks Combined.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Semantics.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks TypeSystem.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Attacker.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Util.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Util.List.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Lattice4pt.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks VarValStore.this_cookbook old.
  Ltac2 Set curr_cookbook as old := join_cookbooks Syntax.this_cookbook old.




  Ltac2 Set cook_debug := 0.

  (* A downgrade that actually crosses the attacker — `from ⋢ to`.  A *safe*
     downgrade (`from ⊑ to`) is routed to extract_step_commute_core instead;
     this predicate lets extract_step_commute_downgrade assume the canonical
     (NI-violating) shape, so its two safe disjuncts close by contradiction. *)
  Definition downgrade_unsafe (oc : option Cmd) : bool :=
    match oc with
    | Some (assign (endorse from to)) => ~~ flows_to (var_lbl from) (var_lbl to)
    | Some (assign (declassify from to)) => ~~ flows_to (var_lbl from) (var_lbl to)
    | _ => true
    end.

  Lemma extract_step_commute_downgrade (st: CmbState) (c: CmbCmd) (restcmd: list CmbCmd):
    oapp is_endorse false (real_cmd c) \/ oapp is_declassify false (real_cmd c) ->
    downgrade_unsafe (real_cmd c) ->
    Invariant (st, c :: restcmd) ->
    (step (extract_2cfg (st, c :: restcmd))).1.1 = extract_2cfg ((comb_step (st, c :: restcmd)).1).
  Proof.
    case: c=> rcmd ratk icmd pclbl.  case: st=> rst ist simst atkst.
    cook. rewrite/Invariant=> downgrade unsafe. case. cook.
    rewrite/CmbCmdInv/StateInv=> + + [].
    case: downgrade=> downgrade.
    1: move: downgrade=> /is_endorse_inv_opt.
    2: move: downgrade=> /is_declassify_inv_opt.
    1,2: move=> [from] [to] Hrc; rewrite Hrc in unsafe; move: Hrc=> ->.
    1,2: rewrite/CmbCmdCoreInv=> - [].
    1: move/wf_endorse_inv. 2: move/wf_declassify_inv.
    (* Split the wf_*_inv disjunction.  After this the four goals are, in order:
       endorse-canonical, endorse-safe, declassify-canonical, declassify-safe.
       The two safe goals (from ⊑ to) contradict `unsafe` (from ⋢ to); the real
       safe downgrades are handled by extract_step_commute_core via the dispatch
       in extract_step_commute. *)
    1,2: move=> [Hcanon | [Hft Hpcto]].
    2,4: by move: unsafe; rewrite /= Hft.
    1,2: move: Hcanon=> [->] [? ?].
    1,2: dotop [cbn]=> <- _ ? ?.
    1,2: rewrite/comb_step/cmbcmd_step/corrupt_ideal/read_sim/extract_2cfg; cook.
    1,2: pattern_eq [sim_active  _] with true=>[| ->]; [simpl; cook|].
    1,2: rewrite/step/acmd_step /=.
    1,2: assert_fails (pattern_focus [construct_simulator _]). (* Checkpoint. TODO: Think about checkpoint practices *)
    1,2: rewrite/clean_assign_stp_store/get_assign_val/get_assign_dest.
    1: pattern_eq [is_untrusted _] with true=>[| ->]; cook.
    2: pattern_eq [is_secret _] with true=>[| ->]; cook.
    1,2: pattern_eq [is_public _] with true=>[| ->]; cook.
    1,2: pattern_eq_2 [post_cmd_action _ _ (update_to_store _ _ _)] [post_cmd_action _ _ (update_to_store _ _ _)]=> [|<-]; swap 2 3.
        { apply/post_cmd_wf/update_to_store_storeview_eq; cook. }
        { apply/post_cmd_wf.  set a := (pre_cmd_action _ _ _). set b := (pre_cmd_action _ _ _).
        have ?: ⟨ b | is_public ⟩ = ⟨ a | is_public ⟩; subst a b; cook. (* I don't like this *)
        erewrite <- update_same_varval;[| eassumption]. repeat f_equal.
        erewrite storeview_eq; [ |apply: pre_cmd_wf_int| ]; cook.
        apply:storeview_eq; eauto. cook. }
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

  (* A command preserves confidentiality unless it is an NI-violating declassify.
     Non-declassify commands and *safe* declassifies (from ⊑ to) all qualify; the
     canonical ST→PT declassify (from ⋢ to) does not.  This is what the reshaping
     in extract_step_commute_core needs for the public-view (simulator) side, and
     it covers the safe-declassify case that `~~ is_declassify` would exclude. *)
  Definition conf_safe_cmd (c : Cmd) : bool :=
    if c is assign (declassify from to) then flows_to (var_lbl from) (var_lbl to) else true.
  Definition conf_safe_oc (oc : option Cmd) : bool := oapp conf_safe_cmd true oc.

  (* Confidentiality noninterference, generalised from `~~ is_declassify` to
     `conf_safe_cmd` so it also holds for safe declassifies. *)
  Lemma ni_cmd_st_conf' c l st1 st2 :
    WellFormedCmd l c -> conf_safe_cmd c ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
    ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof.
    move=> wt cs peq.
    case Hd: (is_declassify c); last first.
    - apply: ni_cmd_st_conf; [exact: wt | rewrite Hd // | exact: peq].
    - move: (is_declassify_inv c Hd) cs => [from [to ->]] /= cs.
      rewrite /clean_cmd_stp_store /clean_assign_stp_store /get_assign_dest /get_assign_val /=.
      case dp: ([elaborate is_public to]); [| rewrite !update_storeview_nochange //].
      apply: update_to_store_storeview_eq; [exact: (flows_to_pub _ _ dp cs) | exact: peq].
  Qed.

  (* The simulator's pre (sim_pre) has the same NI-violation corruption guard as
     corrupt_ideal, so when the command does not corrupt (the core hypothesis
     Hcorr) the simulator leaves the protected ideal store untouched. *)
  Lemma sim_pre_id ast sst ocmd isatk rest ist :
    (forall id ss, corrupt_ideal ocmd id ss = id) ->
    pre_cmd_action (construct_simulator adv) (mk_simstate ast sst ((ocmd, isatk) :: rest)) ist = ist.
  Proof.
    move=> H. rewrite /pre_cmd_action /construct_simulator /sim_pre.
    exact: (H ist _).
  Qed.

  Lemma ni_optcmd_st_conf_atk' ast l oc s1 s2 :
    l ⊢ oc -> conf_safe_oc oc -> ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s1)) =
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s2)).
  Proof.
    move=> wt cs peq. apply: post_cmd_wf.
    case: oc wt cs => [c | ] wt cs /=.
    - apply: (ni_cmd_st_conf' _ _ _ _ wt cs). apply: pre_cmd_wf_conf=> //.
    - apply: pre_cmd_wf_conf=> //.
  Qed.

  Lemma public_compute_new_pc_opt untr pub rcmd :
    public (compute_new_pc_opt (mk_4ptlbl untr pub) rcmd) = ~~ is_secret_guard rcmd && pub.
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
    conf_safe_oc oc ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv atkst
      (optcmd_stp_store oc (if isatk then pre_cmd_action adv atkst s1 else s1)) =
    post_cmd_action adv atkst
      (optcmd_stp_store oc (if isatk then pre_cmd_action adv atkst s2 else s2)).
  Proof.
    move=> wt cs pe. apply: post_cmd_wf.
    move: (acmd_prestate_pubeq atkst isatk _ _ pe) => pe'.
    case: oc cs wt => [c | ] //= *.
    apply: ni_cmd_st_conf'; eauto.
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

  Lemma read_sim_none a b : read_sim None a b = a.
  Proof. by []. Qed.

  (* The simulator's controlled read (sim_step / cmbcmd_step both use read_sim).
     When a `forall ss id, read_sim rcmd ss id = ss` hypothesis is present (the
     core's Hread), eliminate any read_sim of rcmd or None.  This replaces the
     syntactic `no_declassify` cook step for the assignment-like core, which must
     also cover safe declassifies (where `~~ is_declassify` does not hold). *)
  Ltac2 Set curr_cookbook as old :=
    add_cookstep ltac1:(match goal with
      | Hr : forall ss id, read_sim ?c ss id = ss |- context[read_sim ?c ?a ?b] =>
          rewrite (Hr a b)
      | |- context[read_sim None ?a ?b] => rewrite (read_sim_none a b)
      end) "read_sim_elim" old.

  (* The "assignment-like" commute: the reshaping that proves the step/comb_step
     square for a head command that performs NO ideal corruption (Hcorr) and NO
     ideal read (Hread) and preserves confidentiality (conf_safe_oc).  Every
     non-downgrade command and every *safe* downgrade satisfies these (the safe
     downgrades supply Hcorr/Hread via flows_to from to); the dispatcher in
     extract_step_commute routes them here, and routes the canonical
     (NI-violating) downgrades to extract_step_commute_downgrade. *)
  Lemma extract_step_commute_core rst ist simst atkst rcmd ratk icmd untr pub restcmd :
    (mk_4ptlbl untr pub) ⊢ rcmd ->
    ⟨ rst | is_public ⟩ = ⟨ simst | is_public ⟩ ->
    conf_safe_oc rcmd ->
    (forall id ss, corrupt_ideal rcmd id ss = id) ->
    (forall ss id, read_sim rcmd ss id = ss) ->
    (step (extract_2cfg (mk_cmbstate rst ist simst atkst,
                         mk_cmbcmd rcmd ratk icmd (mk_4ptlbl untr pub) :: restcmd))).1.1 =
    extract_2cfg ((comb_step (mk_cmbstate rst ist simst atkst,
                         mk_cmbcmd rcmd ratk icmd (mk_4ptlbl untr pub) :: restcmd)).1).
  Proof.
    move=> rwt pubeq csafe Hcorr Hread.
    rewrite/comb_step/cmbcmd_step. rewrite Hcorr Hread {}/extract_2cfg. cook.
    rewrite /extract_2cfg.
    rewrite/sim_active. cook.
    rewrite/step /acmd_step.  
    pattern_eq [if _ then pre_cmd_action (construct_simulator _) _ _ else ist] with ist; [| move=> ->]. (* Ninja repair *)
      { case: (sim_active' rcmd ratk pub)=> //=.
        rewrite /pre_cmd_action /construct_simulator /sim_pre /=.
        case E: pub=> /=; [exact: (Hcorr ist _) | by rewrite /corrupt_ideal]. }
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
        2: erewrite ni_sec_optcmd_st_conf_atk;[|eassumption]. 
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
        { case: pub rwt => rwt /=; cook. (* TODO: This should be automated *)
           { erewrite ni_optcmd_st_conf_atk'; [reflexivity|..]; eauto. }
        erewrite ni_sec_optcmd_st_conf_atk; [|eassumption]. erewrite noninterfering_post_pre; [reflexivity|]. 
        congruence. }
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
        2: erewrite ni_sec_optcmd_st_conf_atk; [| eassumption]=> /=; cook.
        1: move: newpce=> [] // ->.
        1: rewrite combine_extend2_nil_l.
        1: cook; set l1 := filter _ _; set l2 := repeat true _.
        1: suff: map (fun '(_,i,_) => i) l1 = l2; [move: l1 l2=> > <-; rewrite map_map; apply: map_ext=> - [] [] //|subst l1 l2].  
        1,2: move: (if _ then _ else _) (map Some _)=> ? ?.
        1,2: rewrite combine_extend3_swap23 combine_extend3_splitr filter_map_swap map_map.
        1,2: erewrite map_ext; [|case; case=> *; instantiate (1 := fun '(_, _,_)=> _); reflexivity ].
        1,2: erewrite filter_ext; [|case; case=> *; instantiate (1 := fun '(_, _,_)=> _); reflexivity ].
        1,2: enter (erewrite map_filter_combine_extend2_ind2;  only 2,3: (case=> *; instantiate (1:= fun _ => _); reflexivity); only 2: done).
        1,2: clear; revert_hyp_pat nat; elim=> * /=; cook. rewrite map_id //. }
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

  Theorem extract_step_commute c:
    Invariant c ->
    (step (extract_2cfg c)).1.1 = extract_2cfg ((comb_step c).1).
  Proof.
    case: c. case=> rst ist simst atkst.
    case=> //. case=> rcmd isatk icmd pclbl restcmd inv.
    (* extract the head typing (rwt) and the public-view equality (pubeq) from a
       copy of the invariant; the original `inv` is kept for the canonical route. *)
    move: (inv)=> [hfa hst].
    move: (Forall_inv hfa); rewrite /CmbCmdInv /CmbCmdCoreInv => -[rwt _].
    move: hst; rewrite /StateInv => -[_ pubeq].
    case: (is_endorse_declassify_opt rcmd)=> [Hend | [Hdecl | [noend nodecl]]].
    - (* endorse: canonical → downgrade lemma; safe → core *)
      move: (Hend)=> /is_endorse_inv_opt [from][to] erc.
      rewrite erc in rwt.
      move: (rwt); rewrite WellFormedOptCmd_Some => /wf_endorse_inv [[Hpc [Hfrom Hto]] | [Hft Hpcto]].
      + apply: extract_step_commute_downgrade; [left; exact: Hend | rewrite erc /= Hfrom Hto // | exact: inv].
      + clear inv hfa. move: rwt Hpcto; rewrite erc; move: pclbl; case=> untr pub rwt Hpcto.
        apply: extract_step_commute_core.
        * exact: rwt.
        * exact: pubeq.
        * by [].
        * move=> id ss; exact: (corrupt_ideal_safe_endorse from to id ss Hft).
        * move=> ss id; apply: read_sim_nodecl=> //.
    - (* declassify: canonical → downgrade lemma; safe → core *)
      move: (Hdecl)=> /is_declassify_inv_opt [from][to] erc.
      rewrite erc in rwt.
      move: (rwt); rewrite WellFormedOptCmd_Some => /wf_declassify_inv [[Hpc [Hfrom Hto]] | [Hft Hpcto]].
      + apply: extract_step_commute_downgrade; [right; exact: Hdecl | rewrite erc /= Hfrom Hto // | exact: inv].
      + clear inv hfa. move: rwt Hpcto; rewrite erc; move: pclbl; case=> untr pub rwt Hpcto.
        apply: extract_step_commute_core.
        * exact: rwt.
        * exact: pubeq.
        * by rewrite /conf_safe_oc /conf_safe_cmd.
        * move=> id ss; apply: corrupt_ideal_noend=> //.
        * move=> ss id; exact: (read_sim_safe_declassify from to ss id Hft).
    - (* non-downgrade → core *)
      clear inv hfa. move: rwt; move: pclbl; case=> untr pub rwt.
      apply: extract_step_commute_core.
      * exact: rwt.
      * exact: pubeq.
      * move: nodecl; case: rcmd {rwt noend} => [c|]//; case: c => //; case=> //.
      * move=> id ss; exact: (corrupt_ideal_noend _ id ss (negbTE noend)).
      * move=> ss id; exact: (read_sim_nodecl _ ss id (negbTE nodecl)).
  Qed.

End extract_step_commute.
