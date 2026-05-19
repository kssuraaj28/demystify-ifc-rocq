From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Import ssrmatching.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Combined Simulator.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!". 
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section acmd.  (* TODO: This needs to go to some place good *)
  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm} {AtkStates : Type}.
  Variable (adv: AdvNextStep AtkStates).
  Record AtkCmd := mk_atkcmd {is_attacked: bool; cmd : option Cmd}.
  Definition State := (Store * AtkStates)%type.

  (* TODO: Maybe this is useful enough that you should use this in other places. Simulator construction. Combined *)
  Definition acmd_step (ac: AtkCmd) (s: State): Prog * State * nat :=  
    let: mk_atkcmd isatk cmd := ac in 
    let: (store, atk_st) := s in 
    let: st := if isatk is true then pre_cmd_action adv atk_st store else store in
    let: (prog, st) := (optcmd_stp_cnt cmd st,  optcmd_stp_store cmd st) in 

    let: atk_pst := (post_cmd_action adv atk_st st) in (* Not having this was quite painful. TODO *)
    let: atk_st := if isatk is true then atk_pst.1 else atk_st in
    let: steps := if isatk is true then atk_pst.2 else 0 in

    (prog, (st, atk_st), steps).

  Lemma acmd_step_atk cmd store atk_st :
    acmd_step (mk_atkcmd true cmd) (store, atk_st) =
      let pre_st := pre_cmd_action adv atk_st store in
      let st'    := optcmd_stp_store cmd pre_st in
      let pst    := post_cmd_action adv atk_st st' in
      (optcmd_stp_cnt cmd pre_st, (st', pst.1), pst.2).
  Proof. done. Qed.

  Lemma acmd_step_noatk cmd store atk_st :
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

  Definition Cfg := (list (AtkCmd * AtkCmd) * State1 * State2)%type.

  Definition step (c: Cfg): Cfg :=
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


Section comb_compile_simulator.
  Import Simulator.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.

  Notation SimStates := (SimStates (AtkStates:=AtkStates)).

  Notation CombCfg := (Combined.Cfg (AtkStates:= AtkStates)).
  Notation CfgTwo := (Cfg (AtkStates1:= AtkStates) (AtkStates2:= SimStates)).

  Section sim_active.
    Import Combined.
    Definition sim_active' (rcmd: option Cmd) (ratk: bool) (is_pubpc: bool) : bool :=
      ratk || (is_pubpc && if rcmd is None then false else true).

    (* TODO: Learn more about this variant stuff. *)
    Variant sim_active'_spec (rcmd: option Cmd) (ratk pub: bool) : bool -> Prop :=
      | SimActiveFalse :
          ratk = false -> (pub = false \/ rcmd = None) ->
          sim_active'_spec rcmd ratk pub false
      | SimActiveTrue :
          (ratk = true \/ (pub = true /\ exists cmd, rcmd = Some cmd)) ->
          sim_active'_spec rcmd ratk pub true.

    
    (* This is an ssr trick *)
    Lemma sim_active'P rcmd ratk pub :
      sim_active'_spec rcmd ratk pub (sim_active' rcmd ratk pub).
    Proof.
      rewrite /sim_active'.
      case: ratk; [do! constructor; done|].
      case: pub; [case: rcmd => > | ]; do! constructor; eauto; done. 
    Qed.

    Definition sim_active (c: CmbCmd) : bool :=
      sim_active' (real_cmd c) (real_atk_bit c) (public (pc_lbl c)).

    
  End sim_active.

  Section cmd_map.
    Import Combined.
    Definition cmd_map (lst: list CmbCmd) : list (AtkCmd * AtkCmd) :=
      let: mapfn :=
        fun cmbcmd => (
          mk_atkcmd (real_atk_bit cmbcmd) (real_cmd cmbcmd),
          mk_atkcmd (sim_active cmbcmd) (ideal_cmd cmbcmd)) in
      map mapfn lst.

    (* TODO: flat_map would fuse the filter+map into one traversal and
       make reasoning slightly easier. Sticking with separate filter and
       map for now to match the rest of the codebase. *)
    Definition cmd_map_sim (lst: list CmbCmd) : list (option Cmd * bool) :=
      let: mapfn :=
        fun cmbcmd =>
          let: ocmd := if (public (pc_lbl cmbcmd)) is false then None else
                         (real_cmd cmbcmd) in
          (ocmd, real_atk_bit cmbcmd) in
      map mapfn (filter sim_active lst).

    Lemma cmd_map_cons a l :
      cmd_map (a :: l) =
        (mk_atkcmd (real_atk_bit a) (real_cmd a),
         mk_atkcmd (sim_active a) (ideal_cmd a)) :: cmd_map l.
    Proof. done. Qed.

    Lemma cmd_map_sim_cons a l :
      cmd_map_sim (a :: l) =
        if sim_active a
        then ((if public (pc_lbl a) is false then None else real_cmd a),
              real_atk_bit a) :: cmd_map_sim l
        else cmd_map_sim l.
    Proof. rewrite /cmd_map_sim /=. case: (sim_active a)=> //=. Qed.

    Lemma cmd_map_app l1 l2 :
      cmd_map (l1 ++ l2) = cmd_map l1 ++ cmd_map l2.
    Proof. rewrite /cmd_map map_app. done. Qed.

    Lemma cmd_map_sim_app l1 l2 :
      cmd_map_sim (l1 ++ l2) = cmd_map_sim l1 ++ cmd_map_sim l2.
    Proof. rewrite /cmd_map_sim filter_app map_app. done. Qed.

    Lemma cmd_map_sim_zip_pub rl il k pclbl :
      public pclbl = true ->
      cmd_map_sim (zip rl il k pclbl) =
      Util.List.combine_extend2 (map Some rl) (repeat true k) None false.
    Admitted. (* TODO: combinatorial induction on rl/il/k. *)

    Lemma cmd_map_sim_zip_sec rl il k pclbl :
      public pclbl = false ->
      cmd_map_sim (zip rl il k pclbl) = repeat (None, true) k.
    Admitted. (* TODO: combinatorial induction on rl/il/k. *)

    Import Util.List.
    Lemma cmd_map_zip rl il steps pclbl :
      cmd_map (zip rl il steps pclbl) =
        map (fun '(rc, ic, abit) =>
               (mk_atkcmd abit rc,
                mk_atkcmd (abit ||
                           (public pclbl &&
                            if rc is None then false else true))
                          ic))
            (combine_extend3 (map Some rl) (map Some il)
                             (repeat true steps) None None false).
    Proof.
      rewrite /cmd_map /zip /sim_active map_map.
      apply: map_ext. case=> -[rc ic] abit. done.
    Qed.

    Lemma map_proj_map_mk pclbl l :
      map (fun _c : CmbCmd =>
             (real_cmd _c, real_atk_bit _c, ideal_cmd _c, sim_active _c))
          (map (fun '(_rc, _ic, _abit) => mk_cmbcmd _rc _abit _ic pclbl) l) =
      map (fun '(_rc, _ic, _abit) =>
             (_rc, _abit, _ic,
              _abit || (public pclbl && if _rc is None then false else true)))
          l.
    Proof. rewrite map_map. apply: map_ext. case=> -[rc ic] abit. rewrite /sim_active /=. done. Qed.

  End cmd_map.

  Section extract.
    Import Combined.
    Definition extract_2cfg (c: CombCfg): CfgTwo :=
      let: (mk_cmbstate rst ist simst atkst, cmblst) := c in 
      let: cfg2prog := cmd_map cmblst in
      let: simprog := cmd_map_sim cmblst in 
      (cfg2prog, (rst, atkst), (ist, mk_simstate atkst simst simprog)).
  End extract.
End comb_compile_simulator.

Section extract_step_commute.
  Import TypeSystem Simulator.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable adv : (AdvNextStep AtkStates).

  Notation CombCfg := Combined.Cfg.
  Notation comb_step := (Combined.cfg_step adv).
  Notation extract_2cfg := (extract_2cfg (AtkStates := AtkStates)).
  Notation step := (step adv (construct_simulator adv)).

  Import Util.List Combined VarValStore.Notations.

  Section cook.
    (* TODO: stir rules in foreign cookbooks reference lemmas by unqualified
       name (e.g. `rewrite -> WellFormedOptCmd_Some in *`). Joining the
       cookbook is not enough — the importing file must also `Import` the
       module so the bare name resolves at fire time, otherwise the rewrite
       errors and `stir` silently drops the step. Figure out a cleaner fix. *)
    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()).
    Ltac2 Set curr_cookbook as old := join_cookbooks Combined.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Semantics.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks TypeSystem.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Attacker.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.List.this_cookbook old.

    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> cmd_map_cons in * ) "cmd_map_cons" old.
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> cmd_map_app in * ) "cmd_map_app" old.
      (*
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> cmd_map_zip in * ) "cmd_map_zip" old.
      *)
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> cmd_map_sim_cons in * ) "cmd_map_sim_cons" old.
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> untrusted_mk in * ) "untrusted_mk" old.
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> public_mk in * ) "public_mk" old.
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> acmd_step_atk in * ) "acmd_step_atk" old.
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> acmd_step_noatk in * ) "acmd_step_noatk" old.
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> construct_simulator_pre_cmd in * ) "construct_simulator_pre_cmd" old.
    Ltac2 Set curr_cookbook as old :=
      add_stirstep 1 ltac1:(rewrite -> construct_simulator_post_cmd_cons in * ) "construct_simulator_post_cmd_cons" old.

    Ltac2 Eval print_cookbook curr_cookbook.
    Ltac2 Eval print_cookbook curr_stirbook.

    Ltac2 Set cook_auto_dbs := fun () => [@trickbag].
    Ltac2 Set cook_debug := 1.
    Ltac2 Set cook_auto_depth := 0.

  (* ssrpatternarg lets you parse X in X... However, you need to delimit with [ ]
    With uconstr, you don't need to, but you can't use X in .
    TODO: cpattern *)
  Tactic Notation "pattern_eq_2" "[" ssrpatternarg(p1) "]" "[" ssrpatternarg(p2) "]" :=
    let a := fresh "_e1" in
    let b := fresh "_e2" in
    ssrpattern p1; move=> a;
    ssrpattern p2; move=> b;
    have: a = b; subst a b.

  Tactic Notation "pattern_eq" "[" ssrpatternarg(p1) "]" "with" constr(c) :=
    let a := fresh "_e1" in
    ssrpattern p1; move=> a;
    have: a = c; subst a.

    Theorem extract_step_commute c:
      Invariant c ->
      step (extract_2cfg c) = extract_2cfg (comb_step c).
    Proof.
      case: c. case=> rst ist simst atkst.
      case=> //. case=> rcmd isatk icmd pclbl restcmd inv.
      rewrite /= in inv. move: inv=> []. (toph Forall_inv)=> i1 restinv i3.
      rewrite /CmbCmdInv/CmbCmdCoreInv in i1. case: i1=> rwt iwt.
      rewrite /StateInv in i3. case: i3=> treq pubeq.
      move: pclbl rwt iwt.
      (case=> - untr pub); stir=> rwt iwt.
      rewrite/comb_step/cmbcmd_step {2}/extract_2cfg; stir.
      rewrite /extract_2cfg; stir.
      rewrite/sim_active; stir.
      rewrite/step; stir.
      congr (_,_,_).
      -- congr (_ ++ _). stir. (* TODO: Forward reasoning *) 
         set l1 := (X in map _ X = _).
         set l2 := (X in _ = map _ X).
         suff: l1 = map (fun c => (real_cmd c, real_atk_bit c,  ideal_cmd c, sim_active c)) l2;
           [move=> ->; rewrite map_map //| subst l1 l2]. (* TODO: This could be lemma / rewrite rule *)
         rewrite/zip.
         set new_pc := (compute_new_pc_opt _ _).
         set l1 := (map Some (optcmd_stp_cnt rcmd _)). set l2 := (map Some (optcmd_stp_cnt icmd _)). set l3 := (repeat true _).
         set c4l := (combine_extend4 _ _ _ _ _ _ _ _). set c3l := (combine_extend3 _ _ _ _ _ _).
         rewrite /cmd_map !map_map. 
         erewrite map_ext; cycle 1.
           { case. case. cbn. rewrite/sim_active. cbn=> *. 
           instantiate (1  := fun '(_,_,_) => (_, _, _, _ )). (* Very cool. Like `refine`, I think *)
           reflexivity. }
         subst c4l c3l.
         set idlatkcont := (repeat true _). 
         rewrite combine_extend3_swap23 map_map.
         erewrite (map_ext);cycle 1.
           { (do 2 case)=> >.
             instantiate (1  := fun '(_,_,_) => (_, _, _, _ )). 
             reflexivity. }
         suff: combine_extend3 l1 l3 idlatkcont None false false =
               map (fun '(c, b) => (c, b, sim_active' c b (public new_pc))) (combine_extend2 l1 l3 None false) by admit.
         set lhs := LHS. set rhs := RHS.
         suff: map (fun '(_,_,x) => x) lhs = 
               map (fun '(_,_,x) => x) rhs; rewrite {}/lhs {}/rhs; rewrite map_map.
         1: move=>/esym; erewrite (map_ext).
         3: symmetry; erewrite (map_ext).
         2,4: case=> >; instantiate (1 := fun '(_,_) => _); reflexivity.
           { rewrite combine_extend3_splitr. move: (combine_extend2 _ _ _ _)=> l. clear.
           move: idlatkcont=>idlatkcont. clear=> h.
           erewrite combine_extend2_map_snd; [apply: map_ext; case=> >; f_equal; instantiate (1:= fun '(_,_) => _); reflexivity|].
           rewrite h. apply: map_ext; case; case=> * //. }
         clear l2 treq iwt.
         subst new_pc l1 l3 idlatkcont. 
         case: sim_active'P=>[|_].
           { move=> -> [] e; rewrite -> e in *=> {e} //=.
           rewrite combine_extend3_splitr; stir. rewrite !map_map.
           apply: map_ext=> *; stir. }
         stir. rewrite/sim_step. stir.
         set (public _) as x; case newpce: x; subst x; cycle 1. (* TODO: ssr version of this? *)
           { case: pub in rwt newpce *; cycle 1. (* Maybe custom rewriting rule *)
             { move=> /=; stir.
             rewrite length_map repeat_length.
             erewrite post_optcmd_stp_store_sec;[|eassumption].
             pattern_eq_2 [post_cmd_action _ _ (if isatk then _ else rst)] [post_cmd_action _ _ (if isatk then _ else simst)]=> [|->].
               { case: isatk; [apply: noninterfering_post_pre| apply: post_cmd_wf]=> //. } (* This pattern can be automated *)
             stir.  rewrite combine_extend3_splitl map_map. symmetry;
             erewrite map_ext; [|case=> ? [] *; instantiate (1 := fun '(_,(_,_)) => _); reflexivity].
             rewrite combine_extend2_same. set l := (map Some _).
             erewrite combine_extend2_map_r; [|done]. rewrite map_map.
             erewrite map_ext; [|case=> *; instantiate (1 := fun '(_,_)=> _);  reflexivity].
             apply: map_ext; case=> *. rewrite /sim_active'; stir. }
           have ->: is_secret_guard rcmd = true by admit. (* TODO: lots of same as before *)
           rewrite /= length_map repeat_length.
           pattern_eq_2 [post_cmd_action _ _ (_ _(if _ then _ else rst))] [post_cmd_action _ _ (_ _(if _ then _ else simst))]=> [|->].
             { destruct rcmd=> //;
             case: isatk; [|apply: post_cmd_wf]; stir.
             apply: noninterfering_post_clean_pre; [eassumption|]=>//. }

           rewrite combine_extend3_splitl combine_extend2_same map_map; symmetry.
           erewrite combine_extend2_map_r; [|done]. rewrite map_map.
           erewrite map_ext; [|case=> ?; instantiate (1 := (fun '(_,_) => _)); reflexivity].
           apply: map_ext. case=> *. rewrite/sim_active'. stir. }
         case: pub in rwt newpce *; [|move=> /=;stir].
         have rcmd_grd: is_secret_guard rcmd = false by admit.
         rewrite rcmd_grd /=. stir.
         pattern_eq_2  [ (post_cmd_action _ _ (_ _(if _ then _ else rst)))] [ (post_cmd_action _ _ (_ _(if _ then _ else simst)))] => [|->].
           { admit. }

         pattern_eq_2 [ (optcmd_stp_cnt _ (if _ then _ else rst)) ]  [(optcmd_stp_cnt _ (if _ then _ else simst)) ]=> [| <-].
           { destruct rcmd => //. 
           apply: clean_cmd_stp_cnt_pub_nf=> //.
           case: isatk; stir. }

         rewrite combine_extend3_splitr. 
         set l:= combine_extend2 (map Some _) (repeat true _) _ _.
         rewrite -map_const combine_extend2_map_self_r map_map. 
         subst l. stir.
         apply: map_ext_in; case; case=> [?|]; case=> //=.
         move: (optcmd_stp_cnt _ _)=> l. move: (if _ then _ else _)=> n. 
         clear=> contra; exfalso; move: contra.
         elim: l n=> //=; [elim=> //= ? ? [] //|]. (* Damn. I used induction in the base, but not  *)
         move=> > ?; case=> //=; [|move=> > [] //; eauto].
         rewrite map_map; case=> // /in_map_iff [] ? [] []//.

      -- congr (_,_); stir .
         case: sim_active'P=>[-> |_]; [case=> e; rewrite -> e in *=> {e} /=; f_equal|]; stir.
         1-2: rewrite /zip cmd_map_sim_app.
         1-2: set l := (X in _ = X ++ _); suff->: l = []; [done|subst l].
         1-2: rewrite/ cmd_map_sim.
         1-2: rewrite filter_map_swap map_map.
         1-2: set l := (X in map _ X); suff->: l = []; [done|subst l].
           { erewrite filter_ext; cycle 1.
               { case; case=> * /=. 
               rewrite compute_new_pc_opt_secret /=.
               instantiate (1:= fun '(_,_,_)=> _); reflexivity. }
             stir. 
             rewrite combine_extend3_nil3 filter_map_swap.
             set l := (X in map _ X); suff->: l = []; [done|subst l].
             erewrite filter_ext; cycle 1.
               { case=> *. instantiate (1:= fun '(_,_)=> _); reflexivity. }
             unshelve erewrite filter_ext; [exact xpred0|apply filter_false|].
             case=> //. }
           { stir. erewrite filter_ext; cycle 1.
               { case; case=> * /=. 
               instantiate (1:= fun '(_,_,_)=> _); reflexivity. }
           rewrite combine_extend3_nil1 combine_extend2_nil_r !map_map filter_map_swap.
           set l := (X in map _ X); suff->: l = []; [done|subst l]. (* This is a good stir rule *)
           unshelve erewrite filter_ext; [exact xpred0|apply filter_false|].
           case=> *; stir. }
         rewrite/sim_step; stir; f_equal; stir.
           { admit. }
           { if_easy_goals. } (* TODO: It's worth having this be a stir rule *)
         rewrite cmd_map_sim_app. 
         set l1 := (X in X ++ ?[y] = _ ++ ?y). set l2 := (X in _ ++ ?[y] = X ++ ?y); suff->: l1 = l2=> //; subst l1 l2.
         rewrite/zip/cmd_map_sim filter_map_swap map_map. symmetry.
         erewrite map_ext; [|case; case=> * /=; instantiate (1:= fun '(_,_,_) => _); reflexivity].
         erewrite filter_ext; [|case; case=> *; rewrite /sim_active; cbn; instantiate (1:= fun '(_,_,_) => _); reflexivity].
         set x :=(combine_extend3 _ _ _ _ _ _); pattern x; set P :=(X in X x); subst x.
         rewrite combine_extend3_swap23. move: (map Some (_ _ ist))=> ?. subst P; cbn beta.
         rewrite filter_map_swap map_map.
         erewrite map_ext; [|case; case=> * /=; instantiate (1:= fun '(_,_,_) => _); reflexivity].
         erewrite filter_ext; [|case; case=> *; cbn; instantiate (1:= fun '(_,_,_) => _); reflexivity].
         set (public _) as x; case newpce: x; subst x; cycle 1. (* TODO: ssr version of this? *)
           { erewrite filter_ext; cycle 1.
               { case; case=> ? x ?. rewrite /sim_active' /= Bool.orb_false_r.
               instantiate (1 := fun '(_,_,_) => _). reflexivity. }
           case: pub in rwt newpce *; cycle 1.
             { erewrite post_optcmd_stp_store_sec; [| eassumption]=> /=.
             pattern_eq_2 [(post_cmd_action _ _ (if _ then _ else rst))] [(post_cmd_action _ _ (if _ then _ else simst))] => [|->].
               { case: isatk; [apply: noninterfering_post_pre| apply: post_cmd_wf]=> //. } (* This pattern can be automated *)
             stir. set l1 := filter _ _. set l2 := repeat true _.
             suff: map (fun '(_,i,_) => i) l1 = l2; [move: l1 l2=> > <-; clear |subst l1 l2].
               { rewrite map_map; apply: map_ext=> - [] [] //. }

             move: (if _ then _ else _) (map Some _)=> ? ?.
             rewrite combine_extend3_splitr [combine_extend2 _ (repeat _ _) _ _]combine_extend2_swap;
             erewrite combine_extend2_map_l; [|instantiate (1 := (_,_)); reflexivity];
             rewrite -combine_extend3_splitr combine_extend3_splitl !map_map filter_map_swap map_map;
             erewrite filter_ext; [|case=> ?;case=> *; instantiate (1 := fun '(_,_) => _); reflexivity];
             erewrite map_ext; [|case=> ?;case=> *; instantiate (1 := fun '(_,_) => _); reflexivity];
             move: (X in combine_extend2 _ X _ _)=> ?.
             erewrite map_filter_combine_extend2_ind1.
             2,3: move=> *; instantiate (1:= fun _ => _); reflexivity. 2: done.
             rewrite map_id; clear; revert_hyp_type nat; elim=> //= *; f_equal=> //. }

           have ->: is_secret_guard rcmd = true by admit. (* TODO: lots of same as before *)
           rewrite combine_extend2_nil_l.
           stir. set l1 := filter _ _. set l2 := repeat true _.
           suff: map (fun '(_,i,_) => i) l1 = l2; [move: l1 l2=> > <-; clear |subst l1 l2]. (* I copied this *)
             { rewrite map_map; apply: map_ext=> - [] [] //. } (* I feel like this is going to be very similar to previous case *)
           pattern_eq_2 [post_cmd_action _ _ (_ _ (if isatk then _ else rst))]
                        [post_cmd_action _ _ (_ _ (if isatk then _ else simst))] => [| ->].
             { admit. }
           stir. set l1 := filter _ _. set l2 := repeat true _.
           suff: map (fun '(_,i,_) => i) l1 = l2; [move: l1 l2=> > <-; clear |subst l1 l2].
             { apply: map_ext=> - [] [] //. }

           move: (if _ then _ else _) (map Some _)=> ? ?.
           rewrite combine_extend3_splitr [combine_extend2 _ (repeat _ _) _ _]combine_extend2_swap;
           erewrite combine_extend2_map_l; [|instantiate (1 := (_,_)); reflexivity];
           rewrite -combine_extend3_splitr combine_extend3_splitl !map_map filter_map_swap map_map;
           erewrite filter_ext; [|case=> ?;case=> *; instantiate (1 := fun '(_,_) => _); reflexivity];
           erewrite map_ext; [|case=> ?;case=> *; instantiate (1 := fun '(_,_) => _); reflexivity];
           move: (X in combine_extend2 _ X _ _)=> ?.
           erewrite map_filter_combine_extend2_ind1.
           2,3: move=> *; instantiate (1:= fun _ => _); reflexivity. 2: done.
           rewrite map_id; clear; revert_hyp_type nat; elim=> //= *; f_equal=> //.  } (* I copied alot!! TODO: Cleanup *)
         case: pub in rwt newpce *; [| move=> /=;stir].
         have rcmd_grd: is_secret_guard rcmd = false by admit. (* Copied!! *)
         rewrite rcmd_grd.
         pattern_eq_2 [ (optcmd_stp_cnt _ (if _ then _ else rst)) ]
                      [ (optcmd_stp_cnt _ (if _ then _ else simst)) ] => [| <-].
           {  destruct rcmd => //. apply: clean_cmd_stp_cnt_pub_nf=> //. case: isatk; stir. }
         pattern_eq_2 [post_cmd_action _ _ (_ _ (if isatk then _ else rst))]
                      [post_cmd_action _ _ (_ _ (if isatk then _ else simst))] => [| ->].
           { admit. }
         rewrite combine_extend3_splitr. 
         move: (X in (map Some X)) (X in (repeat true X))=> *.
         erewrite map_filter_combine_extend2_ind1.
         2,3: case=> *; instantiate (1:= fun '(_,_) => _); reflexivity; done. 2: done.
         clear. erewrite map_ext; [|instantiate (1 := id); case=> //]. rewrite map_id.
         revert_hyp_type nat; revert_hyp_type Prog. 
         elim; [elim=> //= n ?; f_equal=> //|].
         move=> > ?; case=> /= *; [| f_equal; eauto].
         rewrite !filter_map_swap.
         erewrite filter_ext; [| move=> * /=; reflexivity].
         rewrite filter_true //.
    Admitted.
  End cook.

End extract_step_commute.
(* The theorem: 
CmbCmd. invariant holds.



*)


