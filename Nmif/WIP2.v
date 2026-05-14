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
    Definition sim_active (c: CmbCmd) : bool :=
      let: is_rattack := real_atk_bit c in 
      let: is_public_rcmd := 
        public (pc_lbl c) && if (real_cmd c) is None then false else true in 
      is_rattack || is_public_rcmd.
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


Ltac show_state :=
  idtac "==HYPS==";
  (try (match reverse goal with H : ?T |- _ => idtac H ":" T; fail end));
  match goal with |- ?G => idtac "==GOAL==" G end;
  idtac "==END==".

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
      -- congr (_ ++ _); stir. (* TODO: Forward reasoning *) 
         rewrite/cmd_map.
         set l1 := (X in map _ X = _).
         set l2 := (X in _ = map _ X).
         suff: l1 = map (fun c => (real_cmd c, real_atk_bit c,  ideal_cmd c, sim_active c)) l2;
           [move=> ->; rewrite map_map //| subst l1 l2]. (* TODO: This could be lemma / rewrite rule *)
         rewrite/sim_step. stir.
         admit.
         (*
           ++ rewrite map_repeat. 
              rewrite repeat_length; stir.
              rewrite map_proj_map_mk. (* This is pretty dogshit *)
              *)
         
      -- congr(_,_); stir.
         move: isatk untr pub rcmd rwt iwt.
         (case; case; case; (case=> [rcmd|])); stir=> rwt iwt.
         { rewrite/sim_step; stir.
           erewrite noninterfering_post_clean_pre;[ |eassumption | symmetry; eassumption ].
           f_equal.
           rewrite cmd_map_sim_app.
           f_equal.


    Admitted.
  End cook.

End extract_step_commute.
(* The theorem: 
CmbCmd. invariant holds.



*)


