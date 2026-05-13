From Stdlib Require List ssreflect ssrfun ssrbool. 
Import List ListNotations ssreflect ssrfun ssrbool.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics Combined Simulator.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics Tacs.Cook.

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
    let: atk_st := if isatk is true then learner adv atk_st st else atk_st in 
    let: steps := if isatk is true then  substeps adv atk_st else 0 in
    (prog, (st, atk_st), steps).
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
  Import Simulator.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable adv : (AdvNextStep AtkStates).

  Notation CombCfg := Combined.Cfg.
  Notation comb_step := (Combined.cfg_step adv).
  Notation extract_2cfg := (extract_2cfg (AtkStates := AtkStates)).
  Notation step := (step adv (construct_simulator adv)).

  Theorem extract_step_commute c:
    Combined.Invariant c ->
    step (extract_2cfg c) = extract_2cfg (comb_step c).
  Proof.
    case: c => [[rst ist simst atkst] [|cmbcmd cmblst']] inv.
    1:{ done. }
    1:{ case: cmbcmd inv => rcmd ratk icmd pclbl inv.
        rewrite /extract_2cfg /cmd_map /cmd_map_sim /=.
        f_equal; [f_equal | ].
        1:{ rewrite map_app.
            f_equal.
            1:{ move: inv; case: ratk; case ep: (public pclbl); move=> inv /=.
                1:{ idtac "==CASE TT=="; show_state. admit. }
                1:{ idtac "==CASE TF=="; show_state. admit. }
                1:{ idtac "==CASE FT=="; show_state. admit. }
                1:{ idtac "==CASE FF=="; show_state. admit. } } }
        1:{ idtac "==SUBGOAL 2=="; show_state. admit. } }
  Admitted.

End extract_step_commute.
(* The theorem: 
CmbCmd. invariant holds.



*)


















