From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section bisim.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable adv : AdvNextStep AtkStates.


  Notation sadv := (construct_simulator adv).

  Definition bisim_rel (s1 : Semantics.Cfg (AtkStates:=AtkStates))
      (s2 : Semantics.Cfg (AtkStates:=SimStates (AtkStates:=AtkStates))) : Prop :=
    exists cc, Invariant cc /\
      s1 = extract_one_cfg true (extract_2cfg cc) /\
      s2 = extract_one_cfg false (extract_2cfg cc).

  Fail Check "refactor".
  Theorem simulator_bisim (c : Combined.Cfg (AtkStates:=AtkStates)) :
    Invariant c ->
    let: twocfg := extract_2cfg c in
    let: left_cfg := extract_one_cfg true twocfg in
    let: right_cfg := extract_one_cfg false twocfg in
    trace adv left_cfg  ≈  trace sadv right_cfg.
  Proof.
    rewrite/trace=> cinv.
    apply: (trace_bisim _ _ _ _ bisim_rel); [| eexists; eauto].
    move=> s1 s2 [cc [Hinv [-> ->]]].
    have Hrun : Forall (fun '(a,b)=> is_running a || is_running b) (extract_2cfg cc).1.1.
    { move: (extract_step_running cc Hinv); case: (extract_2cfg cc) => [[l z1] z2] /= H; exact: H. }
    move: (extract_step_commute adv cc Hinv)=> Hcom.
    move: (extract_step_commute_event adv cc Hinv)=> Hev.
    move: (cfg_step_inv adv cc Hinv)=> Hinv'.
    have Het : extract_one_event adv sadv true (extract_2cfg cc) = Combined.cmb_event adv cc.
    { rewrite /extract_one_event Hev //. }
    have Hef : extract_one_event adv sadv false (extract_2cfg cc) = Combined.cmb_event adv cc.
    { rewrite /extract_one_event Hev //. }
    have [cl [cs1 [cs2 Ec]]] : exists cl cs1 cs2, extract_2cfg cc = (cl, cs1, cs2).
    { case: (extract_2cfg cc)=> [[l z1] z2]; exists l, z1, z2; reflexivity. }
    case: cl Ec => [Ec | [ac1 ac2] rest Ec].
    - (* empty: both terminated, match with blank events *)
      rewrite Ec in Hcom Het Hef. rewrite Ec.
      left; split.
      + exists cc; split; [exact: Hinv|].
        rewrite Ec /=; split=> //.
      + rewrite /= //.
    - rewrite Ec in Hcom Het Hef. rewrite Ec.
      rewrite Ec /= in Hrun.
      have Hor := Forall_inv Hrun.
      case r1: (is_running ac1); case r2: (is_running ac2).
      + (* both run: match *)
        move: (extract_step_cfg adv sadv true ac1 ac2 rest cs1 cs2 r1)
              (extract_step_event adv sadv true ac1 ac2 rest cs1 cs2 r1)
              (extract_step_cfg adv sadv false ac1 ac2 rest cs1 cs2 r2)
              (extract_step_event adv sadv false ac1 ac2 rest cs1 cs2 r2)
          => Dtc Dte Dfc Dfe.
        left; split.
        * exists (cfg_step adv cc); split; [exact: Hinv'|].
          split; [rewrite -Dtc Hcom // | rewrite -Dfc Hcom //].
        * rewrite -Dte -Dfe Het Hef //.
      + (* only ac1 steps: skip_l *)
        move: (extract_step_cfg adv sadv true ac1 ac2 rest cs1 cs2 r1)
              (extract_step_event adv sadv true ac1 ac2 rest cs1 cs2 r1)
              (extract_stutter_cfg adv sadv false ac1 ac2 rest cs1 cs2 (negbT r2))
              (extract_nrun_event adv sadv false ac1 ac2 rest cs1 cs2 (negbT r2))
          => Sc Se SSc SSe.
        right; left; split.
        * exists (cfg_step adv cc); split; [exact: Hinv'|].
          split; [rewrite -Sc Hcom // | rewrite -Hcom SSc //].
        * rewrite -Se Het -Hef SSe //.
      + (* only ac2 steps: skip_r *)
        move: (extract_step_cfg adv sadv false ac1 ac2 rest cs1 cs2 r2)
              (extract_step_event adv sadv false ac1 ac2 rest cs1 cs2 r2)
              (extract_stutter_cfg adv sadv true ac1 ac2 rest cs1 cs2 (negbT r1))
              (extract_nrun_event adv sadv true ac1 ac2 rest cs1 cs2 (negbT r1))
          => Sc Se SSc SSe.
        right; right; split.
        * exists (cfg_step adv cc); split; [exact: Hinv'|].
          split; [rewrite -Hcom SSc // | rewrite -Sc Hcom //].
        * rewrite -Se Hef -Het SSe //.
      + (* neither runs: contradicts Hrun head *)
        move: Hor; rewrite /= r1 r2 //.
  Qed.
  Print Assumptions simulator_bisim.
End bisim.
