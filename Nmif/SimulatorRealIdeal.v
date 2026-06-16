From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Combined Simulator CombinedExtract CoTrace IdlAtkPreds ControlledDowngrade.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Combined Simulator CombinedExtract CoTrace IdlAtkPreds ControlledDowngrade.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section bisim.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable adv : AdvNextStep (AtkStates := AtkStates).

  Notation sadv := (construct_simulator adv).

  Definition bisim_rel (s1 : Semantics.Cfg (AtkStates:=AtkStates))
      (s2 : Semantics.Cfg (AtkStates:=SimStates (AtkStates:=AtkStates))) : Prop :=
    exists cc, Invariant cc /\
      s1 = extract_one_cfg true (extract_2cfg cc) /\
      s2 = extract_one_cfg false (extract_2cfg cc).

  Fail Check "refactor - common extract full".
  Theorem simulator_bisim (c : Combined.Cfg (AtkStates:=AtkStates)) :
    Invariant c ->
    let: twocfg := extract_2cfg c in
    let: left_cfg := extract_one_cfg true twocfg in
    let: right_cfg := extract_one_cfg false twocfg in
    cfg_trace adv left_cfg  ≈ʷ  cfg_trace sadv right_cfg.
  Proof.
    rewrite/cfg_trace=> cinv.
    apply: (trace_wbisim _ _ _ _ bisim_rel); [| eexists; eauto].
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
              (extract_stutter_event adv sadv false ac1 ac2 rest cs1 cs2 (negbT r2))
          => Sc Se SSc SSe.
        right; left; split.
        * exists (cfg_step adv cc); split; [exact: Hinv'|].
          split; [rewrite -Sc Hcom // | rewrite -Hcom SSc //].
        * rewrite -Se Het -Hef SSe //.
      + (* only ac2 steps: skip_r *)
        move: (extract_step_cfg adv sadv false ac1 ac2 rest cs1 cs2 r2)
              (extract_step_event adv sadv false ac1 ac2 rest cs1 cs2 r2)
              (extract_stutter_cfg adv sadv true ac1 ac2 rest cs1 cs2 (negbT r1))
              (extract_stutter_event adv sadv true ac1 ac2 rest cs1 cs2 (negbT r1))
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

Section sim_trace_eq.
  Import Attacker Semantics.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Theorem simulator_trace_eq p a :
    WellFormedProg ptlbl p -> 
    forall inp, ⟦ p | a ⟧ inp ≈ʷ ⟦ p | (construct_full_simulator p a) ⟧ inp.
  Proof.
    move=> wt init_st.
    rewrite/⟦_|_⟧ /=.
    pose cc := Combined.init_cfg p (init a) init_st.
    have ccinv: Invariant cc; eauto using init_inv.
    let t := open_constr:(_) in pattern_eq [init_cfg p (init _) _] with t=> [|->]; 
      [|let t := open_constr:(_) in pattern_eq [init_cfg p (simulator_init p _) _] with t=> [|->]]; 
      [..|apply/simulator_bisim/ccinv].
    1,2: subst cc=> /=; clear=> /=. 
    1,2: rewrite/cmd_map/cmd_map_sim !map_map !filter_map_swap /is_running filter_true // map_map //.
  Qed.

End sim_trace_eq.


Section sim_idlatkrest.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variables (p: Prog) (a: Attacker).

  Notation AtkStates := (States a).
  Notation CombCfg := (Combined.Cfg (AtkStates := AtkStates)).
  Notation ainit := (Attacker.init a).
  Notation astep := (Attacker.step a).

  Ltac inv_auto := auto using cfg_step_inv, erase_filter_inv.
  Theorem sim_idlatkrest :
    WellFormedProg ptlbl p ->
    IdlAtkDowngradeRestr p (construct_full_simulator p a).
  Proof.
    move=> wt.
    rewrite/IdlAtkDowngradeRestr.
    let t := open_constr:(?[ast_trans]) in pose ast_trans:= t; exists ast_trans.
    let t := open_constr:(?[ast_corr]) in pose ast_corr:= t; exists ast_corr.
    move=> /= inp > rch.
    pose inv c := [elaborate (exists comb : CombCfg,  Invariant comb /\ (c = extract_one_cfg false (extract_2cfg comb)))]. (* TODO: Lemmas *)
    set init := (X in reachable _ X _) in rch. set final := (X in reachable _ _ X) in rch.
    have: inv final.
      { apply: reachable_invariant; [..|exact: rch].
      - rewrite {}/inv /init.  exists (Combined.init_cfg p ainit inp).
        split; auto using init_inv.
        rewrite /= /cmd_map !map_map filter_map_swap /= /is_running filter_true.
        rewrite/cmd_map_sim filter_map_swap !map_map //. 
      - clear. rewrite{}/inv=> _ [cmb] [cmbinv] ->.
        exists (cfg_step astep (erase_filter_cfg false cmb)).
        split; inv_auto.
        rewrite -extract_step_commute ?extract_erase_commute; inv_auto.
        move: (extract_2cfg _)=> ?.
        rewrite extract_one_erase_idem erase_filter_step_commute //. }
    clear rch init wt. rewrite{}/inv {}/final. clear. case.
    case=> - [? idlst ? ? lst] [].
    rewrite/Invariant=> - [] lstinv.
    rewrite/StateInv=> _.
    rewrite/extract_2cfg/extract_one_cfg.
    case. pattern_focus [X in X -> _]=> P.
    rewrite/cmd_map map_map. erewrite map_ext; [| move=> ? /=; reflexivity]. 
    subst P; cbn beta.
    move=> lsteq -> .
    rewrite filter_map_swap /= in lsteq. (* This can be somewhere else *)
    move: lsteq. 
    move e: (filter _ _)=> flt; move: e; case: flt=> // hd rst flte.
    case=> /esym ? -> _.
    pattern_focus [cmd_map_sim _]=> P.
    rewrite/cmd_map_sim/is_running/= in flte *.
    set fsact := (filter sim_active _).
    have: fsact = hd :: tl fsact; [| move=> ->; move: (tl _)=> ? ].
      {subst fsact.
      move: flte. revert_hyp_pat (_ = true); clear=> hdtr.
      elim: lst=> //= > ih.
      case e: sim_active=>//= => [ [] -> // |].
      case: isSome=> // - [] x; rewrite -> x in *; congruence. }
    rewrite{}/P {fsact} map_cons.
    have: CmbCmdInv hd.
      { move:flte lstinv; clear.
      set fltlst := filter _ _=> e1 e2.
      suff: [elaborate Forall CmbCmdInv fltlst]; [rewrite e1; Forall_inv_toph; done|subst fltlst].
      exact: Forall_filter. }
    clear. case: hd=> >.
    rewrite/CmbCmdInv/TypeInv=> - [] [] ? ? _. Combined.local_cook=> asteq.
    split. 
    - rewrite -surjective_pairing.
      set simst' := sim_post _ _ _. set f_ast := ast_trans _. set cmd := (X in match X with | Some _ => _ | _ => _ end).
      pose ctrldecl := [elaborate oapp extract_controlled_declassify None cmd].
      suff:  match ctrldecl with | Some (from, to) => simst' = f_ast (idlst from) | _ => forall garbage, simst' = f_ast garbage  end.
        { clear. move: ast_trans f_ast simst'=> > _ >. rewrite{}/ctrldecl.
        move e: (oapp _ _ _)=> [[? ?]| ]; [|clear;case: cmd=> // - [] // [] //].
        move: e=>/extr_decl_opt=> -[] -> //. }
      rewrite {}/ctrldecl {}/cmd {}/simst' {}/f_ast {}/ast_trans.
      instantiate (ast_trans :=( fun st val => (sim_post astep st (fun => val)))).
      move is_decl : (oapp _ _ _)=> x; move: x is_decl; case=> [[src dst] ? | ? ? ]; rewrite {}asteq; cycle 1.
        { move: (optcmd_stp_store _ _)=> ?.
        rewrite/sim_post.
        pattern_eq_2 [sim_step _ _ _ _ _ _] [sim_step _ _ _ _ _ _]=> [|-> //].
        case pubpc: (public _)=> //.
        rewrite/sim_step. 
        pattern_eq [oapp extract_controlled_declassify _ _] with None=> [|-> //].
        revert_hyp_pat (if _ then _ else _). case untr:  (untrusted _); [move=> _|move=> -> //].
        revert_hyp_pat [Label, (public _ = _), (untrusted _ = _), (_ ⊢ _)]; clear.
        case=> ? ? /= -> ->.
        move e: (oapp _ _ _)=>  x; move: e; case: x=> // - [] > /extr_decl_wf_opt /[apply] //. }
      revert_hyp_pat [Label, (_ ⊢ _), (_ = _), (if _ then _ else _)]; clear.
      case=> - []; [move=> > _ + +  /ltac:(exfalso)=> /extr_decl_wf_opt /[apply] //|].
      move=> ? + + /ltac:(dotop [cbn])=> -> /[swap] /[dup] + /[swap] /[dup].
      move=> /extr_decl_wf_opt /[apply] - [] ->; clear=> wt decl.
      set s1 := (optcmd_stp_store _ _). set s2 := (fun => idlst src).
      have: s1 dst = s2 dst; [subst s1 s2| move: s1 s2=> ? ?].
        { move=> /=. move: (decl) => /extr_decl_opt=> - [->] _ /=. 
        exact:update_to_store_same. } (* Finisher? *)
      move=> dsteq.
      rewrite/sim_post.
      pattern_eq_2 [sim_step _ _ _ _ _ _] [sim_step _ _ _ _ _ _]=> [|-> //].
      rewrite/sim_step decl dsteq //. 
   - split. 
      { rewrite/sim_pre {}asteq {}/ast_corr.
      unshelve instantiate (ast_corr :=  _).
        { let x := open_constr:(fun ast hd isatk sim_st => ?[ast_corr]) in 
        refine  (fun '(mk_simstate ast sim_st prg) =>   if prg isn't (hd, isatk) :: _ then None else  x ast hd isatk sim_st ). }
      move=> /=.
      unshelve instantiate (ast_corr :=  _).
        { refine (if oapp extract_controlled_endorse None hd is Some (to,from) then Some (to, ?[ast_corr]) else None); shelve.  }
      move=> /=.
      move endeq: (oapp extract_controlled_endorse _ _)=> [ [? ?] | //].
      congr update_to_store. move: (if _ then _ else _)=> ?. reflexivity. } (* What did I just do lmao *)
     set cmd := (X in match X with Some _ => _ | _ => _ end). set astcorval := (ast_corr _).
     pose ctrlend := [elaborate oapp extract_controlled_endorse None cmd].
     suff:  match ctrlend with 
       | Some (from, to) => if astcorval is Some (var, _) then  var = from else  True
       | _ => astcorval = None 
       end; subst ctrlend astcorval.
       { move: cmd ast_corr=> c ?; clear.
       case: c=> // - [] // [] // >. 
       move e: (oapp _ _ _)=> [ [? ?] | ?];[|rewrite e //].
       move: e=> /extr_endorse_eq=> - [] [->] _ _.
       case: (X in match X with | None => True | _ => _ end)=> // - []//. }
     rewrite {}asteq {}/ast_corr {}/cmd /=.
     move ende: (oapp _ _ _)=> [[? ?] | ].
       { revert_hyp_pat [Label, (_ ⊢ _), (_ = _), (if _ then _ else _)]; clear.
       case=> + [] //=; case; [move=> + _ _ | move=> + + e; rewrite {}e=> + ->  //].
       move ?: (oapp _ _ _)=>  [[?] | ] //.
       move/extr_endorse_wf_opt/[apply]=> //. }
     pattern_eq [oapp _ _ _] with None=> [|-> //].
     revert_hyp_pat [Label, (_ ⊢ _), (_ = _), (if _ then _ else _)]; clear.
     case=> + [] //= => - [+ _ _| + + -> //].
     move ?: (oapp _ _ _)=> [[?] | //].
     move=>/extr_endorse_wf_opt /[apply] //.
  Qed.

End sim_idlatkrest.


(* TODO: Where should this be defined actually? *)
Section fairness.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variables (p: Prog) (areal aideal: Attacker).
  Notation TwoCfg := (TwoCfg (AtkStates1 := (States areal)) (AtkStates2 := States aideal)).

  Notation cfg_init_fn inp := (init_twocfg p inp (init areal) (init aideal)).
  Notation twostep := (twostep (Attacker.step areal) (Attacker.step aideal)).

  Definition FairIdlAtk := forall inp, 
    let: init_cfg := cfg_init_fn inp in 
    forall final_cfg, 
      reachable twostep init_cfg final_cfg ->
      let: (cmdlst, _, _) := final_cfg in
      let: pred := 
        fun '(mk_atkcmd ratk rcmd,mk_atkcmd iatk icmd) => 
          (iatk -> icmd || rcmd || ratk)  in (* I could do iatk => ..  \/ .. \/ .. too *)
      Forall pred cmdlst.
End fairness.

Section sim_fair.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variables (p: Prog) (a: Attacker).

  Notation AtkStates := (States a).
  Notation CombCfg := (Combined.Cfg (AtkStates := AtkStates)).

  Theorem sim_fair :
    WellFormedProg ptlbl p ->
    FairIdlAtk p a (construct_full_simulator p a).
  Proof.
    pose inv c := [elaborate (exists comb : CombCfg, Invariant comb /\ (c = (extract_2cfg comb)))]. (* TODO: Lemmas. Maybe rename Invariant to something else, which will help me flag *)
    move=> wt.
    rewrite/FairIdlAtk=> inp ? rch.
    set init := (X in _ _ X _) in rch.  set final := (X in _ _ _ X) in rch.
    have: inv final; subst inv init final. (* I think that these only appear in this file, so we can do it.. *)
      { apply: reachable_invariant rch. 
        - exists (Combined.init_cfg p (init a) inp).
          split; auto using init_inv. (* Lemma.. *)
          rewrite/init_twocfg/extract_2cfg /=.
          do ! cnstrct_eq_gl.
          1: rewrite/cmd_map map_map.
          2: rewrite/cmd_map_sim filter_map_swap /= map_map filter_true.
          1,2: apply: map_ext=> //. 
        - move=> ? [] cmb [] inv ->.
          exists (cfg_step (Attacker.step a) cmb).
          split; [exact: cfg_step_inv|].
          exact: extract_step_commute. }
    clear=> /= - [] [] ? clst [].
    rewrite/Invariant=> - [] + _.
    rewrite/CmbCmdInv=> inv -> /=.
    rewrite/cmd_map Forall_map.
    apply: Forall_impl inv. clear.
    rewrite/TypeInv/ActiveInv. 
    case=> /= rcmd ratk > [] [] _ _. 
    case: ratk; case: rcmd; Util.local_cook=> ?; Util.local_cook.
  Qed.

End sim_fair.

