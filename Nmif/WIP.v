From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Notation Cfg := Semantics.Cfg.

Section sim_restriction.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {States: Type}.

  Variable (adv : AdvNextStep States)  (initc : Cfg (AtkStates:= States)).

  Notation step := (step adv).
  Notation acmd_step := (acmd_step adv).
  Notation pre_cmd_action := (pre_cmd_action adv).
  
  Definition idealatk_restriction: Prop :=
    exists ast_trans : States -> Vals (* declassified value *) -> (States * nat) (* ast , substeps *),
    exists ast_corr : States -> option (Vars * Vals) (* endorsed value *),

    forall cmd rstcmd store ast, 
      let: acmd := mk_atkcmd true cmd in  
      let: state := (store, ast) in
      let: c := ((acmd :: rstcmd), state) in
      reachable step initc c  ->

      let: learner_restriction :=
        let: atk_output := 
           let: (_, (_, ast'), atk_substeps) := acmd_step acmd state in
           (ast', atk_substeps) in
        if cmd is Some (assign (declassify from to)) then atk_output = ast_trans ast (store from) else
        forall garbage, atk_output = ast_trans ast garbage in
      
      let: corruptor_restriction := 
        let: ast_corr_output := ast_corr ast in

        let: ast_corr_match :=
          pre_cmd_action ast store = 
            if ast_corr_output isn't Some (var, val) then store 
            else update_to_store store var val in
         
        let: ast_corr_restriction :=
          if cmd isn't Some (assign (endorse from to)) then ast_corr_output = None else
          if ast_corr_output is Some (var, val) then var = from else
          True in
        ast_corr_match /\ ast_corr_restriction in

      learner_restriction /\ corruptor_restriction.
End sim_restriction.

Section sim_restriction.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {States: Type}.

  Variable (adv : AdvNextStep States).

  Import Util.List VarValStore.Notations.

  Ltac inv_auto := auto using cfg_step_inv, erase_filter_inv.
  Lemma sim_learn_restiction c: 
    (exists comb, (Invariant comb /\ c = extract_one_cfg false (extract_2cfg comb))) ->
    idealatk_restriction (construct_simulator adv) c.
  Proof.
    move=> cinv. pattern c in cinv. (* Normal rocq tactic *) revert cinv. set inv := (X in (X c) ->_)=> /= cinv.
    rewrite/idealatk_restriction. 
    let t := open_constr:(?[ast_trans]) in pose ast_trans:= t; exists ast_trans.
    let t := open_constr:(?[ast_corr]) in pose ast_corr:= t; exists ast_corr.
    move=> cmd > /=. 
    set final := (X in reachable _ _ X)=> rch. 
    have: inv final.
      { apply:reachable_invariant; [eassumption| |eassumption].
      clear. rewrite{}/inv=> twocfg [comb [invcomb ->]].
      exists (cfg_step adv (erase_filter_cfg false comb)).
      split; inv_auto.
      rewrite -extract_step_commute ?extract_erase_commute; inv_auto.
      move: (extract_2cfg _)=> ?.
      rewrite extract_one_erase_idem erase_filter_step_commute //. }
    subst inv final=> {rch} /= - []; clear cinv c.
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
      instantiate (ast_trans :=( fun st val => (sim_post adv st (fun => val)))).
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

End sim_restriction.
