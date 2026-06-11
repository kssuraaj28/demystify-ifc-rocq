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
      Print step.

  Notation step := (step adv).
  
  #[refine] Definition idealatk_restriction: Prop :=
    exists ast_trans : States -> Vals (* declassified value *) -> States,  
    forall cmd rstcmd store ast, 
      let: acmd := mk_atkcmd true cmd in 
      let: c := ((acmd :: rstcmd), (store,ast)) in
      reachable step initc c  ->

      (* Learner restriction *)
      let: (_, (x, ast')) := step c in
      match cmd with (* We use the same function because we want to confuse the ideal attacker *)
      | Some (assign (declassify from to)) => ast' = ast_trans ast (store from) 
      | _ => forall garbage, ast' = ast_trans ast garbage
      end 

      /\

      True.
  Defined.
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
    let t := open_constr:(?[ast_trans]) in pose f:= t; exists f.
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
    set simst' := sim_post _ _ _. set f_ast := f _. set cmd := (X in match X with | Some _ => _ | _ => _ end).
    pose ctrldecl := [elaborate oapp extract_controlled_declassify None cmd].
    split. 
    - suff:  match ctrldecl with | Some (from, to) => simst'.1 = f_ast (idlst from) | _ => forall garbage, simst'.1 = f_ast garbage  end.
        { clear. move:f f_ast simst'=> > _ >. rewrite{}/ctrldecl.
        move e: (oapp _ _ _)=> [[? ?]| ]; [|clear;case: cmd=> // - [] // [] //].
        move: e=>/extr_decl_opt=> -[] -> //. }
      rewrite {}/ctrldecl {}/cmd {}/simst' {}/f_ast {}/f.
      instantiate (ast_trans :=( fun st val => (sim_post adv st (fun => val)).1)).
      move is_decl : (oapp _ _ _)=> x; move: x is_decl; case=> [[src dst] ? | ? ? ]; congr _.1; rewrite {}asteq; cycle 1.
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
   - admit.
  Admitted.

End sim_restriction.
