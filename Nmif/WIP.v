From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace.
Import Tacs Util Util.List VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Notation Cfg := Semantics.Cfg.

(* Moved *)
Section idlatk_pred.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variables (p: Prog) (a: Attacker).

  Notation AtkStates := (States a).
  Notation ainit := (Attacker.init a).
  Notation astep := (Attacker.step a).
  Notation step := (step astep).
  Notation acmd_step := (acmd_step astep).
  Notation pre_cmd_action := (pre_cmd_action astep).
  Notation init_cfg_fn inp := ((Semantics.init_cfg p ainit inp)). 

  (* TODO: Definition vs Notation? *)
  Notation IdealAstTrans := (AtkStates -> Vals (* declassified value *) -> (AtkStates * nat) (* ast , substeps *)).
  Notation IdealAstCorr := (AtkStates -> option (Vars * Vals) (* endorsed value *)).

  Definition IdlAtkDowngradeRestr : Prop :=
    exists (ast_trans: IdealAstTrans)  (ast_corr : IdealAstCorr),
    forall inp, 
      let: init_cfg := init_cfg_fn inp in
      forall cmd rstcmd store ast, 
      let: acmd := mk_atkcmd true cmd in  
      let: state := (store, ast) in
      let: c := ((acmd :: rstcmd), state) in
      reachable step init_cfg c  ->

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
End idlatk_pred.


(* Should go to sim.. *)
Section wt_idlatk_rest.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variables (p: Prog) (a: Attacker).

  Notation AtkStates := (States a).
  Notation CombCfg := (Combined.Cfg (AtkStates := AtkStates)).
  Notation ainit := (Attacker.init a).
  Notation astep := (Attacker.step a).

  Ltac inv_auto := auto using cfg_step_inv, erase_filter_inv.
  Theorem wt_idlatk_rest :
    WellFormedProg ptlbl p ->
    IdlAtkDowngradeRestr p (construct_full_simulator p a).
  Proof.
    move=> wt.
    rewrite/IdlAtkDowngradeRestr.
    let t := open_constr:(?[ast_trans]) in pose ast_trans:= t; exists ast_trans.
    let t := open_constr:(?[ast_corr]) in pose ast_corr:= t; exists ast_corr.
    move=> /= inp > rch.
    pose inv c := [elaborate (exists comb : CombCfg,  Invariant comb /\ (c = extract_one_cfg false (extract_2cfg comb)))].
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

End wt_idlatk_rest.


Section semantic_preds.
  Import Noninterference VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).

  Variable adv_step : AdvNextStep.

  (* TODO: Am i respective these prop naming rules? *)
  Definition Passive : Prop :=
    let: corr_fn :=  pre_cmd_action adv_step in
    forall ast store, corr_fn ast store = store.

  Definition Nonmauling : Prop :=
    let: corr_fn :=  pre_cmd_action adv_step in
    exists nm_corr_fn : AtkStates -> StoreView,
    forall ast store, corr_fn ast store = ⟨ (nm_corr_fn ast)  → store ⟩.
  
  Definition Incurious : Prop :=
    forall st,
    let: learn_fn :=  post_cmd_action adv_step st in
    Noninterfering id learn_fn id.  (* Maybe I should just define and write constant? *)


  Definition NMIFRestr :=  Nonmauling.
  Definition TERestr :=  Nonmauling /\ Incurious.
  Definition RDRestr := Passive.
  Definition NIRestr := Passive /\ Incurious.
End semantic_preds.

Section atk_step_record_update.
  Import VarValStore.Notations Noninterference Util.DecEq.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).

  Notation ReplCorrInp := (AtkStates -> option (Vars * Vals) (* endorsed value *)).

  Obligation Tactic := try easy.
  Program Definition replace_corruptor
      (adv : AdvNextStep) (corr : ReplCorrInp ) : AdvNextStep := {|
    pre_cmd_action  := fun ast store =>
      if corr ast is Some (var, val) then
        (if is_untrusted var then update_to_store store var val else store)
      else store;
    pre_cmd_event   := pre_cmd_event adv;
    post_cmd_action := post_cmd_action adv;
    post_cmd_wf     := post_cmd_wf adv;
  |}.
  Next Obligation.
    move=> ? corr ast /= st. case e: (corr ast)=> [[var val]|] //.
    case eu: (is_untrusted var)=> //.
    apply: update_storeview_nochange. rewrite /is_trusted eu //.
  Qed.
  Next Obligation.
    move=> ? corr ast /=. rewrite /Noninterfering=> i1 i2 heq.
    case: (corr ast)=> [[var val]|]; [|exact: heq].
    case: (is_untrusted var); [exact: update_same_varval heq | exact: heq].
  Qed.

  Lemma replace_corruptor_nonmauling
      (adv : AdvNextStep) (corr : ReplCorrInp):
      Nonmauling (replace_corruptor adv corr).
  Proof.
    rewrite/Nonmauling. eexists.
    rewrite /pre_cmd_action/replace_corruptor=> ast store.
    instantiate (1 := fun ast => if corr ast is Some (var, val) then _ else _).
    move e: (corr _)=> [ [var val] | ]; rewrite {}e /=; [|instantiate (1 := fun _ => None); done].
    instantiate (1 := if is_untrusted var then _ else _).
    case e: (is_untrusted _); [|instantiate (1 := fun _ => None); done].
    rewrite/⟨ _ → _ ⟩/update_to_store.
    instantiate (1 := fun var' => if var =? var' then _ else _).
    apply: store_eq_ext=> v.
    case: (var =? v); [|instantiate (1 := None);done].
    instantiate (1 := Some _); done.
  Qed.

  Program Definition remove_corruptor (adv : AdvNextStep) : AdvNextStep := {|
    pre_cmd_action  := fun _ store => store;
    pre_cmd_event   := pre_cmd_event adv;
    post_cmd_action := post_cmd_action adv;
    post_cmd_wf     := post_cmd_wf adv;
  |}.


  Notation ReplLrnInp := (AtkStates -> (AtkStates * nat)).
  (* Record update!! *)


  Program Definition replace_learner
      (adv : AdvNextStep) (learn : AtkStates -> (AtkStates * nat)) : AdvNextStep := {|
    pre_cmd_action  := pre_cmd_action adv;
    pre_cmd_event   := pre_cmd_event adv;
    post_cmd_action := fun ast _ => learn ast;
    pre_cmd_wf_int  := pre_cmd_wf_int adv;
    pre_cmd_wf_conf := pre_cmd_wf_conf adv;
  |}.

End atk_step_record_update.

Section ts_restr_implication.
  Import VarValStore.Notations Util.DecEq Util.DecEq.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variable (adv : Attacker) (prog : Prog).
  Variable noend nodecl : bool.

  Notation adv_init := (Attacker.init adv).
  Notation adv_step := (Attacker.step adv).

  Notation adv_restr adv_step := 
    (match noend, nodecl with
      | true, true => NIRestr adv_step
      | true, false => RDRestr adv_step
      | false, true => TERestr adv_step
      | false, false => NMIFRestr adv_step
    end).
  
  Notation witness_constr adv_step corr_fn learn_fn :=
    (match noend, nodecl with
      | true, true => replace_learner (remove_corruptor adv_step) (fun st => learn_fn st val_ne)
      | true, false => remove_corruptor adv_step
      | false, true => replace_learner (replace_corruptor adv_step corr_fn) (fun st => learn_fn st val_ne)
      | false, false => replace_corruptor adv_step corr_fn
    end).

  Notation CmdRestr  :=
    (fun cmd => match noend, nodecl with
      | true, true => 
         match cmd with
         | (assign(endorse _ _)) | (assign(declassify _ _))  =>  False
         | _ => True
         end
      | true, false => 
         match cmd with
         | (assign(endorse _ _)) => False
         | _ => True
         end
      | false, true => 
         match cmd with
         | (assign(declassify _ _)) => False
         | _ => True
         end
      | false, false => True
    end).

  (*Notation ProgRestr := (Forall CmdRestr).  This is tricky *)
  Notation CfgListRestr cmd := 
    (let: (lst, st) := cmd  in 
    if lst isn't (mk_atkcmd _ (Some cmd )) :: _ then True else
    CmdRestr cmd).
  Check CfgListRestr _.

  (* TODO: Copy? *)
  Notation init_cfg_fn inp := ((Semantics.init_cfg prog adv_init inp)). 


  Definition RuntimeCmdRestr :=
    (forall inp cfg, 
      reachable (step adv_step) (init_cfg_fn inp) cfg ->
      CfgListRestr cfg).

  Lemma ts_sem_impl':
    IdlAtkDowngradeRestr prog adv ->
    RuntimeCmdRestr ->
    exists adv_step', adv_restr adv_step' /\
    forall inp cfg, 
      reachable (step adv_step) (init_cfg_fn inp) cfg ->
      step adv_step cfg = step adv_step' cfg /\ event adv_step cfg = event adv_step' cfg.
  Proof.
    rewrite /IdlAtkDowngradeRestr/NMIFRestr/RDRestr/TERestr/NIRestr.
    move=> - [trns] [wt] idlrst synrst.
    exists (witness_constr adv_step wt trns).
    split.
      { move: noend nodecl=> [] [] //; [split|]=> //; exact: replace_corruptor_nonmauling. }
    move=> inp [] + [str states] => - [] // [] [] // cmd ?.
    move=> /[dup]. 
    move: synrst idlrst => + /[swap]=> /[apply] + /[apply] cmdrest.
    case=> nodecl' [] precmdeq  noend'.
    rewrite /event/step.
    pattern_eq_2 [acmd_step _ _ _] [acmd_step _ _ _]; [|clear; case: noend; case: nodecl=> -> //].
    rewrite/acmd_step -!surjective_pairing in nodecl'.
    rewrite/acmd_step.
    pattern_eq_2 [pre_cmd_action _ _ _] [pre_cmd_action _ _ _]; cycle 1. 
      { move=> <- {precmdeq}.
      pattern_eq_2 [post_cmd_action _ _ _] [post_cmd_action _ _ _]=> [|-> //].
      move: noend nodecl cmdrest nodecl'. 
      clear=> - [] [] //; case: cmd => //= - [] // [] //. } (* Very interesting that you need //= *)
    move: (pre_cmd_wf_int adv_step)=>/(_ states str).
    rewrite {}precmdeq /= in nodecl' *.
    case: noend cmdrest=> /= cmdrest.
      { suff: wt states = None; [move=> -> _; clear; case: nodecl=> //|].
      move: noend' cmdrest; clear.
      case: nodecl; case: cmd=> // - [] // [] //. } 
    move wte: (wt _)=> [ [vr vl] |]; move: wte; clear; case: nodecl=> /= -> //.
    1,2: case untr : is_untrusted=> // wf. (* TODO: Lemma *)
    1,2: suff: (str vr = vl); [move=> <-; exact: update_to_store_id|].
    1,2: move: wf=> /equal_f /(_ vr).
    1,2: rewrite/⟨_|_⟩ /is_trusted untr /=.
    1,2: case=> <-;  exact: update_to_store_same. 
  Qed.
  
  Lemma ts_sem_impl:
    IdlAtkDowngradeRestr prog adv ->  RuntimeCmdRestr ->
    exists adv', adv_restr (Attacker.step adv') /\
    forall inp, ⟦ prog | adv  ⟧ inp ≈ˢ ⟦prog | adv' ⟧ inp.
  Proof.
    move: ts_sem_impl'=> /[apply] /[apply] - [] step' [restr1 restr2].
    exists {|States := States adv; init := init adv ; Attacker.step :=  step' |}.
    move=> /=; split=> // {restr1}.
    move=> inp; move: restr2=> /(_ inp). (* Why no apply *)
    rewrite /⟦_|_ ⟧ /=.
    set initcfg := (init_cfg_fn _)=> inv.
    pose bsirel cfg cfg' := cfg = cfg' /\ reachable (step adv_step) initcfg cfg. (* Can I use evar magic *)
    unshelve apply: trace_sbisim; [exact bsirel| ..]; subst bsirel; cycle 1.
      { rewrite /= /initcfg. split=> //. move. exists 0. done. } (* TODO: Lemma *)
    move=> s1 s2 [<- rch].
    move: inv (rch)=> /[apply]=> [] [] <- <-.
    do 2 split=> //.
    move: rch=> [n ->]. exists (S n)=> //. (* Should be a lemma. TODO *) 
  Qed.

End ts_restr_implication.
