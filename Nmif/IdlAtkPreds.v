From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace.
Import Tacs Util Util.List VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Combined Simulator WfFinisher CombinedExtract CoTrace Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section idldowngrade_prd.
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
End idldowngrade_prd.

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

(* The theorem:
  IdlAtkDowngradeRestr -> NMIFRestr / ... has parameters
*)
Section restriction_impl_prm.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.

  Variable noend nodecl : bool.

  Notation AdvInit := (AdvInit (AtkStates := AtkStates)) (only parsing).
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)) (only parsing).
  Notation Cfg := (Semantics.Cfg (AtkStates := AtkStates)) (only parsing).

  Definition AdvRestr (adv_step : AdvNextStep) :=
    (match noend, nodecl with
      | true, true => NIRestr adv_step
      | true, false => RDRestr adv_step
      | false, true => TERestr adv_step
      | false, false => NMIFRestr adv_step
    end).

  Definition CmdRestr  :=
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
  Definition CfgListRestr (cmd : Cfg) := 
    (let: (lst, st) := cmd  in 
    if lst isn't (mk_atkcmd _ (Some cmd )) :: _ then True else
    CmdRestr cmd).


  (* TODO: Copy? *)
  Notation init_cfg_fn prog adv_init inp := ((Semantics.init_cfg prog adv_init inp)). 
  Definition RuntimeCmdRestr prog adv_init adv_step :=
    (forall inp cfg, 
      reachable (step adv_step) (init_cfg_fn prog adv_init inp) cfg ->
      CfgListRestr cfg).
End restriction_impl_prm.

Check CmdRestr.

(* Utility functions to show  how IdlAtkDowngradeRestr impled that other four *)
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


  Notation ReplLrnInp := (AtkStates -> (AtkStates * nat)). (* Record update!! *)
  Program Definition replace_learner
      (adv : AdvNextStep) (learn : AtkStates -> (AtkStates * nat)) : AdvNextStep := {|
    pre_cmd_action  := pre_cmd_action adv;
    pre_cmd_event   := pre_cmd_event adv;
    post_cmd_action := fun ast _ => learn ast;
    pre_cmd_wf_int  := pre_cmd_wf_int adv;
    pre_cmd_wf_conf := pre_cmd_wf_conf adv;
  |}.
End atk_step_record_update.

Section restriction_impl.
  Import VarValStore.Notations Util.DecEq Util.DecEq.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variable (adv : Attacker) (prog : Prog).
  Variable noend nodecl : bool.

  Notation adv_init := (Attacker.init adv).
  Notation adv_step := (Attacker.step adv).
  Notation init_cfg_fn inp := ((Semantics.init_cfg prog adv_init inp)).   (* TODO: Copy? *)

  Notation RuntimeCmdRestr := (RuntimeCmdRestr noend nodecl prog adv_init adv_step).  Check RuntimeCmdRestr : Prop.
  Notation IdlAtkDowngradeRestr := (IdlAtkDowngradeRestr prog adv). Check IdlAtkDowngradeRestr : Prop.

  Notation AdvRestr :=  (AdvRestr noend nodecl).  Check AdvRestr : AdvNextStep -> Prop.



  (* Witness consturu *)


  (* TODO: Add the constructions should come here *)
  Notation witness_constr adv_step corr_fn learn_fn :=
    (match noend, nodecl with
      | true, true => replace_learner (remove_corruptor adv_step) (fun st => learn_fn st val_ne)
      | true, false => remove_corruptor adv_step
      | false, true => replace_learner (replace_corruptor adv_step corr_fn) (fun st => learn_fn st val_ne)
      | false, false => replace_corruptor adv_step corr_fn
    end).


  Lemma ts_sem_impl':
    IdlAtkDowngradeRestr ->    RuntimeCmdRestr ->
    exists adv_step', AdvRestr adv_step' /\
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
    IdlAtkDowngradeRestr ->  RuntimeCmdRestr ->
    exists adv', AdvRestr (Attacker.step adv') /\
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

End restriction_impl.
