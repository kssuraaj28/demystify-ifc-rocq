From Stdlib Require List ssreflect ssrfun ssrbool. 
Import List ListNotations ssreflect ssrfun ssrbool.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section sim_st.
  Context `{!VarPrm, !ValPrm} {AtkStates: Type}.

  Record SimStates  := mk_simstate {
      ast : AtkStates;
      sim_st : Store; 
      program : list ((option Cmd) * bool); 
    }.
End sim_st.



Section sim_constr.
  Import Util.List.

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Notation SimStates := (SimStates (AtkStates:=AtkStates)).
  Notation SimStateMachine := (AdvNextStep (AtkStates := SimStates)).

  Variables (atk: (AdvNextStep (AtkStates := AtkStates))).

  (* `c` has a guard and is secret.. *)
  Definition is_secret_guard (c: option Cmd) : bool :=
    match c with
    | Some (cond (gvar, _) _ _) => is_secret gvar
    | Some (while (gvar, _) _) => is_secret gvar
    | _ =>  false
    end. 

  Definition sim_step
    (ideal_st : Store) (ocmd: option Cmd) (isatk: bool) (sim_st : Store) (ast: AtkStates):
    (Store (* sim_st *) * AtkStates * list ((option Cmd) * bool)) :=

    let: sim_st := if isatk is true then (pre_cmd_action atk ast sim_st) else sim_st in
    let: sim_st := optcmd_stp_store ocmd sim_st in 
    let: sim_st := if oapp extract_controlled_declassify None ocmd isn't Some (from, to) then sim_st else
                   update_to_store sim_st to (ideal_st to) in (* Controlled ideal read *)

    let: post_atk := post_cmd_action atk ast sim_st in
    let: ast := if isatk is true then post_atk.1 else ast in
    let: steps := if isatk is true then post_atk.2 else 0 in


    let: cont_prog := if is_secret_guard ocmd is true then [] else map Some (optcmd_stp_cnt ocmd sim_st) in
    let: cont_atk := repeat true steps in
    let: cont_full := combine_extend2 cont_prog cont_atk None false in

    (sim_st, ast, cont_full).

  
  Definition sim_post st ideal_st :=
    let: (mk_simstate ast sim_st prg) :=  st in
    if prg isn't (ocmd, isatk) :: rest then (st , 0) else
    let: (sim_st, new_ast , cont) := sim_step ideal_st ocmd isatk sim_st ast in
    (mk_simstate new_ast sim_st (cont ++ rest), length cont).

  Definition sim_pre st ideal_st :=
    let: (mk_simstate ast sim_st prg) :=  st in
    if prg isn't (ocmd, isatk) :: rest then ideal_st else
    let: sim_st := if isatk is true then (pre_cmd_action atk ast sim_st) else sim_st in (* There is repetition here *)
    let: sim_st := optcmd_stp_store ocmd sim_st in
    if oapp extract_controlled_endorse None ocmd isn't Some (from, to) then ideal_st else
    update_to_store ideal_st from (sim_st from).

  Definition sim_evnt st :=
    let: (mk_simstate ast _ prg) := st in
    if prg isn't (_, isatk) :: rest then None else
    if isatk is false then None else
    pre_cmd_event atk ast.

  Obligation Tactic := idtac. (* Program cases *)
  Program Definition construct_simulator : SimStateMachine :=
    {|
      pre_cmd_action := sim_pre;
      pre_cmd_event := sim_evnt;
      post_cmd_action := sim_post;
    |}.
  Next Obligation. 
    case=> ? ? [] //= - [] [] // [] // [] // *. Util.local_cook. 
    move t: (extract_controlled_endorse _)=> t'; move: t' t; case=> // - [] >. (* this move + equation happens a lot*)
    move/extr_endorse_eq=> [] [-> ->] [] /= *. 
    apply: update_storeview_nochange. 
    Util.local_cook. Attacker.local_cook.
  Qed.

Import VarValStore.Notations.
  Next Obligation. 
    case=> ? ?; case=> // - []. 
    rewrite/sim_pre /Noninterference.Noninterfering; case; try easy.
    case; try easy. case=> // *. 
    Semantics.local_cook. Util.local_cook.
    move t: (extract_controlled_endorse _)=> t'; move: t' t; case=> // - [] >. (* this move + equation happens a lot*)
    move/extr_endorse_eq=> [] [-> ->] [] /= *. 
    auto using update_same_varval.
  Qed.

  Next Obligation. 
    case=> ? ?; case=> // - [] [] // [] // [] //.  
    rewrite/sim_post /Noninterference.Noninterfering=> from to ? ? i1 i2 *.
    pattern_eq_2 [sim_step _ _ _ _ _] [sim_step _ _ _ _ _]=> [| ->] //.
    rewrite/sim_step. Semantics.local_cook. Util.local_cook.
    move t: (extract_controlled_declassify _)=> t'; move: t' t; case=> // - [] vfr vto. (* This move + equn *)
    move/extr_decl_eq=> [] [-> ->] [] /= *.
    suff: (i1 vto = i2 vto)=> [-> //|].
    apply: storeview_eq; eauto. Attacker.local_cook. 
  Qed.

  Lemma clean_cmd_stp_store_secret_guard c s :
    is_secret_guard (Some c) = true ->
    clean_cmd_stp_store c s = s.
  Proof. case: c=> * //=. Qed.

  Import VarValStore.Notations.
  Lemma clean_cmd_stp_cnt_pub_nf c st1 st2: (* This name is stupid *)
    is_secret_guard (Some c) = false ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
    clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof.
    case: c=> //= - [g c] > nsg ?.
    1-2: do [rewrite /is_secret_guard /= /is_secret; move/negbFE] in nsg.
    1-2: rewrite /eval_bool_exp /=.
    1-2: pattern_eq_2 [st1 _] [st2 _]; [eauto using storeview_eq| ]=> -> //.
  Qed.
End sim_constr.

Section full_sim_constr.
  Import VarValStore VarValStore.Notations Noninterference Datatypes.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variable (p : Prog) (a: Attacker).
  Notation AtkStates := (States a). 
  Notation SimStates := (SimStates (AtkStates := AtkStates)).
  Notation adv_step := (Attacker.step a).

  Obligation Tactic := idtac.
  Program Definition simulator_init : AdvInit (AtkStates := SimStates) := {|
      init_fn st := 
        mk_simstate 
          (init_fn (init a) st) 
          ( let: blanksv := fun _ => val_ne in
            let: pubsv := ⟨ st | is_public ⟩ in 
            ⟨ pubsv → blanksv ⟩)
          (map (fun c => (Some c,  true)) p);
    |}.
  Next Obligation.  
    rewrite/Noninterference.Noninterfering/id=>  > /[dup] + ->=> ?.
    Util.local_cook. exact: init_wf.
  Qed.
  
End full_sim_constr.

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac local_cook := ltac2:(cook this_cookbook).
