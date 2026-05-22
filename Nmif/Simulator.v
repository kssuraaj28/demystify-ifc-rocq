From Stdlib Require List ssreflect ssrfun ssrbool. 
Import List ListNotations ssreflect ssrfun ssrbool.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

(* How is the simulator constructed? *)

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
  Notation SimStateMachine := (AdvNextStep SimStates).

  Variables (atk: AdvNextStep AtkStates)(* (prog: Prog) You only need this when you do the init*).

  (* `c` has a guard and is secret.. *)
  Definition is_secret_guard (c: option Cmd) : bool :=
    match c with
    | Some (cond (gvar, _) _ _) => is_secret gvar
    | Some (while (gvar, _) _) => is_secret gvar
    | _ =>  false
    end. 

  (* sim_init forwarded the underlying attacker's init_state to build a
     SimStates from the public store view:
       Definition sim_init (init_sv : StoreView) : SimStates :=
         let: store := fun v => if (init_sv v) is Some vl then vl else val_ne in
         mk_simstate (init_state atk init_sv) store (map (fun c => (Some c, true)) prog).
     Dropped along with the init_state field of AdvNextStep. *)

  Definition sim_step 
    (ocmd: option Cmd) (isatk: bool) (sim_st : Store) (ast: AtkStates):
    (Store (* sim_st *) * AtkStates *  list ((option Cmd) * bool)) :=

    let: sim_st := if isatk is true then (pre_cmd_action atk ast sim_st) else sim_st in
    let: sim_st := optcmd_stp_store ocmd sim_st in 

    let: post_atk := post_cmd_action atk ast sim_st in
    let: ast := if isatk is true then post_atk.1 else ast in
    let: steps := if isatk is true then post_atk.2 else 0 in

    let: cont_prog := if is_secret_guard ocmd is true then [] else map Some (optcmd_stp_cnt ocmd sim_st) in 
    let: cont_atk := repeat true steps in
    let: cont_full := combine_extend2 cont_prog cont_atk None false in


    (sim_st, ast, cont_full).

  
  Obligation Tactic := easy. (* TODO: Program cases or whatnot *)
  Program Definition construct_simulator : SimStateMachine := 
    {|
      post_cmd_action st _ :=
        let: (mk_simstate ast sim_st prg) :=  st in 
        if prg isn't (ocmd, isatk) :: rest then (st, 0) else
        let: (sim_st, new_ast, cont) := sim_step ocmd isatk sim_st ast in
        (mk_simstate new_ast sim_st (cont ++ rest), length cont);
        

(*
      substeps '(mk_simstate ast sim_st prg) := 
        if prg isn't (ocmd, isatk) :: _ then 0 else
        let: (_, cont) := sim_step ocmd isatk sim_st ast in
        length cont;
        *)

      pre_cmd_action _ st :=  st ;  (* Ideal pre-cmd action is weak *)
    |}.

  Fact construct_simulator_pre_cmd ast st :
    pre_cmd_action construct_simulator ast st = st.
  Proof. done. Qed.

  Fact construct_simulator_post_cmd_cons ocmd isatk rest ast sim_st st :
    post_cmd_action construct_simulator
      (mk_simstate ast sim_st ((ocmd, isatk) :: rest)) st =
      let: (sim_st', new_ast, cont) := sim_step ocmd isatk sim_st ast in
      (mk_simstate new_ast sim_st' (cont ++ rest), length cont).
  Proof. rewrite /=; case isatk=>  //=. Qed.

  Lemma clean_cmd_stp_store_secret_guard c s :
    is_secret_guard (Some c) = true ->
    clean_cmd_stp_store c s = s.
  Proof. case: c => [dst exp | [g cmp] b1 b2 | [g cmp] b] //=. Qed.

  Import VarValStore.Notations.
  Lemma clean_cmd_stp_cnt_pub_nf c st1 st2:
    is_secret_guard (Some c) = false ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
    clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof.
    case: c => [dst exp | [g cmp] b1 b2 | [g cmp] b] //=.
    - move=> nsg pubeq.
      rewrite /is_secret_guard /= /is_secret in nsg.
      have gp : is_public g.
      { move: nsg. case: (is_public g) => //. }
      rewrite /eval_bool_exp /=.
      have eqg : st1 g = st2 g.
      { apply: storeview_eq; [exact: pubeq | exact: gp]. }
      rewrite eqg. done.
    - move=> nsg pubeq.
      rewrite /is_secret_guard /= /is_secret in nsg.
      have gp : is_public g.
      { move: nsg. case: (is_public g) => //. }
      rewrite /eval_bool_exp /=.
      have eqg : st1 g = st2 g.
      { apply: storeview_eq; [exact: pubeq | exact: gp]. }
      rewrite eqg. done.
  Qed.
End sim_constr.

Ltac2 this_cookbook () := this_cookbook_ ().
