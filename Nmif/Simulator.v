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
    (ideal_st : Store) (ocmd: option Cmd) (isatk: bool) (sim_st : Store) (ast: AtkStates):
    (Store (* sim_st *) * AtkStates *  list ((option Cmd) * bool)) :=

    let: sim_st := if isatk is true then (pre_cmd_action atk ast sim_st) else sim_st in
    let: sim_st := optcmd_stp_store ocmd sim_st in 
    let: sim_st := if ocmd isn't Some (declassify from to) then sim_st else 
                   if (is_public to) is false then sim_st else
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
        if prg isn't (ocmd, isatk) :: rest then (st, 0) else
        let: (sim_st, new_ast, cont) := sim_step ideal_st ocmd isatk sim_st ast in
        (mk_simstate new_ast sim_st (cont ++ rest), length cont).

  Definition sim_pre st ideal_st :=
        let: (mk_simstate ast sim_st prg) :=  st in 
        if prg isn't (ocmd, isatk) :: rest then ideal_st else 
        let: sim_st := if isatk is true then (pre_cmd_action atk ast sim_st) else sim_st in (* There is repetition here *)
        let: sim_st := optcmd_stp_store ocmd sim_st in 
        if ocmd isn't Some (endorse from to) then ideal_st else  
        if (is_public from  &&  is_untrusted from) is false then ideal_st else
        update_to_store ideal_st from (sim_st from).

  Obligation Tactic := idtac. (* Program cases *)
  Program Definition construct_simulator : SimStateMachine := 
    {|
      post_cmd_action := sim_post;
      pre_cmd_action := sim_pre;
    |}. (* TODO: Why 11 obligations. *)
  Next Obligation. 
    case=> ? ?; case=> [] //= [] [] // [] //= ? ? *.
    case e1: is_untrusted=> //;[|rewrite Bool.andb_false_r]=> //.
    rewrite Bool.andb_true_r.
    case: is_public=> //.
    apply: update_storeview_nochange. rewrite /is_trusted e1 //.
  Qed.

Import VarValStore.Notations.
  Next Obligation. 
    case=> ? ?; case=> // - []. 
    rewrite/sim_pre /Noninterference.Noninterfering; case; try easy.
    case=> *; try easy.
    case e1: is_untrusted=> //; [|rewrite Bool.andb_false_r]=> //.
    rewrite Bool.andb_true_r.
    case e2: is_public=> //=.
    move: (update_to_store (if _ then _ else _) _ _ _)=> ?.
    auto using update_same_varval.
  Qed.

  Next Obligation. 
    case=> ? ?; case=> // - [] [] // [] //.  
    rewrite/sim_post /Noninterference.Noninterfering=> from to ? ? i1 i2 *.
    pattern_eq_2 [sim_step _ _ _ _ _] [sim_step _ _ _ _ _]=> [| ->] //.
    rewrite/sim_step.
    case e: is_public=> //=.
    suff: (i1 to = i2 to)=> [-> //|].
    eauto using storeview_eq.
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

(*
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> construct_simulator_pre_cmd) "construct_simulator_pre_cmd" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> construct_simulator_post_cmd_cons) "construct_simulator_post_cmd_cons" old.
*)

Ltac2 this_cookbook () := this_cookbook_ ().
