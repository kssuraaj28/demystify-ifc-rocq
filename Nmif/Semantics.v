From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt CoTrace.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt CoTrace Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

Fail Ltac2 Check Attacker.this_cookbook_.
#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section exp.
  Context `{!VarPrm, !ValPrm}.
  Definition eval_val_exp (st: Store) (e: ValExp) : Vals :=
    let: (v1, v2, comp) := e in 
    let: vl1 := st v1 in
    let: vl2 := st v2 in
    comp vl1 vl2.

  Definition eval_bool_exp (st: Store) (e: BoolExp) : bool :=
    let: (v, comp) := e in
    let: vl := st v in
    comp vl.
End exp.

Section assignstep.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Definition get_assign_dest (a: Assignment) : Vars :=
    match a with
    | exp_assign _ dst => dst
    | endorse _ dst    => dst
    | declassify _ dst => dst
    end.

  Definition get_assign_val (s: Store) (a: Assignment) : Vals :=
    match a with
    | exp_assign exp _ => eval_val_exp s exp
    | endorse src _    => s src
    | declassify src _ => s src
    end.

  Definition clean_assign_stp_store (a: Assignment) (s: Store) : Store :=
    update_to_store s (get_assign_dest a) (get_assign_val s a).

End assignstep.

Section cleanstep.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Notation Continuation := Syntax.Prog.

  Definition clean_cmd_stp_store (c: Cmd) (s: Store) : Store :=
    if c isn't assign a then s else clean_assign_stp_store a s.
  
  Definition optcmd_stp_store := oapp clean_cmd_stp_store id.

  Definition clean_cmd_stp_cnt (c: Cmd) (s: Store) : Continuation :=
    match c with
    | cond exp b1 b2 => 
      let: tst := eval_bool_exp s exp in 
      if tst is true then b1 else b2
    | while exp b =>
      let: tst := eval_bool_exp s exp in 
      if tst is true then (b ++ [c]) else []
    | _ =>  []
    end.

  Definition optcmd_stp_cnt := oapp clean_cmd_stp_cnt (fun _ => []).


  Fact optcmd_stp_store_simpl c s: ltac2:(cbn_eq (optcmd_stp_store (Some c) s)). Proof. done. Qed.
  Fact optcmd_stp_cnt_simpl c s: ltac2:(cbn_eq (optcmd_stp_cnt (Some c) s)). Proof. done. Qed.
  Fact clean_cmd_stp_store_endorse from to s :
    ltac2:(cbn_eq (clean_cmd_stp_store (assign (endorse from to)) s)).
  Proof. done. Qed.
  Fact clean_cmd_stp_store_declassify from to s :
    ltac2:(cbn_eq (clean_cmd_stp_store (assign (declassify from to)) s)).
  Proof. done. Qed.

  Lemma clean_cmd_stp_cnt_idem c s :
    clean_cmd_stp_cnt c (clean_cmd_stp_store c s) = clean_cmd_stp_cnt c s.
  Proof. case: c => //=. Qed.

  Fact optcmd_stp_cnd_idem c s : (* TODO: This should be rewrite step *)
    optcmd_stp_cnt c (optcmd_stp_store c s) = optcmd_stp_cnt c s.
  Proof. case: c=> //= *. exact: clean_cmd_stp_cnt_idem. Qed.

  Fact clean_cmd_stp_cnt_assign a s : clean_cmd_stp_cnt (assign a) s = [].
  Proof. done. Qed.
End cleanstep.

Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> optcmd_stp_store_simpl) "optcmd_stp_store_simpl" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> optcmd_stp_cnt_simpl) "optcmd_stp_cnt_simpl" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> optcmd_stp_cnd_idem) "optcmd_stp_cnd_idem" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> clean_cmd_stp_store_endorse) "clean_cmd_stp_store_endorse" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> clean_cmd_stp_store_declassify) "clean_cmd_stp_store_declassify" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> clean_cmd_stp_cnt_assign) "clean_cmd_stp_cnt_assign" old.

Section test.
  Context `{!VarPrm, !ValPrm}.
  Ltac cook := ltac2:(cook this_cookbook_).

  Goal forall (P: _ -> Prop) c s, P (optcmd_stp_store (Some c) s).
  Proof. move=> *. cook. Abort.
End test.

Section acmd.
  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm} {AtkStates : Type}.
  Variable (adv: AdvNextStep (AtkStates := AtkStates)).
  Record AtkCmd := mk_atkcmd {is_attacked: bool; ocmd : option Cmd}.
  Definition State := (Store * AtkStates)%type.

  Definition acmd_step (ac: AtkCmd) (s: State): Prog * State (* * Event *) * nat :=
    let: mk_atkcmd isatk cmd := ac in
    let: (store, atk_st) := s in
    let: st := if isatk is true then pre_cmd_action adv atk_st store else store in
    let: (prog, st (*, cevnt *)) := (optcmd_stp_cnt cmd st,  optcmd_stp_store cmd st (*, optcmd_evnt cmd st *)) in

    let: atk_pst := (post_cmd_action adv atk_st st) in
    let: atk_st := if isatk is true then atk_pst.1 else atk_st in
    (* let: aevnt := if isatk is true then atk_pst.1.2 else None in *)
    let: steps := if isatk is true then atk_pst.2 else 0 in

    (prog, (st, atk_st) (*, mk_acmd_evnt cevnt aevnt *), steps).
  

  Fact acmd_step_atk cmd store atk_st :
    ltac2:(cbn_eq (acmd_step (mk_atkcmd true cmd) (store, atk_st))). 
  Proof. done. Qed. 

  Fact acmd_step_noatk cmd store atk_st :
    ltac2:(cbn_eq (acmd_step (mk_atkcmd false cmd) (store, atk_st))).
  Proof. done. Qed.
End acmd.

Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> acmd_step_atk ) "acmd_step_atk" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> acmd_step_noatk ) "acmd_step_noatk" old.

Section event_helper.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Variable (adv: AdvNextStep (AtkStates := AtkStates)).

  Definition CmdEvent := option (Vars * Vals).

  Variant Event := mk_acmd_evnt ( cevnt : CmdEvent) ( aevnt : AdvEvent ) | mk_terminate_event.
  Definition blank_event := mk_acmd_evnt None None.

  (* Can be split into a CmdEvent helper and an AdvEvent helper later. *)
  Definition event_gen (curr_cmd : AtkCmd) (store : Store) (ast : AtkStates) : Event :=
    let: mk_atkcmd isatk ocmd := curr_cmd in
    let: atk_event := if isatk is false then None else pre_cmd_event adv ast in
    let: cmd_event := if ocmd isn't Some (output v) then None else
                      let: oval := ⟨ store | is_trusted ⟩ v in
                      omap (pair v) oval in
    mk_acmd_evnt cmd_event atk_event.
End event_helper.

Section cfg.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Variable (adv: AdvNextStep (AtkStates := AtkStates)).

  Definition Cfg := (list AtkCmd * State (AtkStates:=AtkStates))%type.

  Definition step (c : Cfg) : Cfg :=
    let: (aclst, s) := c in
    if aclst isn't ac :: rest then c else
    let: (p, s', steps) := acmd_step adv ac s in
    let: cont := combine_extend2 (map Some p) (repeat true steps) None false in
    let: cont := map (fun '(oc, a) => mk_atkcmd a oc) cont in
    (cont ++ rest, s').

  Definition event (c : Cfg) : Event :=
    let: (aclst, s) := c in
    if aclst isn't ac :: rest then mk_terminate_event else
    let: (store, ast) := s in
    event_gen adv ac store ast.
End cfg.

Section step_inj.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).

  Lemma single_step_inj (a a' : AdvNextStep) ac tl s :
    step a (ac :: tl, s) = step a' (ac :: tl, s) ->
    acmd_step a ac s = acmd_step a' ac s.
  Proof.
    rewrite /step.
    move: (acmd_step a ac s) => [[p st] n].
    move: (acmd_step a' ac s) => [[p' st'] m].
    move=> [] /app_inv_tail /map_inj.
    evar_spec_toph=> [ [? ?] [? ?] [-> ->] //|].
    move=> + ->=> leq.
    suff: (p = p' /\ n = m)=> [[-> ->] // |].
    split; move: leq; clear. (* TODO: Lemma? *)

    + elim: p p' (repeat _ _) (repeat _ _).
        1: case=> // ? ?. 2: move=> ? ? ih [].
        1,2: move=> r1 r2 + /ltac:(exfalso).
        1,2: rewrite ![map Some []]/= ![map Some (_ :: _)]/= combine_extend2_consl. (* Can be cook rules *)
        1,2: (case: r1 + case: r2); done.
      move=> >. rewrite ![map Some (_ :: _)]/= !combine_extend2_consl.
      case=> -> _ /ih -> //.

    + elim: n m (map _ _) (map _ _).
        1: case=> // ?. 2: move=> ? ih [].
        1,2: move=> m1 m2 + /ltac:(exfalso).
        1,2: rewrite ![repeat true 0]/= ![repeat true (S _)]/= combine_extend2_consr.
        1,2: (case: m1 + case: m2); done.
      move=> >. rewrite ![repeat _ (S _)]/= !combine_extend2_consr.
      case=> _ /ih -> //.
  Qed.

End step_inj.

Section cfg_trace.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Variable (adv : AdvNextStep (AtkStates := AtkStates)).

  Fail Check ltac:(exact Trace).
  Instance event_prm : EventPrm := {
    Events := Event;
    stutter := blank_event;
  }.  Check ltac:(exact Trace).

  Definition cfg_trace (c : Cfg (AtkStates := AtkStates)) : Trace :=
    build (step adv) (event adv) c.
End cfg_trace.

Section init.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Variable (p : Prog) (ainit: AdvInit (AtkStates := AtkStates)) (init_store: Store).

  Definition init_cfg : Cfg :=
    (map (fun c => mk_atkcmd true (Some c)) p, (init_store, init_fn (ainit) init_store)). 
End init.

Section trace_proper.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.


  Variable (p : Prog) (a: Attacker) (init_store: Store).
  Notation AtkStates := (States a).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation adv_step := (Attacker.step a). (* TODO: Change adv to adv_step everywhere *)
  Notation adv_init := (Attacker.init a). 


  Definition trace := let initc := init_cfg p adv_init init_store in cfg_trace adv_step initc.
End trace_proper.

Notation "⟦ p | a ⟧" := (trace p a). Check ⟦_ | _ ⟧ : Store -> Trace.

Section running.
  Context `{!VarPrm, !ValPrm}.
  Definition is_running (ac : AtkCmd) : bool :=
      is_attacked ac || isSome (ocmd ac).
End running.

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac local_cook := ltac2:(cook this_cookbook).
