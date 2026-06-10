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
  Variable (adv: AdvNextStep AtkStates).
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
  Variable (adv : AdvNextStep AtkStates).

  Definition CmdEvent := option (Vars * Vals).

  Record Event := mk_acmd_evnt { cevnt : CmdEvent ; aevnt : AdvEvent }.
  Definition blank_event := mk_acmd_evnt None None.

  (* Can be split into a CmdEvent helper and an AdvEvent helper later. *)
  Definition event_helper (past_acmd : AtkCmd) (new_store : Store) (old_ast : AtkStates) : Event :=
    let: mk_atkcmd isatk ocmd := past_acmd in
    let: atk_event := if isatk is false then None else pre_cmd_event adv old_ast in
    let: cmd_event := if ocmd isn't Some (assign a) then None else
                      let: adst := get_assign_dest a in
                      let: oval := ⟨ new_store | is_trusted ⟩ adst in
                      omap (pair adst) oval in
    mk_acmd_evnt cmd_event atk_event.
End event_helper.


Section cfg.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Variable (adv : AdvNextStep AtkStates).

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
    if aclst isn't ac :: rest then blank_event else
    let: (_, old_ast) := s in
    let: (_, s') := step c in
    let: (new_store, _) := s' in
    event_helper adv ac new_store old_ast.
End cfg.

Section trace.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Variable (adv : AdvNextStep AtkStates).

  Instance event_prm : EventPrm := {
    Events := Event;
    stutter := blank_event;
  }.

  Definition trace (c : Cfg (AtkStates := AtkStates)) : Trace :=
    build (step adv) (event adv) c.
End trace.

Section running.
  Context `{!VarPrm, !ValPrm}.
  Definition is_running (ac : AtkCmd) : bool :=
      is_attacked ac || isSome (ocmd ac).
End running.

Section twocfg.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable (adv1: AdvNextStep AtkStates1) (adv2: AdvNextStep AtkStates2).

  Notation State1 := (State (AtkStates:=AtkStates1)).
  Notation State2 := (State (AtkStates:=AtkStates2)).

  Definition TwoCfg := (list (AtkCmd * AtkCmd) * State1 * State2)%type.

  Definition twostep (c: TwoCfg): TwoCfg (* * (Event * Event) *) :=
    let: (c2lst, s1, s2) := c in
    if c2lst isn't (ac1, ac2) :: rest then c (*, (blank_event, blank_event) *) else
    let: (p1, st1 (*, ev1 *), steps1) := (acmd_step adv1 ac1 s1) in
    let: (p2, st2 (*, ev2 *), steps2) := (acmd_step adv2 ac2 s2) in

    let: cont := combine_extend4
                   (map Some p1) (repeat true steps1)
                   (map Some p2) (repeat true steps2)
                   None false None false in
    let: cont := map (fun '(oc1, a1, oc2, a2) => (mk_atkcmd a1 oc1, mk_atkcmd a2 oc2)) cont in
    (cont ++ rest, st1, st2) (*, (ev1, ev2) *).




  Import VarValStore.Notations.

  Definition twoevent (c: TwoCfg): Event * Event :=
    let: (c2lst, s1, s2) := c in
    if c2lst isn't (ac1, ac2) :: rest then (blank_event, blank_event) else
    let: (_, old_ast1) := s1 in
    let: (_, old_ast2) := s2 in
    let: (_, s1', s2') := twostep c in (* Here, I've defined this in terms of twostep. *)
    let: (new_store1, _) := s1' in
    let: (new_store2, _) := s2' in
    let: e1 := event_helper adv1 ac1 new_store1 old_ast1 in
    let: e2 := event_helper adv2 ac2 new_store2 old_ast2 in
    (e1, e2).
End twocfg.

Section twooneextract.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable (adv1: AdvNextStep AtkStates1) (adv2: AdvNextStep AtkStates2).

  Notation TwoCfg := (TwoCfg (AtkStates1:=AtkStates1) (AtkStates2:=AtkStates2)).
  Notation State1 := (State (AtkStates:=AtkStates1)).
  Notation State2 := (State (AtkStates:=AtkStates2)).

  Definition extract_one_cfg (is_left : bool) (c : TwoCfg ) :=
    let: (aclst, s1, s2) := c in
    let: aclst :=
      filter is_running
        (map (if is_left then fst else snd) aclst) in
    if is_left as b return Cfg (AtkStates := if b then AtkStates1 else AtkStates2)
    then (aclst, s1) else (aclst, s2).

  Definition extract_one_event (is_left : bool) (c: TwoCfg) : Event :=
    let: (e1, e2) := twoevent adv1 adv2 c in
    if is_left then e1 else e2.

  Notation adv b := (if b as b' return (_ (if b' then _ else _)) then adv1 else adv2).
  Notation step_extract c b := (extract_one_cfg b (twostep adv1 adv2 c)).
  Notation extract_step c b := (step (adv b) (extract_one_cfg b c)).

  Lemma extract_step_cfg b ac1 ac2 rest s1 s2 :
    is_running (if b then ac1 else ac2) ->
    step_extract ((ac1, ac2) :: rest, s1, s2) b  = extract_step ((ac1, ac2) :: rest, s1, s2) b.
  Proof.
    case: b; rewrite/is_true=> ?.
    1,2: rewrite/extract_one_cfg map_cons [filter _ _] /=; Util.local_cook.
    1,2: pattern_focus [LHS] => P.
    1,2: rewrite/twostep. 
    1: case: (acmd_step adv2 _ _)=>- [] *. 2: case: (acmd_step adv1 _ _)=>- [] *.
    1: move step: (acmd_step adv1 _ _)=> [[? ?] ?]. 2: move step: (acmd_step adv2 _ _)=> [[? ?] ?].
    1,2: rewrite combine_extend4_split22  !map_app filter_app !map_map.
    1,2: erewrite map_ext; [| case=> - [] ? ? [] > /=; instantiate (1 := fun '(_,_,(_, _)) => _); reflexivity].
    1,2: subst P; cbn beta. 
    1,2: rewrite/Semantics.step step; Util.local_cook; Util.List.local_cook.
    1,2: rewrite filter_map_swap.
    1: erewrite filter_ext; [|case=> - [? ?]  [? ?] /=; instantiate (1 := fun '(_,_,_) => _); reflexivity ].
    2: erewrite filter_ext; [|case=> - [? ?]  [? ?] /=; instantiate (1 := fun '(_,_,(_,_)) => _); reflexivity ].
    1: erewrite map_filter_combine_extend2_ind1; [ | case=> ? ? _; instantiate (1 := fun '(_,_)=> _); reflexivity | case=> ? ? [] _ _; instantiate (1 := fun '(_,_) => _); reflexivity | done].
    2: erewrite map_filter_combine_extend2_ind2; [| case=> _ _ [] >; instantiate (1 := fun '(_,_) => _); reflexivity| case=> _ _ [] >; instantiate (1 := fun '(_,_) => _); reflexivity | done].
    1,2: congr map; clear.
    1,2: revert_hyp_pat [Prog, nat].
    1,2: elim; [ elim=> // >  /= -> // |].
    1,2: move=> > ih  [] /= *; Util.local_cook. 
    1,2: clear; rewrite map_map filter_map_swap filter_true //.
  Qed.

  Lemma extract_step_event b ac1 ac2 rest s1 s2 :
    is_running (if b then ac1 else ac2) ->
    extract_one_event b ((ac1, ac2) :: rest, s1, s2) = event (adv b) (extract_one_cfg b ((ac1, ac2) :: rest, s1, s2)).
  Proof.
    case: b;rewrite/is_true=> ?.
    1,2: rewrite/extract_one_event /extract_one_cfg/map_cons [filter _ _]/=; Util.local_cook.
    1,2: rewrite/event/step; move e: (acmd_step _ _ _)=> [[? [? ?]] ?].
    1,2: rewrite/twoevent/twostep e; case: (acmd_step _ _ _)=> - [] _ [] ? _ _.
    1,2: clear. 
    1,2: case: s1=> *; case: s2=> *; done.
  Qed.

  Lemma extract_stutter_cfg b ac1 ac2 rest s1 s2 :
    ~~ is_running (if b then ac1 else ac2) ->
    step_extract ((ac1, ac2) :: rest, s1, s2) b = extract_one_cfg b ((ac1, ac2) :: rest, s1, s2).
  Proof.
    case: b=> /negbTE.
    1: move: ac1. 2: move: ac2.
    1,2: case=> - [] // [] // _.
    1,2: rewrite/extract_one_cfg map_cons [filter _ _]/=.
    1,2: rewrite/twostep; case: s1; case: s2=> *.
    1: pattern_focus [acmd_step adv1 _ _]=> P. 2: pattern_focus [acmd_step adv2 _ _]=> P.
    1,2: rewrite/acmd_step /=; subst P; cbn beta.
    1: move: (acmd_step adv2 _ _)=> [] [] *. 2: move: (acmd_step adv1 _ _)=> [] [] *.
    1,2: rewrite combine_extend4_split22 /= ?combine_extend2_nil_r ?combine_extend2_nil_l !map_map map_app map_map; Util.local_cook. 
    1,2: rewrite filter_app; Util.List.local_cook. 
    1,2: erewrite map_ext;[| case=> * /=; instantiate (1:= fun _ => _); reflexivity].
    1,2: rewrite filter_map_swap; Util.List.local_cook.
    1,2: erewrite filter_ext;[| case=> * /=;rewrite/is_running/=; instantiate (1:= fun _ => _); reflexivity].
    1,2: rewrite filter_false; done.
  Qed.

  Lemma extract_stutter_event b ac1 ac2 rest s1 s2 :
    ~~ is_running (if b then ac1 else ac2) ->
    extract_one_event b ((ac1, ac2) :: rest, s1, s2) = blank_event.
  Proof.
    case: b=>/negbTE.
    1: move: ac1. 2: move: ac2.
    1,2: case=> - [] // [] // _.
    1,2: rewrite/extract_one_event.
    1,2: rewrite/twoevent/twostep; case: s1; case: s2=> *.
    1: pattern_focus [acmd_step adv1 _ _]=> P. 2: pattern_focus [acmd_step adv2 _ _]=> P.
    1,2: rewrite/acmd_step /=; subst P; cbn beta.
    1: move: (acmd_step adv2 _ _)=> [] [] *. 2: move: (acmd_step adv1 _ _)=> [] [] *.
    1,2: move=> /=; clear.
    1: revert_hyp_pat State2. 2: revert_hyp_pat State1. 
    1,2: case; done.
  Qed.
End twooneextract.

(* Given a configuration, erase what  *)
Section cfg_erase_filter.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable (adv1: AdvNextStep AtkStates1) (adv2: AdvNextStep AtkStates2).

  Notation twostep := (twostep adv1 adv2).
  Notation TwoCfg := (TwoCfg (AtkStates1:=AtkStates1) (AtkStates2:=AtkStates2)).
  Notation State1 := (State (AtkStates:=AtkStates1)).
  Notation State2 := (State (AtkStates:=AtkStates2)).

(* TODO: This was copied. Maybe make it better *)
  Notation adv b := (if b as b' return (_ (if b' then _ else _)) then adv1 else adv2).
  Notation step_extract c b := (extract_one_cfg b (twostep c))(only parsing).
  Notation extract_step c b := (step (adv b) (extract_one_cfg b c)) (only parsing).

  Definition erase_filter_cfg (is_left : bool) (c : TwoCfg) : TwoCfg :=
    let: (p, st1, st2) := c in
    (filter (fun '(c1,c2) => let c := if is_left then c1 else c2  in is_running c) p, st1, st2).
  

  Lemma erase_filter_step_commute b c: 
    let: c' := erase_filter_cfg b c in
    step_extract c' b = extract_step  c' b . (* TODO: I think that this should be c *)
  Proof.
    case: c=> - [].
    case: b=> *.
    1,2: rewrite /erase_filter_cfg. 
    1,2: move eqn: (filter _ _)=> [| [? ?] ?] //.
    1,2: rewrite extract_step_cfg=> //.
    1,2: move: eqn; move: (X in filter _ X); clear. 
    1,2: elim=> // - [] > /= ?. (* TODO: Lemma *)
    1,2: case e: (is_running _)=> // - [] e1 e2.
    1,2: rewrite -?e1 -?e2 //.
  Qed.

End cfg_erase_filter.

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac local_cook := ltac2:(cook this_cookbook).
