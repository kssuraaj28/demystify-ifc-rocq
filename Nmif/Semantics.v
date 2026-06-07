From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Tacs.Cook.

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

  Notation State1 := (State (AtkStates:=AtkStates1)).
  Notation State2 := (State (AtkStates:=AtkStates2)).

  Definition extract_one_cfg (is_left : bool)
    (c : TwoCfg (AtkStates1:=AtkStates1) (AtkStates2:=AtkStates2)) :=
    let: (aclst, s1, s2) := c in
    let: aclst :=
      filter (fun ac => is_attacked ac || isSome (ocmd ac))
        (map (if is_left then fst else snd) aclst) in
    if is_left as b return Cfg (AtkStates := if b then AtkStates1 else AtkStates2)
    then (aclst, s1) else (aclst, s2).

  Definition extract_one_event (is_left : bool)
    (c : TwoCfg (AtkStates1:=AtkStates1) (AtkStates2:=AtkStates2)) : Event :=
    let: (e1, e2) := twoevent adv1 adv2 c in
    if is_left then e1 else e2.


  Lemma extract_two_one_correct b c: 
    let: step_extract := extract_one_cfg b (twostep adv1 adv2 c) in
    let: adv := if b as b' return (AdvNextStep (if b' then AtkStates1 else AtkStates2)) then adv1 else adv2 in
      (step_extract = (extract_one_cfg b c) /\ extract_one_event b c = blank_event) (* Stutter *)
    \/ 
      (step_extract = step adv (extract_one_cfg b c) /\
      extract_one_event b  c = event adv (extract_one_cfg b c)).
  Proof.
    case: b. 
    1,2: case: c; case; case; [repeat constructor; fail| ]; case. 
    1: move=> + ? ? + ?. 2: move=> ? + ? ?.
    1,2: move=> ac st.
    1,2: case: st; case: ac=> isatk ocmd *. 
    1,2: enter (idtac; case stutter: (isatk || isSome (ocmd)); cycle 1).  2,4: shelve.
      1,2: left.  (* This switches goals for some reason. stupid *)
      1,2: move: stutter=> /Bool.orb_false_elim [].
      1,2: move=> ->; case: ocmd=> // _.
      1,2: split. 2,4: shelve.
        1,2: rewrite/extract_one_cfg map_cons [filter _ _]/=. 
        1,2: pattern_focus [LHS] => P.
        1,2: rewrite/twostep /= . 
        1: case: (acmd_step adv2 _ _)=>- [] *.  2: case: (acmd_step adv1 _ _)=>- [] *. 
        1,2: rewrite map_app combine_extend4_split22 /= !map_map.
        1: enter (idtac; erewrite map_ext; [|case=> * /=; instantiate (1 := fun _ => _); reflexivity]).
        2: enter (idtac; erewrite map_ext; [|case=> - [? ?] [? ?] /=; instantiate (1 := fun '(_, _, (_,_)) => _); reflexivity]).
        1,2: rewrite filter_app;  subst P; cbn beta; Util.local_cook; Util.List.local_cook.
        2: rewrite map_map.
        1,2: rewrite filter_map_swap; Util.List.local_cook.
        2:  erewrite filter_ext; [| case=> > /=; instantiate (1 := fun _ => _); reflexivity] .
        1,2: rewrite filter_false //.
      Unshelve. 1,2: shelve.
      1,2: rewrite/extract_one_event/twoevent/=; case: (acmd_step _ _ _)=> - [] _ [] ? _ _.
      1,2: clear.
      1: revert_hyp_pat State2. 2: revert_hyp_pat State1.
      1,2: case; done.

   Unshelve.
    1,2: right; split. 2,4: shelve.
      1,2: rewrite/extract_one_cfg map_cons [filter _ _] /= stutter.
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

    Unshelve.
    1,2: rewrite/extract_one_event /extract_one_cfg map_cons [filter _ _]/= stutter.
    1,2: rewrite/event/step; move e: (acmd_step _ _ _)=> [[? [? ?]] ?].
    1,2: rewrite/twoevent/twostep e; case: (acmd_step _ _ _)=> - [] _ [] ? _ _.
    1,2: clear. 
    1: revert_hyp_pat State2.  2: revert_hyp_pat State1.
    1,2: case; done.
  Qed.
End twooneextract.


(*
Section cont.
  Import Util.List. (* When to import? TODO *)
  Context `{!VarPrm, !ValPrm}.
  
  (* 
    When executing, steps are like  
    (enabled?) attack - (enabled?) prog 
  *)
  Record AtkCmd :=
    mk_cstep {is_attacked: bool; get_cmd : option Cmd}.

  Definition pure_atk := (mk_cstep true None).
  Definition pure_cmd c := (mk_cstep false (Some c)).

  Definition Continuation := list AtkCmd.



  (*  *)
  Fixpoint prog_zip (p: Prog) (atk_steps: nat) : Continuation :=
    match p, atk_steps with
    | cmd :: p', S atk_steps' =>
          (mk_cstep true (Some cmd)) :: (prog_zip p' atk_steps')

    | [], _ => 
        repeat pure_atk atk_steps

    | _ , 0 =>  
        map pure_cmd p
    end.

  Lemma prog_zip_noprg: forall n, prog_zip [] n = nlist pure_atk n. Proof.
    move=> //.
  Qed.

  Lemma prog_zip_noatk: forall p, prog_zip p 0 = map pure_cmd p. Proof.
    Fail move=> //; fail.
    case=>//.
  Qed.

  Section check.
    Variables c1 c2 c3 : Cmd.
    Compute prog_zip [c1 ; c2 ; c3] 5.
    Compute prog_zip [c1 ; c2 ; c3] 0.
    Compute prog_zip [c1 ; c2 ; c3] 1.
    Compute prog_zip [c1 ; c2 ; c3] 3.
  End check.
End cont.


Section atk_cmd_step.
  Import VarValStore.Notations. (* TODO: Import practice? *)

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Context  {AtkStates : Type} (atksm: AdvNextStep AtkStates).
    init_substeps: AtkStates -> nat; (* We allow atkstates because this can depend on the public store. You could force adv to run  cou *)


  (* I think that eventually, you'd want to put the observations here also.. *)
  Definition atk_cmd_step 
      (c : AtkCmd) (s : Store) (atkst : AtkStates) : 
      (Store * AtkStates * Continuation * option LeakVals) := 

        let: mk_cstep is_atk c := c in 

        (* Part1 of adversary runs *)
        let: s := if is_atk is false then s else
          corruptor atksm atkst s
        in

        (* Run your computation *)
        let: (s, pcont) := optcmd_step c s in

        (* Part2a of adversary runs. *)
        let: atkst := if is_atk is false then atkst else learner atksm atkst s  in

        (* Part2b of adversary runs. *)
        let: (substeps, optleak) :=
          if is_atk is false then
            (0, None)
          else
            (substeps atksm atkst, leaker atksm atkst)
        in

        (s, atkst, prog_zip pcont substeps, optleak).

End atk_cmd_step.

Section cfg.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Context (AtkStates : Type).

  (* Only trusted store view *)
  Definition Observation := (StoreView * option LeakVals)%type.

  Definition ObservationTrace := list Observation.

  (* It is useful to put everything in Cfg for bisimulation proofs *)
  Definition Cfg := (Continuation * Store * AtkStates * ObservationTrace)%type.
End cfg.

Section init_cfg.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Context {AtkStates : Type}.

  Definition initial_cfg (p: Prog) (atksm : AdvNextStep AtkStates) (s: Store) : Cfg AtkStates :=
    let: atkst := init_state atksm ⟨s | is_public⟩ in
    let: init_cont := prog_zip p (init_substeps atksm atkst) in
    (init_cont, s, atkst, []).
End init_cfg.

Section cfg_step.
  Import VarValStore.Notations. 
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Context {AtkStates : Type} (atksm : AdvNextStep AtkStates). (* TODO: unify *)

  Notation Cfg := (Cfg AtkStates).

  Definition step (c : Cfg) : Cfg :=
    let: (cont, store, atkst, trace) := c in

    let: (cont', store', atkst', optlk) := 
      if cont isn't (atk_cmd :: cont') then (cont, store, atkst, None) else (* TODO: How to handle termination correctly *)
      let: (store', atkst', extra_cont, optlk) := atk_cmd_step atksm atk_cmd store atkst in 
      (extra_cont ++ cont', store', atkst', optlk)
    in 

    (cont', store', atkst', ( ⟨ store' | is_trusted ⟩, optlk) :: trace).

  (* Man, testing this might be painful.. *)
  Fixpoint multistep (gas: nat) (c : Cfg) : Cfg :=
    match gas with
    | 0 => c
    | S gas => step (multistep gas c) 
    end.

  Definition extract_trace (c : Cfg) : ObservationTrace :=
    let: (_,_,_,cfg) := c in
    cfg.
End cfg_step.

Section program_sem.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Definition Behavior := Store -> nat -> ObservationTrace.

  Context {AtkStates : Type} (atksm : AdvNextStep AtkStates).

  (* Simulating coinduction... *)
  Definition prog_behavior {AtkStates} (p : Prog) (atksm : AdvNextStep AtkStates) : Behavior :=
                          fun init_store gas =>
                            let: init_cfg := initial_cfg p atksm init_store in
                            extract_trace (multistep atksm gas init_cfg).

End program_sem.

Module Notations.
  Notation "⟦ p ☠︎︎ a ⟧" := (prog_behavior p a).
End Notations.
*)

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac local_cook := ltac2:(cook this_cookbook).
