From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Semantics Lattice4pt CoTrace.
Import Tacs Util VarValStore Attacker Syntax Semantics Lattice4pt CoTrace Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section twocfg.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.

  Notation State1 := (State (AtkStates:=AtkStates1)).  Notation State2 := (State (AtkStates:=AtkStates2)).

  Definition TwoCfg := (list (AtkCmd * AtkCmd) * State1 * State2)%type.
End twocfg.

Section twoinit.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable 
     (p : Prog) (init_store: Store)
     (adv1: AdvInit (AtkStates := AtkStates1)) 
     (adv2: AdvInit (AtkStates := AtkStates2)).

  Notation TwoCfg := (TwoCfg (AtkStates1 := AtkStates1) (AtkStates2 := AtkStates2)).

  Definition init_twocfg : TwoCfg :=
    (map (fun c => let ac := mk_atkcmd true (Some c) in (ac ,ac) ) p,  
    (init_store, init_fn adv1 init_store), (init_store, init_fn adv2 init_store)).
End twoinit.



Section twostep.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable  (adv1: AdvNextStep (AtkStates := AtkStates1))  (adv2: AdvNextStep (AtkStates := AtkStates2)).
  Definition twostep (c: TwoCfg): TwoCfg :=
    let: (c2lst, s1, s2) := c in
    if c2lst isn't (ac1, ac2) :: rest then c (*, (blank_event, blank_event) *) else
    let: (p1, st1 (*, ev1 *), steps1) := (acmd_step adv1 ac1 s1) in
    let: (p2, st2 (*, ev2 *), steps2) := (acmd_step adv2 ac2 s2) in

    let: cont := combine_extend4
                   (map Some p1) (repeat true steps1)
                   (map Some p2) (repeat true steps2)
                   None false None false in
    let: cont := map (fun '(oc1, a1, oc2, a2) => (mk_atkcmd a1 oc1, mk_atkcmd a2 oc2)) cont in
    (cont ++ rest, st1, st2).


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
End twostep.


Section twooneextract.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable  
    (adv1: AdvNextStep (AtkStates := AtkStates1)) 
    (adv2: AdvNextStep (AtkStates := AtkStates2)).

  Notation TwoCfg := (TwoCfg (AtkStates1:=AtkStates1) (AtkStates2:=AtkStates2)).
  Notation State1 := (State (AtkStates:=AtkStates1)).
  Notation State2 := (State (AtkStates:=AtkStates2)).

  Definition extract_one_cfg (is_left : bool) (c : TwoCfg) :=
    let: (aclst, s1, s2) := c in
    let: aclst :=
      filter is_running
        (map (if is_left then fst else snd) aclst) in
    if is_left as b return Cfg (AtkStates := if b then AtkStates1 else AtkStates2)
    then (aclst, s1) else (aclst, s2).

  Definition extract_one_event (is_left : bool) (c: TwoCfg) : Event :=
    let: (e1, e2) := twoevent adv1 adv2 c in
    if is_left then e1 else e2.

End twooneextract.

Section twooneinitsound.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.

  Variable 
     (p : Prog) (init_st: Store) (b: bool)
     (adv1: AdvInit (AtkStates := AtkStates1)) 
     (adv2: AdvInit (AtkStates := AtkStates2)).

  Notation adv b := (if b as b' return (_ (if b' then _ else _)) then adv1 else adv2).

  Lemma extract_inittwo:
    extract_one_cfg b (init_twocfg p init_st adv1 adv2) = init_cfg p (adv b) init_st.
  Proof.
    rewrite/extract_one_cfg/init_cfg/= map_map filter_map_swap /is_running /= . 
    case: b=> /=; rewrite filter_true //.
  Qed.
End twooneinitsound.

Section twoonestepsound.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable  
    (adv1: AdvNextStep (AtkStates := AtkStates1)) 
    (adv2: AdvNextStep (AtkStates := AtkStates2)).

  Notation TwoCfg := (TwoCfg (AtkStates1:=AtkStates1) (AtkStates2:=AtkStates2)).
  Notation State1 := (State (AtkStates:=AtkStates1)).
  Notation State2 := (State (AtkStates:=AtkStates2)).

  Notation extract_one_event := (extract_one_event adv1 adv2).
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
End twoonestepsound.

(* Another function from twocfg to onecfg *)
Section cfg_erase_filter.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates1 AtkStates2 : Type}.
  Variable  
    (adv1: AdvNextStep (AtkStates := AtkStates1)) 
    (adv2: AdvNextStep (AtkStates := AtkStates2)).

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

  Lemma extract_one_erase_idem b c :
    extract_one_cfg b c = extract_one_cfg b (erase_filter_cfg b c).
  Proof.
    case: c => [[p st1] st2]; rewrite /extract_one_cfg /erase_filter_cfg.
    case: b => /=; Util.local_cook.
    1,2: rewrite !filter_map_swap.
    1,2: rewrite filter_filter; congr map.
    1,2: apply: filter_ext=> - [] /= *; Util.local_cook.
  Qed.

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


Section twocfg_swap_atk.
  Import VarValStore.Notations Util.DecEq Util.DecEq.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}. 
  
  Context (prog: Prog).
  Context (nonswpatk : Attacker).
  Notation ainitold := (init nonswpatk).
  Notation astepold := (Attacker.step nonswpatk).

  Context {AtkStatesSwp : Type} 
    (ainitnew : AdvInit (AtkStates := AtkStatesSwp)) 
    (astep1: AdvNextStep (AtkStates := AtkStatesSwp))
    (astep2: AdvNextStep (AtkStates := AtkStatesSwp)).

  Notation init_fn inp := (init_cfg prog ainitnew inp).
  Notation step1 := (step astep1).  Notation event1 := (event astep1).
  Notation step2 := (step astep2).  Notation event2 := (event astep2).

  Notation twoinit_fn inp := (init_twocfg prog inp ainitold ainitnew).
  Notation twostep1 := (twostep astepold astep1).  Notation twoevent1 := (twoevent astepold astep1).
  Notation twostep2 := (twostep astepold astep2).  Notation twoevent2 := (twoevent astepold astep2).

  Notation StepEqHyp :=
    (forall inp final_cfg, 
      reachable step1 (init_fn inp) final_cfg ->
      step1 final_cfg = step2 final_cfg /\ event1 final_cfg = event2 final_cfg) (only parsing).


  (* TODO: Parameterize eventually *)
  Lemma twocfg_swap_atk:
    StepEqHyp ->
    forall inp final_cfg, 
      reachable twostep1 (twoinit_fn inp) final_cfg ->
      twostep1 final_cfg = twostep2 final_cfg /\ twoevent1 final_cfg = twoevent2 final_cfg.
  Proof.
    move=> + x=> /(_ x); move: x=> ?. (* TODO: Should just be apply*)
    move=> ih [] [] [] // [].
    move=> c1 c2 > rch.
    rewrite/twostep1/twostep2 /step1/step2 in ih *.
  Admitted.
End twocfg_swap_atk.
