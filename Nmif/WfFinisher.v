From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2 Printf.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem ControlledDowngrade Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section ni.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Lemma wf_cmd_st_conf_ni c l st1 st2:
      WellFormedCmd l c ->
      extract_controlled_declassify c = None ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof.
    case=> //.
      { move=> *;apply: update_to_store_storeview_eq; Attacker.local_cook; done. }
      { move=> > + + + /ltac:(exfalso)=> /= -> -> //. }
    { (* wf_assign *)
      move=> a pclbl Hsrc _ _ pubeq /=.
      case dpub: [elaborate (is_public (get_assign_dest a))]; cycle 1.
        { rewrite !update_storeview_nochange //. }
      have psrc : public (asgn_src_lbl a); [exact: (flows_to_pub _ _ dpub Hsrc)|].
      have Hval : get_assign_val st1 a = get_assign_val st2 a.
      { move: psrc; case: a {Hsrc dpub} => /=.
        - move=> src d psrc /=; rewrite (storeview_eq _ _ _ src pubeq) //.
        - move=> src d psrc /=; rewrite (storeview_eq _ _ _ src pubeq) //.
        - move=> [[v1 v2] comp] d Hp.
          have pv1 : is_public v1.
          { move: Hp; rewrite /asgn_src_lbl /is_public.
            case: (var_lbl v1) => u1 p1; case: (var_lbl v2) => u2 p2 /= /andP[h _]; exact: h. }
          have pv2 : is_public v2.
          { move: Hp; rewrite /asgn_src_lbl /is_public.
            case: (var_lbl v1) => u1 p1; case: (var_lbl v2) => u2 p2 /= /andP[_ h]; exact: h. }
          rewrite /eval_val_exp /= (storeview_eq _ _ _ v1 pubeq pv1) (storeview_eq _ _ _ v2 pubeq pv2) //. }
      rewrite /clean_assign_stp_store Hval. apply: update_same_varval; exact: pubeq. }
  Qed.

  
  (* In a secret context, the public view is constant *)
  Lemma wf_sec_cmd_st_conf_ni:
    forall c i st,
      WellFormedCmd (mk_lbl i false) c ->
      ⟨ clean_cmd_stp_store c st | is_public ⟩ =
      ⟨ st | is_public ⟩.
  Proof. 
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap].
    case=> //= > ++e; rewrite -{}e => *.
    rewrite update_storeview_nochange=> //.
    rewrite/is_public.
    apply/negbTE/flows_from_sec; rewrite/secret; eauto; done.
  Qed.

  Lemma wf_cmd_st_int_ni c l st1 st2:
      WellFormedCmd l c ->
      extract_controlled_endorse c = None ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof.
    case=> //.
      { move=> > + + + /ltac:(exfalso)=> /= -> -> //. }
      { move=> *;apply: update_to_store_storeview_eq; Attacker.local_cook; done. }
    { (* wf_assign *)
      move=> a pclbl Hsrc _ _ treq /=.
      case dtr: [elaborate (is_trusted (get_assign_dest a))]; cycle 1.
        { rewrite !update_storeview_nochange //. }
      have tsrc : trusted (asgn_src_lbl a); [exact: (flows_to_tr _ _ dtr Hsrc)|].
      have Hval : get_assign_val st1 a = get_assign_val st2 a.
      { move: tsrc; case: a {Hsrc dtr} => /=.
        - move=> src d tsrc /=; rewrite (storeview_eq _ _ _ src treq) //.
        - move=> src d tsrc /=; rewrite (storeview_eq _ _ _ src treq) //.
        - move=> [[v1 v2] comp] d Hp.
          have pv1 : is_trusted v1.
          { move: Hp; rewrite /asgn_src_lbl /is_trusted /is_untrusted /trusted.
            case: (var_lbl v1) => u1 p1; case: (var_lbl v2) => u2 p2 /=; rewrite negb_or => /andP[h _]; exact: h. }
          have pv2 : is_trusted v2.
          { move: Hp; rewrite /asgn_src_lbl /is_trusted /is_untrusted /trusted.
            case: (var_lbl v1) => u1 p1; case: (var_lbl v2) => u2 p2 /=; rewrite negb_or => /andP[_ h]; exact: h. }
          rewrite /eval_val_exp /= (storeview_eq _ _ _ v1 treq pv1) (storeview_eq _ _ _ v2 treq pv2) //. }
      rewrite /clean_assign_stp_store Hval. apply: update_same_varval; exact: treq. }
  Qed.
  (* TODO repair (constructors changed shape):
    move=> [] // d s1 s2 ? ?.
      { apply: update_to_store_storeview_eq. rewrite /is_trusted /is_untrusted s2 //. }
    case de: ([elaborate is_untrusted d])=> fs1d fs2d _ _ treq /=;
      [do 2 (rewrite update_storeview_nochange{1}/is_trusted; [rewrite de //|])=> //|].
    rewrite/is_trusted/is_untrusted/= in de.
    move: de=>/untrusted_false td.
    move: (flows_to_tr _ _ td fs1d)=> {fs1d} ts1.
    move: (flows_to_tr _ _ td fs2d)=> {fs2d} ts2.
    set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
    set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
    suff: v1 = v2; [move=> ->; apply/update_same_varval=> //|subst v1 v2].
    rewrite /get_assign_val /eval_val_exp /=.
    f_equal; eauto using storeview_eq.
  *)


  Fact wf_optcmd_st_conf_ni l oc st1 st2:
      l ⊢ oc ->
      oapp extract_controlled_declassify None oc = None ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ optcmd_stp_store oc st1 | is_public ⟩ = ⟨ optcmd_stp_store oc st2 | is_public ⟩.
  Proof.
    case: oc => //= c wf nodecl pubeq.
    exact: wf_cmd_st_conf_ni wf nodecl pubeq.
  Qed.

  Fact wf_sec_optcmd_st_conf_ni i oc s:
    mk_lbl i false ⊢ oc ->
    ⟨ optcmd_stp_store oc s | is_public ⟩ = ⟨ s | is_public ⟩.
  Proof. case: oc => //= c wf. exact: wf_sec_cmd_st_conf_ni wf. Qed.

  Lemma wf_untr_cmd_st_int_ni:
    forall p c st,
    WellFormedCmd (mk_lbl true p) c ->
    ⟨ clean_cmd_stp_store c st | is_trusted ⟩ = ⟨ st | is_trusted ⟩.
  Proof.
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap].
    case=> //= > ++ /ltac:(dotop [idtac])=> <- /[swap].
    move/flows_from_untr=> /=. evar_spec_toph=> // + _.
    rewrite/asgn_dst_lbl-/(get_assign_dest _).
    move=> + /ltac:(apply: update_storeview_nochange=> //).
    move: (get_assign_dest _)=> ?.
    rewrite/is_trusted/is_untrusted=> -> //.
  Qed.

  Fact wf_untr_optcmd_st_int_ni p oc s:
    mk_lbl true p ⊢ oc ->
    ⟨ optcmd_stp_store oc s | is_trusted ⟩ = ⟨ s | is_trusted ⟩.
  Proof. case: oc => //= c wf. exact: wf_untr_cmd_st_int_ni wf. Qed.

  Lemma wf_tr_cmd_cnt_ni p p' c st1 st2:
      WellFormedCmd (mk_lbl false p) c ->
      compute_new_pc (mk_lbl false p) c = mk_lbl false p' ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof. 
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap].
    case=> // > => [++ <- | + <- ]=> * /=.
    1,2: pattern_eq_2 [X in _ = (if (_ X) then _ else _)] [X in (if (_ X) then _ else _) = _]=> [|->] //.
    1,2: apply:storeview_eq; [symmetry;eassumption | ].
    1,2: revert_hyp_pat (compute_new_pc _ _ = _)=> /=; rewrite/is_trusted/is_untrusted; case: var_lbl=> - [] [] //. (* TODO: Should be in Lattice4pt *)
  Qed.

  Lemma wf_cmd_st_end c l cc st1 st2:
      WellFormedCmd l c ->
      extract_controlled_endorse c = Some cc ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof.
    move=> _; case: cc=> [from to] /extr_endorse_eq [-> [efrom eto]] pubeq /=.
    apply: update_to_store_storeview_eq; [rewrite /is_public efrom // | exact: pubeq].
  Qed.

End ni.

Ltac2 mutable wf_finisher_debug : int := 0.
(* Print [msg] when wf_finisher_debug is at least [lvl]. *)
Ltac2 wf_dbg (lvl : int) (msg : message) : unit :=
  if Int.ge wf_finisher_debug lvl then Message.print msg else ().

(* TODO: Eventually, we should have a pattern that let's us not have these versions for optional cmd and so on *)
Ltac2 wf_finisher_arms () : unit :=
  goal_assertion 1 "wf_finisher_rec";
  let lemmas : Std.reference list := [
    reference:(wf_cmd_st_conf_ni); (* References are parse time! *)
    reference:(wf_optcmd_st_conf_ni);
    reference:(wf_sec_cmd_st_conf_ni);
    reference:(wf_sec_optcmd_st_conf_ni);
    reference:(wf_cmd_st_int_ni);
    reference:(wf_untr_cmd_st_int_ni);
    reference:(wf_untr_optcmd_st_int_ni);
    reference:(wf_tr_cmd_cnt_ni);
    reference:(pre_cmd_wf_int);
    reference:(pre_cmd_wf_conf);
    reference:(post_cmd_wf)
  ] in
  let apply_lemma (c : constr) : unit := ltac1:(c |- apply: [elaborate c]) (Ltac1.of_constr c) in (* ssr apply: fails in some other file. TODO: Debug *)
  let rec or_all l :=
    match l with
    | [] => softfail_s "wf_finisher_arms" "no lemma applies"
    | r :: rest =>
      Control.plus
      (fun _ =>
        let c := Env.instantiate r in
        wf_dbg 3 (fprintf "wf_finisher_arms: trying %t" c);
        apply_lemma c)
      (fun _ =>
        or_all rest)
    end in
  or_all lemmas.

Ltac2 wf_finisher_close () : unit :=
  goal_assertion 1 "wf_finisher_rec";
  first [
    wf_dbg 3 (fprintf "close: reflexivity branch");
    if Constr.has_evar (Control.goal ()) then Control.zero (Tactic_failure None) else reflexivity |
    wf_dbg 3 (fprintf "close: eassumption branch"); eassumption |
    wf_dbg 3 (fprintf "close: symmetry; eassumption branch"); symmetry; eassumption];
  goal_assertion 0 "wf_finisher_rec". (* TODO: There's this whole assert_goals_hard thing or whatever. Maybe I just need this *)

(* TODO: We don't need n I think *)
Ltac2 rec wf_finisher_rec (n : int) : unit :=
  harden 0 (
  goal_assertion 1 "wf_finisher_rec";
  if Int.equal n 0 then panic_s "wf_finisher_rec" "out of fuel" else
  Control.plus
    (fun () => wf_finisher_close ())
    (fun _ =>
      lazy_match! goal with
      | [ |- _ = _ ] => ()
      | [ |- _ ] => softfail_s "wf_finisher_rec" "goal is not an equation" (* TODO: Why softfail? *)
      end;
      Control.plus 
         (fun _  => wf_dbg 3 (fprintf "nosym branch"))
         (fun _ => wf_dbg 3 (fprintf "sym branch"); symmetry);
      wf_finisher_arms (); 
      Control.enter (fun () => wf_finisher_rec (Int.sub n 1)))).
      

Ltac2 wf_finisher () := wf_finisher_rec 5.
Ltac wf_finisher := ltac2:(wf_finisher ()).

Goal 5 = 5. wf_finisher.  Abort.  (* TODO!!!  assert_fails also succeeds!!  WHAT *)

Section test.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->    extract_controlled_declassify c = None ->
    ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st2 | is_public ⟩ = ⟨ st1 | is_public ⟩ ->    extract_controlled_declassify c = None ->
    ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall l c st1 st2, WellFormedCmd l c ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->    extract_controlled_endorse c = None ->
    ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall i c st, WellFormedCmd (mk_lbl i false) c ->
    ⟨ clean_cmd_stp_store c st | is_public ⟩ = ⟨ st | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall p c st, WellFormedCmd (mk_lbl true p) c ->
    ⟨ clean_cmd_stp_store c st | is_trusted ⟩ = ⟨ st | is_trusted ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast l c s1 s2,
    WellFormedCmd l c ->
    extract_controlled_declassify c = None ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (clean_cmd_stp_store c (pre_cmd_action adv ast s1)) =
    post_cmd_action adv ast (clean_cmd_stp_store c (pre_cmd_action adv ast s2)).
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast l oc s1 s2,
    l ⊢ oc ->
    oapp extract_controlled_declassify None oc = None ->
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s1)) =
    post_cmd_action adv ast (optcmd_stp_store oc (pre_cmd_action adv ast s2)).
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast i oc s,
    mk_lbl i false ⊢ oc ->
    post_cmd_action adv ast (optcmd_stp_store oc s) = post_cmd_action adv ast s.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall p p' c st1 st2,
    WellFormedCmd (mk_lbl false p) c ->
    compute_new_pc (mk_lbl false p) c = mk_lbl false p' ->
    ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
    clean_cmd_stp_cnt c st1 = clean_cmd_stp_cnt c st2.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s,
    ⟨ pre_cmd_action adv ast s | is_trusted ⟩ = ⟨ s | is_trusted ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s1 s2,
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    ⟨ pre_cmd_action adv ast s1 | is_public ⟩ = ⟨ pre_cmd_action adv ast s2 | is_public ⟩.
  Proof. move=> *. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s1 s2,
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (pre_cmd_action adv ast s1) =
    post_cmd_action adv ast (pre_cmd_action adv ast s2).
  Proof. move=> *. wf_finisher. Qed.

  Goal forall s s',
    ⟨ s | is_trusted ⟩ = ⟨ s' | is_trusted ⟩ ->
    ⟨ s' | is_trusted ⟩ = ⟨ s | is_trusted ⟩.
  Proof. move=> *. wf_finisher. Qed.
End test.

(* TODO: This Ltac1.t is weird. Maybe later *)
Ltac2 wf_finisher_guess_aux (pat : Ltac1.t) (u : preterm) : unit :=
  let wf_partial_tac := ltac1:(p v |- pattern_eq [p] with v) pat in
  let acc : constr list ref := { contents := [] } in

  let run_probe (k : constr -> unit) : unit :=
    let v := Constr.Pretype.pretype Constr.Pretype.Flags.open_constr_flags_with_tc Constr.Pretype.expected_without_type_constraint u in
    wf_partial_tac (Ltac1.of_constr v);
    wf_dbg 2 (fprintf "wf_finisher_guess: pattern_eq ok, %i goals" (Control.numgoals ()));
    Control.focus 1 1 (fun () =>
      wf_finisher ();
      k v) in

  let fail_runner () := run_probe (fun v =>
    let v' := clone_constr v in
    wf_dbg 1 (fprintf "wf_finisher_guess: candidate v = %t" v');
    acc.(contents) := v' :: acc.(contents);
    Control.zero (Tactic_failure None)) in

  (* We re-guess because of weird universe quality bug *)
  let final_runner v_init_guess :=
    wf_dbg 1 (fprintf "wf_finisher_guess: replay with v = %t" v_init_guess);
    run_probe (fun v_final =>
      if Constr.equal v_init_guess v_final then () else (* Does not compare universe quality or whatnot *)
      panic_s "wf_finisher_guess" "probe candidate diverges on replay") in

  wf_dbg 1 (fprintf "wf_finisher_guess: probe begin");
  match Control.case (fail_runner) with
  | Val _ => panic_s "wf_finisher_guess" "unreachable: probe loop must Control.zero"
  | Err e =>
    wf_dbg 1 (fprintf "wf_finisher_guess: probe end");
    wf_dbg 2 (fprintf "wf_finisher_guess: probe loop exit: %a" (fun () e' => Message.of_exn e') e);
    let dedup := List.fold_right (fun c acc =>
      if List.exist (Constr.equal c) acc then acc else c :: acc) (acc.(contents)) [] in
    wf_dbg 1 (fprintf "wf_finisher_guess: %i unique candidate(s)" (List.length dedup));
    match dedup with
    | [v_single] =>
      match Control.case (fun () => final_runner v_single) with
      | Err _ => panic_s "wf_finisher_guess" "Final call should not fail"
      | _ => ()
      end
    | _ =>
      Message.print (Message.of_string "Guess list");
      List.iter (fun c => Message.print (Message.of_constr c)) dedup;
      panic_s "wf_finisher_guess" "ambiguous (or no) guess"
    end
  end.

Tactic Notation "wf_finisher_guess" "[" ssrpatternarg(p) "]" "with" uconstr(u) :=
  let f := ltac2:(p u |- wf_finisher_guess_aux p (Option.get (Ltac1.to_preterm u))) in
  f p u.

Section test.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast l c s1 s2,
    WellFormedCmd l c ->
    extract_controlled_endorse c = None ->
    ⟨ s1 | is_trusted ⟩ = ⟨ s2 | is_trusted ⟩ ->
    ⟨ clean_cmd_stp_store c (pre_cmd_action adv ast s1) | is_trusted ⟩ =
    ⟨ clean_cmd_stp_store c s2 | is_trusted ⟩.
  Proof.
    move=> *.
    unshelve (wf_finisher_guess [RHS] with ⟨ clean_cmd_stp_store _ _ | _ ⟩ => ->).
    wf_finisher.
    Restart.
    move=> ????? st *.
    wf_finisher_guess [LHS] with ⟨ clean_cmd_stp_store _ st | _ ⟩ => ->.
    wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast p p' c s1 s2,
    WellFormedCmd (mk_lbl false p) c ->
    compute_new_pc (mk_lbl false p) c = mk_lbl false p' ->
    ⟨ s1 | is_trusted ⟩ = ⟨ s2 | is_trusted ⟩ ->
    clean_cmd_stp_cnt c (pre_cmd_action adv ast s1) = clean_cmd_stp_cnt c s2.
  Proof. move=> *. wf_finisher_guess [RHS] with _=> ->. wf_finisher. Qed.

  Goal forall {AtkStates} (adv : AdvNextStep AtkStates) ast s1 s2,
    ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
    post_cmd_action adv ast (pre_cmd_action adv ast s1) =
    post_cmd_action adv ast (pre_cmd_action adv ast s2).
  Proof. move=> *.
  wf_finisher_guess [post_cmd_action _ _ _] with _ => -> //.
  Qed.

  Goal forall (P : StoreView -> Prop) s s',
    ⟨ s | is_trusted ⟩ = ⟨ s' | is_trusted ⟩ ->
    P (⟨ s' | is_trusted ⟩) ->
    P (⟨ s | is_trusted ⟩).
  Proof. move=> *. wf_finisher_guess [⟨ _ | is_trusted ⟩] with _ => ->. auto. Qed.

  Goal forall (P : StoreView -> Prop) s s',
    ⟨ s | is_trusted ⟩ = ⟨ s' | is_trusted ⟩ ->
    P (⟨ s | is_trusted ⟩) ->
    P (⟨ s' | is_trusted ⟩).
  Proof. move=> *. wf_finisher_guess [⟨ _ | is_trusted ⟩] with _ => ->. auto. Qed.
End test.
