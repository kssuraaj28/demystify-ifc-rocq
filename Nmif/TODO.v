From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem WfFinisher.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem WfFinisher Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section ni.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  Notation AdvNextStep := (AdvNextStep (AtkStates := AtkStates)).

  Lemma update_untr_keep_view s1 s2 v vl :
      is_untrusted v ->
      ⟨ s1 | is_trusted ⟩ = ⟨ s2 | is_trusted ⟩ ->
      ⟨ s1 | is_trusted ⟩ = ⟨ update_to_store s2 v vl | is_trusted ⟩.
  Proof.
    move=> untrv treq.
    have htv : is_trusted v = false.
    { rewrite /is_trusted; move: untrv; case: (is_untrusted v) => //. }
    rewrite (update_storeview_nochange _ _ _ _ htv).
    exact: treq.
  Qed.

  Lemma endorse_pre_read_eq from to s1 s2:
      is_public from ->
      ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
      clean_assign_stp_store (endorse from to) s2 from = s1 from.
  Proof.
    move=> pubfrom pubeq.
    have ->: clean_assign_stp_store (endorse from to) s2 from = s2 from.
    { rewrite /clean_assign_stp_store /get_assign_dest /get_assign_val /update_to_store /=.
      case: (Util.DecEq.dec_eq _ _) => //. }
    apply: storeview_eq; eauto.
  Qed.

  Lemma wf_endorse_st_int from to st1 st2:
      st1 from = st2 from ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      ⟨ clean_cmd_stp_store (assign (endorse from to)) st1 | is_trusted ⟩ =
      ⟨ clean_cmd_stp_store (assign (endorse from to)) st2 | is_trusted ⟩.
  Proof.
    move=> eqfrom treq.
    rewrite /clean_cmd_stp_store /= /clean_assign_stp_store /get_assign_dest /get_assign_val /=.
    rewrite eqfrom.
    exact: update_same_varval treq.
  Qed.

  Lemma declassify_pubeq  (adv : AdvNextStep) ast
    from to real_store ideal_store sim_store :
    var_lbl from = mk_lbl false false ->
    var_lbl to = mk_lbl false true ->
    ⟨ real_store | is_trusted ⟩ = ⟨ ideal_store | is_trusted ⟩ ->
    ⟨ real_store | is_public ⟩ = ⟨ sim_store | is_public ⟩ ->
    ⟨ update_to_store (pre_cmd_action adv ast sim_store) to (ideal_store from) | is_public ⟩ =
    ⟨ update_to_store (pre_cmd_action adv ast real_store) to (pre_cmd_action adv ast real_store from) | is_public ⟩.
  Proof.
    move=> Hfrom Hto treq pubeq.
    have tfrom : is_trusted from; [rewrite /is_trusted /is_untrusted Hfrom //|].
    have valeq : pre_cmd_action adv ast real_store from = ideal_store from.
    { rewrite (storeview_eq _ _ _ from (pre_cmd_wf_int adv ast real_store) tfrom).
      exact: (storeview_eq _ _ _ from treq tfrom). }
    rewrite valeq.
    apply: update_same_varval.
    exact: (pre_cmd_wf_conf adv ast _ _ (esym pubeq)).
  Qed.
End ni.
