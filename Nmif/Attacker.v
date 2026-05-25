From Stdlib Require Program ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore Util Noninterference Lattice4pt Tacs. 
Import VarValStore Noninterference VarValStore.Notations Tacs Tacs.Cook. 

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Class AdvLeakPrm := LeakVals : Type.

Class AdvLvlPrm `{!VarPrm} :=  var_lbl : Vars -> Lattice4pt.Label.

Section defs.
  Import Lattice4pt.
  Context `{!VarPrm, !AdvLvlPrm}.
  Definition is_public v := public (var_lbl v).
  Definition is_untrusted v := untrusted (var_lbl v).
  Definition is_secret v := ~~ is_public v.
  Definition is_trusted v := ~~ is_untrusted v.
End defs.



(* 
  TODO
  You need to eventually corrupt store,
  Learn from store etc 
*)
(* 
  The attacker is sandwiched between the normal code... 
  corrupt ; cmd;  learn ; leak || substeps

  Another thing we could do is something where
  you also get access to pc?  TODO

  Prm naming scheme? TODO
*)

Definition AdvEvent `{!AdvLeakPrm} := option LeakVals.

(* Previously this record also carried
     init_state : StoreView -> AtkStates
   (the attacker only sees the untrusted view) together with a TODO for an
   init_state well-formedness obligation. Dropped during the rename to
   AdvNextStep — initial-state construction now lives outside this record. *)
Record AdvNextStep `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}
    {AtkStates : Type} := {
    (* Corruption *)
    pre_cmd_action: AtkStates -> Store -> Store;
 
    pre_cmd_wf_int: 
      forall ast, 
        let: ast_corr := pre_cmd_action ast in
        let: tr_view := (store_to_view is_trusted) in
        (forall st, tr_view (ast_corr st) = (tr_view st));  (* The adversary does not touch trusted computation. This is a little bit ugly *)

    pre_cmd_wf_conf: 
      forall ast, 
        let: ast_corr := pre_cmd_action ast in
        let: pub_view := (store_to_view is_public) in 
        Noninterfering pub_view ast_corr pub_view; (* public outputs don't chnage if public inputs don't *)


    post_cmd_action: AtkStates -> Store -> (AtkStates * (*AdvEvent * *) nat); (* New state, event, and substeps *)
    post_cmd_wf:
      forall ast,
        let: ast_lrn := post_cmd_action ast in
        let: pub_view := store_to_view is_public in
        Noninterfering pub_view ast_lrn id;

  }.

Arguments AdvNextStep: clear implicits.
Arguments AdvNextStep {_ _ _ _} AtkStates.

Lemma noninterfering_post_pre `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}
  {AtkStates} (adv : AdvNextStep AtkStates) ast s1 s2 :
  ⟨ s1 | is_public ⟩ = ⟨ s2 | is_public ⟩ ->
  post_cmd_action adv ast (pre_cmd_action adv ast s1) =
  post_cmd_action adv ast (pre_cmd_action adv ast s2).
Proof.  move=> hyp.  apply: post_cmd_wf.  apply: pre_cmd_wf_conf. done. Qed.

Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> pre_cmd_wf_int) "pre_cmd_wf_int" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(unshelve erewrite pre_cmd_wf_conf;[|reflexivity|]) "pre_cmd_wf_conf" old.
  (* TODO: I think maybe apply is better? TODO *)

Ltac2 this_cookbook () := this_cookbook_ ().
Ltac2 Eval print_cookbook this_cookbook.

Section test.
  Context `{!VarPrm,!ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Generalizable All Variables.
  Ltac2 Set curr_cookbook := this_cookbook. 

  Goal `(forall P, P ⟨ pre_cmd_action (AtkStates := A) adv ast st  | is_trusted ⟩).
  Proof.   move=> *.  cook.  Abort.
End test.
