From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem WfFinisher.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem WfFinisher Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section bug.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.

Parameter test : forall {T}, T.
  Lemma bug
    (P : _ -> Prop) 
    (adv : AdvNextStep AtkStates)
    (a : Cmd) (real_atk_bit : bool)
    (rs ss : Store) (ast : AtkStates)
    (eqp : ⟨ rs | is_public ⟩ = ⟨ ss | is_public ⟩)
    (wfa : WellFormedCmd {| untrusted := false; public := false |} a) 
    :
    P ⟨ clean_cmd_stp_store a (if real_atk_bit  then pre_cmd_action adv ast rs  else rs) | is_public ⟩.
  Proof.
    move=> *.
    wf_finisher_guess [ ⟨_|_⟩] with ⟨ match _ with _ => _ end |is_public⟩.
    exact test.
  Qed.

End bug.
