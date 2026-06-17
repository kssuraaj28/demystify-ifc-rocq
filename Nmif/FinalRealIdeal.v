From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds CoTrace SimulatorRealIdeal.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds CoTrace SimulatorRealIdeal.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.


Section thm.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Variable (p : Prog).
  Hypothesis (wtprogram : WellFormedProg ptlbl p).

  Definition TypeSysRealIdl :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      IdlAtkDowngradeRestr p idlatk /\  FairIdlAtk p rlatk idlatk /\
      forall inp, ⟦ p | rlatk ⟧ inp ≈ʷ ⟦ p | idlatk  ⟧ inp.
  
  Theorem typesys_real_ideal: TypeSysRealIdl.
  Proof.
    move=> rl. 
    eexists; repeat split;
      exact: sim_idlatkrest ||
      exact: sim_fair ||
      exact: simulator_trace_eq.
  Qed.

End thm.
