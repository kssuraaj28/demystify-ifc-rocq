From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds CoTrace SimulatorRealIdeal.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds CoTrace SimulatorRealIdeal.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.


Section statements.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Coercion Attacker.step : Attacker >-> AdvNextStep.

  Fail Check "rename".
  Definition NMIFCRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      IdlAtkDowngradeRestr prog idlatk /\  FairIdlAtk prog rlatk idlatk /\ (* TODO: NMIFC restriction *)
      forall inp, ⟦ prog | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition NMIFRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      NMIFRestr idlatk /\  FairIdlAtk prog rlatk idlatk /\
      forall inp, ⟦ prog  | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition RDRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      RDRestr idlatk /\  FairIdlAtk prog rlatk idlatk /\
      forall inp, ⟦ prog  | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition TERealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      TERestr idlatk /\  FairIdlAtk prog rlatk idlatk /\
      forall inp, ⟦ prog  | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition NIRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      NIRestr idlatk /\  FairIdlAtk prog rlatk idlatk /\
      forall inp, ⟦ prog  | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.
End statements.

Section nmifc.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Notation "⊢ p" := (WellFormedProg ptlbl p) (at level 10).
  
  Theorem nmifc_real_ideal p: 
    ⊢ p -> 
    NMIFCRealIdeal p.
  Proof.
    move=> ? rl. 
    eexists; repeat split;
      exact: sim_idlatkrest ||
      exact: sim_fair ||
      exact: simulator_trace_eq.
  Qed.
End nmifc.

Section nmif.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Theorem nmif_real_ideal p: 
    NMIFCRealIdeal p -> 
    NMIFRealIdeal p.
  Proof.
    rewrite/NMIFCRealIdeal/NMIFRealIdeal=> + x=> /(_ x); move: x=> ?.
    case=> ? [] + []=> /restriction_impl=> /(_ false false).
    evar_spec_toph; [move=> + + _=> _ [] [] // [] ? [] //|].
    rewrite/AdvRestr=> - [atk] [restr] ? ? ?.
    exists atk.
    split=> //.
    split; [admit|].
    revert_hyp_pat [(forall st, _ ≈ˢ _), (forall st, _ ≈ʷ _)]; clear.
    move=> + + inp=> /(_ inp) + /(_ inp)=> *.
    apply: weq_seq_trans; eauto.
  Admitted.
End nmif.
