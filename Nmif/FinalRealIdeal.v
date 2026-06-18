From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds CoTrace SimulatorRealIdeal DowngradeSyntaxRestriction.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds CoTrace SimulatorRealIdeal DowngradeSyntaxRestriction.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.


Section statements.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Coercion Attacker.step : Attacker >-> AdvNextStep.

  Definition NMIFCRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      NMIFCRestr prog idlatk /\  FairIdlAtkRestr prog rlatk idlatk /\ 
      forall inp, ⟦ prog | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition NMIFRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      NMIFRestr idlatk /\  FairIdlAtkRestr prog rlatk idlatk /\
      forall inp, ⟦ prog  | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition RDRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      RDRestr idlatk /\  FairIdlAtkRestr prog rlatk idlatk /\
      forall inp, ⟦ prog  | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition TERealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      TERestr idlatk /\  FairIdlAtkRestr prog rlatk idlatk /\
      forall inp, ⟦ prog  | rlatk ⟧ inp ≈ʷ ⟦ prog | idlatk  ⟧ inp.

  Definition NIRealIdeal prog :=
    forall (rlatk : Attacker), exists (idlatk: Attacker),
      NIRestr idlatk /\  FairIdlAtkRestr prog rlatk idlatk /\
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
    case=> ? [] + []=> /restriction_impl=> /(_ false false); rewrite/AdvRestr.
    evar_spec_toph; [move=> + + _=> _ [] [] // [] ? [] //|].
    rewrite/AdvRestr => -  [atk]  [restr] [fair] + {}/fair=> ? ? ?.  
    exists atk.
    do 2 split=> //.
    revert_hyp_pat [(forall st, _ ≈ˢ _), (forall st, _ ≈ʷ _)]; clear.
    move=> + + inp=> /(_ inp) + /(_ inp)=> *.
    apply: weq_seq_trans; eauto.
  Qed.
End nmif.

Section te.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Theorem te_real_ideal p: 
    NMIFCRealIdeal p -> declassify_absent p ->
    TERealIdeal p.
  Proof.
    rewrite/NMIFCRealIdeal/TERealIdeal=> + ?=> + x=> /(_ x); move: x=> ?.
    case=> ? [] + []=> /restriction_impl=> /(_ false true); rewrite/AdvRestr.
    evar_spec_toph; [exact:dwnrd_rstrct_sound|].
    rewrite/AdvRestr => -  [atk]  [restr] [fair] + {}/fair=> ? ? ?.  
    exists atk.
    do 2 split=> //.
    revert_hyp_pat [(forall st, _ ≈ˢ _), (forall st, _ ≈ʷ _)]; clear.
    move=> + + inp=> /(_ inp) + /(_ inp)=> *.
    apply: weq_seq_trans; eauto.
  Qed.

End te.

Section rd.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Theorem rd_real_ideal p: 
    NMIFCRealIdeal p -> endorse_absent p ->
    RDRealIdeal p.
  Proof.
    rewrite/NMIFCRealIdeal/RDRealIdeal=> + ? => + x=> /(_ x); move: x=> ?.
    case=> ? [] + []=> /restriction_impl=> /(_ true false); rewrite/AdvRestr.
    evar_spec_toph; [exact:dwnrd_rstrct_sound|].
    rewrite/AdvRestr => -  [atk]  [restr] [fair] + {}/fair=> ? ? ?.  
    exists atk.
    do 2 split=> //.
    revert_hyp_pat [(forall st, _ ≈ˢ _), (forall st, _ ≈ʷ _)]; clear.
    move=> + + inp=> /(_ inp) + /(_ inp)=> *.
    apply: weq_seq_trans; eauto.
  Qed.

End rd.


Section ni.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Theorem ni_real_ideal p: 
    NMIFCRealIdeal p -> downgrade_absent p ->
    NIRealIdeal p.
  Proof.
    rewrite/NMIFCRealIdeal/NIRealIdeal=> + ? => + x=> /(_ x); move: x=> ?.
    case=> ? [] + []=> /restriction_impl=> /(_ true true); rewrite/AdvRestr.
    evar_spec_toph; [exact:dwnrd_rstrct_sound|].
    rewrite/AdvRestr => -  [atk]  [restr] [fair] + {}/fair=> ? ? ?.  
    exists atk.
    do 2 split=> //.
    revert_hyp_pat [(forall st, _ ≈ˢ _), (forall st, _ ≈ʷ _)]; clear.
    move=> + + inp=> /(_ inp) + /(_ inp)=> *.
    apply: weq_seq_trans; eauto.
  Qed.

End ni.
