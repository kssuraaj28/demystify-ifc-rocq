Supplementary material for 
"Demystifying Information Flow Downgrading Using the Real--Ideal Paradigm"

rocq_install.sh: install Rocq
dune build: build the project

Proofs scripts live in the Nmif/ directory:

    FinalRealIdeal.v : The main result. All main theorems print assumptions.

    Attacker.v : definition of attackers
    CoTrace.v : definition of infinite traces
    Combined.v : combined real-ideal configuration & operational semantics
    CombinedExtract.v : commutative lemmas for combined semantics
    ControlledDowngrade.v : definition of non-harmless downgrading
    DowngradeSyntaxRestriction.v : checking that a program does no downgrading
    FullLattice.v : the full lattice of heterogeneous principals
    FullTypeSystem.v : type system for IMPThreat with the full lattice
    IdlAtkPreds.v : predicates for constraining ideal attackers
    Lattice4pt.v : the 4-point lattice
    Noninterference.v : definition of noninterference
    Semantics.v : the operational semantics
    Simulator.v : simulator construction
    SimulatorRealIdeal.v : simulator real-ideal equivalence
    Syntax.v : IMPThreat syntax
    Tacs.v : tactic library
    TwoCfg.v : configuration combining program and attacker
    TypeSystem.v : type system for the 4-point lattice
    Util.v : utility definitions, lemmas, tactics
    VarValStore.v : definition of the store
    WfFinisher.v : finisher tactic library

There are no admits and the only axiom used is functional extensionality.
