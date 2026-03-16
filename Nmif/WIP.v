(* Time to cook *)
From Stdlib Require Import ssreflect.

(* This may be useful *)
From QuickChick Require Import Decidability.

Require Import Util VarValStore Syntax Semantics.
Import Util.Dec.

Instance vli : ValPrm := {Vals := nat}.
Inductive EgVars := st | pt | pu | su. Instance eg_dec : DecEq EgVars. Proof. by dec_eq. Qed. (* I wonder whether there are better tactics *)
Instance vri : VarPrm := {Vars := EgVars}.


Parameter simple_cmd : Cmd.

Section holemode. Variable hole: forall T, T. Import Tacs.GallinaUtil.
  Parameter example_atk : ??.
  Parameter ideal_atk : ??.
  Import Semantics.Notations.

  Goal ⟦ ??  ⟧ = ⟦ ??  ⟧.

End holemode.
