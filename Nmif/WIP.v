(* This is the current thing I am working on.. *)

(* 
  I will define syntactic restriction on clean program, but with an attacklvl prm.
  We can then show that for this attack lvl prm, nmif is satisfied.

*)

From Stdlib Require (*Arith*) ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarVal CleanSyntax AtkSyntax SimSecurity.
Import VarVal CleanSyntax AtkSyntax.Prms CleanSyntax.

#[local] Notation CleanProg := CleanSyntax.Prog.

Section welltyped.
  Context `{!ValPrm, !VarPrm, !AdvLvlPrm}.

  Definition is_well_typed : pred CleanProg. Admitted.

End welltyped.

