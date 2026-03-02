(* This is the current thing I am working on.. *)

(* 
  I will define syntactic restriction on clean program, but with an attacklvl prm.
  We can then show that for this attack lvl prm, nmif is satisfied.

*)

From Stdlib Require (*Arith*) ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarVal CleanSyntax AtkSyntax SimSecurity.
Import VarVal CleanSyntax AtkSyntax.Prms CleanSyntax MetaSyntax.

(* TODO: This notatio is stupid *)
#[local] Notation CleanProg := CleanSyntax.Cmd.

Section welltyped.
  Context `{!ValPrm, !VarPrm, !AdvLvlPrm}.

  (* The right way to define  *)
  (* TODO: Maybe abstract this out in MetaSyntax also*)
  Program Definition is_well_typed : pred CleanProg. Proof.
  refine (
    fun p =>
      match p with
      | skip => true
      | assign d exp => _
      | seq c1 c2 => _
      | cond cond_var b1 b2 => _
      | while cond_var body => _
      end).
    destruct 1. 

    Show Proof.

    fun p =>
      true.

End welltyped.

