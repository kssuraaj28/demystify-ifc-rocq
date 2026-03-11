From Ltac2 Require Import Ltac2 Bool Control Printf.

#[local] Parameter admit_val : forall {T}, T.

#[local] Ltac2 admit_tac does_print := 
  if  (neg does_print) then () else 
  printf "The goal is  ~%t~" (goal ());
  exact admit_val.


Notation "??" := ltac2:(admit_tac false) (only parsing).
Notation "??!" := ltac2:(admit_tac true) (only parsing).


Check ?? + 5.
Check ?? + ??.
Check ??! + 5.

Compute  (match ??! with 
  | true => ??!
  | false => ??
  end).
