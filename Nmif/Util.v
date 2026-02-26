From QuickChick Require Decidability.

(* Should this be #[global]? *)
Notation DecEq := Decidability.Dec_Eq.

Module Notations.
  Export (notations) Decidability.
End Notations.
