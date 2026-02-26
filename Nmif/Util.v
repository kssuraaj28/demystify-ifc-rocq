From QuickChick Require Decidability.

(* Should this be #[global]? *)
Notation DecEq := Decidability.Dec_Eq.
Export (notations) Decidability.
Check (6 = 7)? : bool.
