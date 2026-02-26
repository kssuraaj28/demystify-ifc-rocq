From Ltac2 Require Import Ltac2. Set Default Proof Mode "Classic".

Ltac2 goals l :=
  let name_goal x := ltac1:(x |- refine ?[x]) (Ltac1.of_ident x) in
  Control.dispatch (List.map (fun x () => name_goal x) l).

(* This can be used in more places. TODO *)
Ltac hnf_clean def :=
    let t := def in
    let t := eval red in t in 
    let t := eval hnf in t in 
    exact t.
