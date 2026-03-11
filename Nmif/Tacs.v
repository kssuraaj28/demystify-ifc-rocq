From Ltac2 Require Import Ltac2 Bool Control Printf.

Ltac2 goals l :=
  let name_goal x := ltac1:(x |- refine ?[x]) (Ltac1.of_ident x) in
  Control.dispatch (List.map (fun x () => name_goal x) l).

(* This can be used in more places. TODO *)
Ltac hnf_clean def :=
    let t := def in
    let t := eval red in t in 
    let t := eval hnf in t in 
    exact t.



Module HoleNotations.
  #[local] Ltac2 admit_tac does_print := 
    if  (neg does_print) then () else 
    printf "Give me a ~%t~" (goal ());
    let hole_constr := Control.hyp (@hole) in
    refine (fun () => '($hole_constr _)). 
    (* TODO: I wish that this was exact. 
    I also wish that I could check the type of hole,
    and make sure that it is forall T, T
    *)

  Notation "??" := ltac2:(admit_tac false) (only parsing).
  Notation "??!" := ltac2:(admit_tac true) (only parsing).

  Fail Check ?? + 5.

  Section usage. Hypothesis hole : forall T, T.

    Check ??.

    Let x := ?? + ??.
    Let y := 5 + ??!.
    Check ??! + 5.

    Compute  (match ??! with 
      | true => ??!
      | false => ??
      end).

  End usage.


  Section test. Variable hole : bool.
    Fail Check ??.
  End test.
End HoleNotations.
