(* TODO: too many imports *)
From Ltac2 Require Import Ltac2 Bool Control Printf.
From Corelib Require Import ssreflect.

(* TODO: Notation for this *)
Ltac2 goals l :=
  let name_goal x := ltac1:(x |- refine ?[x]) (Ltac1.of_ident x) in
  Control.dispatch (List.map (fun x () => name_goal x) l).

(*
  This can be used in more places. 
  TODO.  This should also be in Ltac2
*)
Ltac hnf_clean def :=
    let t := def in
    let t := eval red in t in 
    let t := eval hnf in t in 
    exact t.

(* ssreflect helpers. 
Goal discipline is annoying when you are exploring
*)
Notation ">" := (ltac:(intros *;
                      idtac "Warning: Remove this in the final proof"))
                (at level 0, only parsing) : ssripat_scope.

Notation "*" := (ltac:(intros;
                      idtac "Warning: Remove this in the final proof"))
                (at level 0, only parsing) : ssripat_scope.

Notation "?" := (ltac:(intros;
                      idtac "Warning: Remove this in the final proof"))
                (at level 0, only parsing) : ssripat_scope.

Goal forall x, x + 1 = x + 1. Proof Mode "Classic".  by move=> /> //. Abort.

Module GallinaUtil.
  (* Holes *)
  #[local] Ltac2 admit_tac () := 
    let hole_constr := Control.hyp @hole in
    refine (fun () => '($hole_constr _)).

    (* TODO: I wish that this was exact. 
    I also wish that I could check the type of hole,
    and make sure that it is forall T, T

    Maybe then have marked hole, etc.
    You could have a way to look for marked holes, etc.

    You could also attach arbitrary ltac2 things.
    Maybe the right place for this is to know the types of certain things..
    Can we get gallina notations for this?
    Notation x _ := x.
    *)
  Notation "??" := ltac2:(admit_tac ()) (only parsing).

  Section usage. 
    Fail Check ?? + 5.
    Hypothesis hole : forall T, T.
    Check ??.
    Let x := ?? + ??. Print x.
    Let y := 5 + ??. Print x.
    Check ?? + 5.

    Compute  (match ?? with 
      | true => ??
      | false => ??
      end).

  End usage.

  Section test. Variable hole : bool.   Fail Check ??.  End test.


  (* Inspection  *)
  #[local] Ltac2 inspect value tactic :=
    tactic value (Constr.type value);
    exact value. (* Why does $value also work? *)

  Ltac2 Notation "⟦" v(constr) t(tactic) " ⟧"  := inspect v t.

  Check ltac2:( ⟦ 5 (fun v t => printf "%t %t" v t)  ⟧).

  Notation "⟦ v ⟧"  := 
    ltac2:(
    inspect (Constr.pretype v) (fun v t => printf "%t : %t" v t )) (only parsing).

  Check ⟦ 4 ⟧.
  (* Having arbitrary ltac2 functions in gallina does not seem very easy.. *)

End GallinaUtil.
