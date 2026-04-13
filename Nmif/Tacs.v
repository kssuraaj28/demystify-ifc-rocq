From Ltac2 Require Import Ltac2 Bool Control Printf. (* TODO: Hygiene *)
Require Import ssreflect.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.


(* TODO: This file structure is ugly *)

(* TODO: Notation for this *)
Ltac2 goals l :=
  let name_goal x := ltac1:(x |- refine ?[x]) (Ltac1.of_ident x) in
  Control.dispatch (List.map (fun x () => name_goal x) l).



(*  
    If t is a tactic that takes in a hypothesis, 
    this tactic will apply the top hypothesis on it
    The top hypothesis might go away
*)
(* TODO: Can I make this part of ssr => *)
(* TODO: I use ⟨  ⟩ too much *)
Tactic Notation "⟨" tactic(t)  "⟩" := let f := fresh in (move=> f); t f. (* Tactic Notation vs Ltac Notation *)

(* This is a little hacky because you don't you are doing trial and error.. 
   Maybe better to specialize *)
Tactic Notation "⟨⟨" tactic(t) "⟩⟩" :=
    match goal with
    H : _ |- _ => t H
    end.
Section test.
  Ltac t H := idtac H.
  Goal False -> False.  Proof.  ⟨ t ⟩. Abort.
  Goal False -> False.  Proof.  move=> *. ⟨⟨ t ⟩⟩. Abort.
End test.

Ltac evar_spec H :=  
    move: H;
    let t := open_constr:(_) in 
    let f := fresh in 
    pose f := t=> /(_ f); subst f.
(* TODO: Test for these also *)


Ltac2 dst_hyp_type (ty : constr) :=
  let hyps := List.filter (fun h => let (_, _, t) := h in Constr.equal t ty) (Control.hyps ()) in
  match hyps with
  | [(h, _, _)] => let hcnstr := hyp h in destruct $hcnstr
  | [] => Control.zero (Tactic_failure (Some (fprintf "No hypothesis of type %t" ty)))
  | _ => Control.zero (Tactic_failure (Some (fprintf "Multiple hypotheses of type %t" ty)))
  end.

Ltac dst_hyp_type ty :=
  let f := ltac2:(ty |- dst_hyp_type (Option.get (Ltac1.to_constr ty))) in
  f ty.

Goal nat -> False. Proof. move=> *.  dst_hyp_type nat. Abort.
Goal nat -> nat -> False. Proof. move=> *.  Fail dst_hyp_type nat. Abort.


Module GallinaUtil.
  Import Ltac2 Bool Control Printf.
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

  (* TODO: Inspection is a little stupd.. *)
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

