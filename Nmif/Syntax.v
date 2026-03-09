From Stdlib Require List ssreflect.
Import List ssreflect. 
(* I wonder whether there is something equilvalent for Forall in sssreflect *)

From mathcomp Require seq.
Import seq.

Require VarVal Store.
Import VarVal Store.

Section syntax.
  Context `{!VarPrm, !ValPrm}.

  Section cmd.
    Notation Prog' Cmd := (list Cmd) (only parsing).

    Unset Elimination Schemes. 
    Inductive Cmd :=
      | assign (comp : Store -> Store)
      | cond (tst: Store -> bool) (b1 b2: Prog' Cmd)
      | while (tst: Store -> bool) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

    Hypothesis hyp_assign : 
      `(P (assign comp)).

    Hypothesis hyp_cond : 
      `(Forall P b1 ->
        Forall P b2 ->
        P (cond tst b1 b2)).

    Hypothesis hyp_while : 
      `(Forall P b ->
        P (while tst b)).

    (* I wonder whether I could have a better version from ssreflect? *)
    Ltac t hyp :=
      apply: hyp; 
      match goal with |- Forall _ ?l => elim: l end;
      auto.

    Fixpoint Cmd_ind : forall c, P c. Proof.
      case=> >; 
        by [t hyp_assign | t hyp_cond | t hyp_while].
    Qed.
  End cmd_ind.
End syntax.


Section cfg.
  Context `{!VarPrm, !ValPrm}.

  Inductive ContinuationStep :=
    | atk_cmd (c : Cmd)
    | clean_cmd (c : Cmd)
    | pure_atk.

  (* TODO: Make this seq? *)
  Definition Continuation := seq ContinuationStep.
  Compute (nseq 5 true).

  Fixpoint prog_zip (p: Prog) (atk_steps: nat) : Continuation :=
    match p, atk_steps with
    | cmd :: p', S atk_steps' =>
          (atk_cmd cmd) :: (prog_zip p' atk_steps')

    | [::], _ => 
        nseq atk_steps pure_atk

    | _ , 0 =>  
        [seq clean_cmd c | c <- p] 
    end.


  Lemma prog_zip_noprg: forall n, prog_zip [::] n = nseq n pure_atk. Proof.
    by [].
  Qed.

  Lemma prog_zip_noatk: forall p, prog_zip p 0 = [seq clean_cmd c | c <-  p]. Proof.
    Fail by [].
    by case.
  Qed.

  Section Check.
    Variables c1 c2 c3 : Cmd.
    Compute prog_zip [:: c1 ; c2 ; c3] 5.
    Compute prog_zip [:: c1 ; c2 ; c3] 0.
    Compute prog_zip [:: c1 ; c2 ; c3] 1.
  End Check.

End cfg.

Class AtkStatesPrm := AtkStates : Type.

(* 
  TODO
  You need to eventually corrupt store,
  Learn from store etc 
*)
Class AtkStateMachinePrm `{AtkStatesPrm} := {
    atk_step : AtkStates -> (AtkStates * nat)  (* Subactivations *)
  }.


Section step.
  Context `{!VarPrm, !ValPrm, !AtkStatesPrm, !AtkStateMachinePrm}.

  Notation ProgContinutation := Prog (only parsing).
  Notation Ret := (Store * ProgContinutation)%type. (* Prog continutation *)

  Definition step (c : Cmd) (s : Store) : Ret :=
    match c with
    | assign comp => 
        (comp s, [::])
    | cond tst b1 b2 => 
        (s, if (tst s) is true then 
              b1
            else 
              b2)
    | while tst b => 
        (s, if (tst s) is true then 
              (b ++ [:: while tst b]) 
            else 
              [::])
    end.


  (* It seems like this should work.. *)
  Definition step_w_atk (c : ContinuationStep) (s : Store) (atkst : AtkStates) : (Store * AtkStates * Continuation) := 
    match c with 
    | clean_cmd c => 
        let: (s', cont) := step c s in
        (s', atkst , prog_zip cont 0)
    | atk_cmd c => 
        let: (s', cont) := step c s in
        let: (atkst', atkcont) := atk_step atkst in
        (s', atkst', prog_zip cont atkcont)
    | pure_atk => 
        let: (atkst', atkcont) := atk_step atkst in
        (s, atkst', prog_zip [::] atkcont)
    end.


  (* Maybe make something Cfg *)
  (* What is 'state'? *)
  Definition cfg_step 
                (c: Continuation) (s: Store) (ast: AtkStates) : 
                (Continuation * Store * AtkStates) := 
                if c isn't cmd :: rest then ([::], s, ast) else
                let: (s', ast', cont') := step_w_atk cmd s ast in
                (cont' ++ rest ,s', ast').

End step.

