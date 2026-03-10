From Stdlib Require List ssreflect ssrbool.
Import List ListNotations ssreflect ssrbool. 

Require VarVal Store.
Import VarVal Store.

Section syntax.
  Context `{!VarPrm, !ValPrm}.

  Section cmd.
    Notation Prog' Cmd := (list Cmd) (only parsing).

    Unset Elimination Schemes. 
    Inductive Cmd :=
      | skip
      | assign (comp : Store -> Store)
      | cond (tst: Store -> bool) (b1 b2: Prog' Cmd)
      | while (tst: Store -> bool) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

    Hypothesis hyp_skip : 
      `(P (skip)).

    Hypothesis hyp_assign : 
      `(P (assign comp)).

    Hypothesis hyp_cond : 
      `(Forall P b1 ->
        Forall P b2 ->
        P (cond tst b1 b2)).

    Hypothesis hyp_while : 
      `(Forall P b ->
        P (while tst b)).

    (* I wonder whether I could have a better version from ssreflect?
    It does not look like I can..
    *)
    Ltac t hyp :=
      apply: hyp; 
      match goal with |- Forall _ ?l => elim: l end;
      auto.

    Fixpoint Cmd_ind : forall c, P c. Proof.
      case=> >; 
        by [t hyp_skip | t hyp_assign | t hyp_cond | t hyp_while].
    Qed.
  End cmd_ind.
End syntax.




Section clean_step.
  Context `{!VarPrm, !ValPrm}.
  Notation ProgContinutation := Prog (only parsing).

  Definition step (c : Cmd) (s : Store) : (Store * ProgContinutation) :=
    match c with
    | skip =>
        (s, [])
    | assign comp => 
        (comp s, [])
    | cond tst b1 b2 => 
        (s, if (tst s) is true then 
              b1
            else 
              b2)
    | while tst b => 
        (s, if (tst s) is true then 
              (b ++ [while tst b]) 
            else 
              [])
    end.
End clean_step.

Section util.
  Context {A: Type}.
  Fixpoint nlist (a:A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => a :: (nlist a n')
    end.

  (* TODO: Learn ssr rewrite. Also, f_equal? *)
  Lemma nlist_len: 
    forall n (a:A), length (nlist a n) = n. 
  Proof.
    elim; first by [].
    by simpl; auto.
  Qed.

  Lemma nlist_content: 
    forall n (a:A), 
      Forall (fun a' => a' = a) (nlist a n). 
  Proof.
    elim; first by [].
    by simpl; auto.
  Qed.
End util.

Section cont.
  Context `{!VarPrm, !ValPrm}.

  Inductive ContinuationStep :=
    mk_cstep (is_attacked: bool) (cmd : Cmd).

  Definition Continuation := list ContinuationStep.

  Notation pure_atk := (mk_cstep true skip).
  Notation pure_cmd := (mk_cstep false).

  Fixpoint prog_zip (p: Prog) (atk_steps: nat) : Continuation :=
    match p, atk_steps with
    | cmd :: p', S atk_steps' =>
          (mk_cstep true cmd) :: (prog_zip p' atk_steps')

    | [], _ => 
        nlist pure_atk atk_steps

    | _ , 0 =>  
        map pure_cmd p
    end.

  Lemma prog_zip_noprg: forall n, prog_zip [] n = nlist pure_atk n. Proof.
    by [].
  Qed.

  Lemma prog_zip_noatk: forall p, prog_zip p 0 = map pure_cmd p. Proof.
    Fail by [].
    by case.
  Qed.

  Section check.
    Variables c1 c2 c3 : Cmd.
    Compute prog_zip [c1 ; c2 ; c3] 5.
    Compute prog_zip [c1 ; c2 ; c3] 0.
    Compute prog_zip [c1 ; c2 ; c3] 1.
    Compute prog_zip [c1 ; c2 ; c3] 3.
  End check.
End cont.

Class AdvLeakPrm := LeakVals : Type.

Class AdvLvlPrm  `{!VarPrm} := {
  is_untrusted : pred Vars ;
  is_public : pred Vars
}.
Section opp.
  Context `{!VarPrm, !AdvLvlPrm}.
  Definition is_secret v := ~~ is_public v.
  Definition is_trusted v := ~~ is_untrusted v.
End opp.

(* 
  TODO
  You need to eventually corrupt store,
  Learn from store etc 
*)
(* 
  The attacker is sandwiched between the normal code... 
  corrupt ; cmd;  learn ; leak || substeps

  Another thing we could do is something where
  you also get access to pc?  TODO
*)
Record AdvStateMachine `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} := {
    AtkStates : Type;
    corruptor: AtkStates -> (StoreView is_untrusted) -> (StoreView is_untrusted);
    learner : AtkStates -> (StoreView is_public) -> AtkStates;
    leaker : AtkStates -> LeakVals;
    substeps : AtkStates -> nat;
  }.

Section xxx.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Variable (adv : AdvStateMachine).

  (* Making this a class makes this all automatic. TODO *)
  Notation AtkStates := (AtkStates adv).
  Notation corruptor := (corruptor adv).
  Notation learner := (learner adv).
  Notation leaker := (leaker adv).
  Notation substeps := (substeps adv).
            
  (* Make this a snippet *)
  Parameter TODO : forall {T}, T.
  Import Store.Notations.


  (* You could do optional leak or 
     make adversaries fancier..
  *)
  Definition step_w_atk 
      (c : ContinuationStep) (s : Store) (atkst : AtkStates) : 
      (Store * AtkStates * Continuation * option LeakVals) := 

        let: mk_cstep is_atk c := c in 

        (* Part1 of adversary runs *)
        let: s := if is_atk is false then s else
          TODO (* Need to update view *) in

        (* Run your computation *)
        let: (s, pcont) := step c s in

        
        (* 
          Part2 of adversary runs. 
          It is important that atkst is updated first, 
          because substeps and leak may depend on new information
        *)
        let: atkst := if is_atk is false then atkst else learner atkst ⟨s⟩ in
        let: substeps := if is_atk is false then 0 else substeps atkst in
        let: optleak := if is_atk is false then None else Some (leaker atkst) in
        (s, atkst, prog_zip pcont substeps, optleak).


  (* Maybe make something Cfg *)
  (* What is 'state'? *)
  (* This is disgusting. TODO *)
  Definition cfg_step 
                (c: Continuation) (s: Store) (ast: AtkStates) : 
                (Continuation * Store * AtkStates) := 
                if c isn't cmd :: rest then ([::], s, ast) else
                let: (s', ast', cont') := step_w_atk cmd s ast in
                (cont' ++ rest ,s', ast').
End step.
