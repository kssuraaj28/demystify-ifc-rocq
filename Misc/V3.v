From Stdlib Require Import List ssreflect.
(* ssreflect for gallina extensions *)
From QuickChick Require Import Decidability. 
(* QuickCheck decidable equality classes are so good *)

Import ListNotations.
(* I'm just going to bundle stuff for now. The context is getting quite large otherwise.
*)
Class VarPrm := {Vars : Type ; vars_deceq :: Dec_Eq Vars}. 
Class ValPrm := {Vals : Type}.

(* An adversary level is given by specifying which variables can be controlled  *)
Class AdvLvlParam `{VarPrm} := { is_untrusted : Vars -> bool ; is_public : Vars -> bool }.


(* When you instantiate an adversary, you also give it memory *)
Class AdvMemParam := {AdvMem : Type}. (* Maybe specify initial value also.. *)

Class AdvLeakParam := {LeakVals : Type}.  (* The type of messages that the adversary leaks *)

Section advsnips.
  Context `{ValPrm} `{AdvMemParam} `{AdvLeakParam}. (* I wonder whether some sus thing can happen when I have duplication.. TODO *)

  (* I think that this eventually has to have memory updates as well *)
  Definition AdvExfiltrator := Vals -> AdvMem -> LeakVals. 
  Definition AdvCorruptor := Vals -> AdvMem -> Vals. 
End advsnips.

Section syntax.
  Context `{VarPrm} `{ValPrm}.

  (* 
    v1 ∘ v2. Some binary operation 
    If either variable is controlled by the adversary, then that strat will be applied.
    Another thing we could to is to have an alternative where the adversary gets to supply an alternative function.
    Here, when either variable is untrusted, the adversary function gets activated
  *)
  Inductive ValExp :=
    mk_vl_exp (v1 v2: Vars) (v1_adv v2_adv : AdvCorruptor) (comp : Vals -> Vals -> Vals).

  Inductive BoolExp := 
    mk_bl_exp (v: Vars) (v_adv : AdvCorruptor) (test : Vals -> bool).

  Inductive AssignDest := 
    mk_ass_dest (v: Vars) (v_adv : AdvExfiltrator).


  Section cmd.
    Notation Prog' Cmd := (list Cmd).
    Unset Elimination Schemes. 
    Inductive Cmd :=
      | assign (d : AssignDest) (exp : ValExp)
      | cond (cond_var: BoolExp) (b1 b2: Prog' Cmd)
      | while (cond_var: BoolExp) (body: Prog' Cmd). 
    Set Elimination Schemes.
    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Variable P : Cmd -> Prop.
    Generalizable All Variables.

    Hypothesis assign : `(P (assign d exp)).

    Hypothesis cond : `(Forall P b1 ->
                        Forall P b2 ->
                        P (cond cond_var b1 b2)).

    Hypothesis while : `(Forall P body ->
                          P (while cond_var body)).

    Ltac done ::= auto.
    Ltac t appl :=  intros; apply appl; match goal with |- Forall P ?b => induction b end.

    (* I don't know whether I'm using the right ssreflect thing *)
    Fixpoint Cmd_ind : forall c, P c. Proof.
      case => c; by [t assign || t cond || t while].
    Qed.
  End cmd_ind.
  (* It is a little weird that a very syntactic  *_ind approach is used. *)
  Goal forall c : Cmd, c = c. elim => c; reflexivity. Qed. 
End syntax.

Section store.
  Context `{VarPrm} `{ValPrm}.

  Definition Store := Vars -> Vals.

  (* This seems like it should be in a module *)
  Definition get_store (s : Store) (v : Vars) : Vals := s v.

  Definition update_store (s : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if (v = v')? is true then vl else s v'.
End store.


Section cfg.
  Context `{VarPrm} `{ValPrm}.

  (* A 'state' is the program state + the pending program / continuation  *)
  Record Cfg := mk_cfg {store : Store; cont : Prog}. 
End cfg.

Section semantics.
  Context `{VarPrm} `{ValPrm}.

  Definition exp_eval (e : ValExp) (store : Store) : Vals :=
    let: mk_vl_exp v1 v2 v1_adv v2_adv comp := e in
    let: v1val := get_store store v1 in
    let: v2val := get_store store v2 in
    comp v1val v2val.

  Definition assign_eval (e : ValExp) (store : Store) : Vals :=
    let: mk_vl_exp v1 v2 v1_adv v2_adv comp := e in
    let: v1val := get_store store v1 in
    let: v2val := get_store store v2 in
    comp v1val v2val.

  Definition step (cfg : Cfg) : Cfg * option LeakVal :=
    let: mk_cfg store prog := cfg in
    if prog isn't (cmd :: prog') then (cfg, None) else  (* prog is skip *)

    match cmd with 
    | assign adv var exp =>  
        let: val := (exp_eval exp store) in
        let: leak := adv val in
        let: cont := prog' in
        let: cfg := mk_cfg (update_store store var val) cont in
        (cfg, Some(leak))

    | cond v b1 b2 =>  (* I really need to think of the right way to treat equality.. *)
        let: branch := if (Nat.eqb v 0) is true then b1 else b2 in
        let: cont := (branch ++ prog') in
        let: cfg := mk_cfg store cont in
        (cfg, None)

    | while v while_bdy  =>  
       let: cont := if (Nat.eqb v 0) is true then prog' else (while_bdy ++ prog) in
       let: cfg := mk_cfg store cont in
       (cfg, None)
    end.


(* 
  My dream is the following:
  - Typeclasses
  - Assign store eval

  Attacker memory.
  Labels.
  Should I think about what the right way to define a trace is?
  Technically, we need to be defining system equivalence.
*)
End semantics.
