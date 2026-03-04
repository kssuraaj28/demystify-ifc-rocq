From Stdlib Require List ssreflect.
Import List ssreflect.

Require VarVal Store.
Import VarVal Store.

Section syntax.
  Context `{!VarPrm, !ValPrm}.

  Inductive ValExp :=
    mk_vl_exp (v1 v2: Vars) (comp : Vals -> Vals -> Vals).

  Inductive BoolExp :=
    mk_bl_exp (v: Vars) (test : Vals -> bool).


  Section cmd.
    Notation Prog' Cmd := (list Cmd).

    Unset Elimination Schemes. 
    Inductive Cmd :=
      | assign (d: Vars) (exp : ValExp)
      | cond (tst: BoolExp) (b1 b2: Prog' Cmd)
      | while (tst: BoolExp) (b: Prog' Cmd). 
    Set Elimination Schemes.

    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Generalizable All Variables.
    Variable P : Cmd -> Prop.

    Hypothesis hyp_assign : 
      `(P (assign d exp)).

    Hypothesis hyp_cond : 
      `(Forall P b1 ->
        Forall P b2 ->
        P (cond tst b1 b2)).

    Hypothesis hyp_while : 
      `(Forall P b ->
        P (while tst b)).

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

  (* What is 'state'? *)
  (* TODO: There might need to exist a pending insruction stack or something *)
  Inductive Cfg := 
    mk_cfg (store : Store) (cont : Prog).
End cfg.

Inductive ProgCounter :=
  | top 
      (pending_ins: nat)

  | condxx 
      (pending_ins: nat) 
      (choice_made: bool) 
      (sub_pc : ProgCounter)

  | while_okay 
      (pending_ins: nat) 
      (sub_pc : ProgCounter)
.

Fixpoint if_step (p : ProgCounter) (cond: bool) (body: nat) : ProgCounter :=
  match p with
  | top n => 
      condxx n cond (top body)
  | condxx n b sub_pc =>
      condxx n b (if_step sub_pc cond body)
  | while_okay n sub_pc =>
      while_okay n (if_step sub_pc cond body)
  end.

Fixpoint while_step (p : ProgCounter) (while_bdy: nat) : ProgCounter :=
  match p with
  | top n => 
      while_okay n (top while_bdy) 
  | condxx n b sub_pc =>
      condxx n b (while_step sub_pc while_bdy) 
  | while_okay n sub_pc =>
      while_okay n (while_step sub_pc while_bdy)
  end.

Fixpoint pop_step (p : ProgCounter) : option ProgCounter :=
  match p with
  | top n => 
      if n isn't S n' then None else 
      Some (top n')
  | condxx n b sub_pc => 
      if (pop_step sub_pc) is Some p then Some (condxx n b p) else 
      if n isn't S n' then None else
      Some (top n')
  | while_okay n sub_pc =>
      if (pop_step sub_pc) is Some p then Some (while_okay n p) else 
      if n isn't S n' then None else
      Some (top n') (* What is happening? *)
  end.

Fixpoint pending_ins_cnt (p : ProgCounter) : nat :=
  match p with 
  | top n => n
  | condxx n _ sub_pc  => n + pending_ins_cnt sub_pc
  | whilexx n _ sub_pc  => n + pending_ins_cnt sub_pc
  end.



(*  The idea is that at runtime, 
    your pending instructions will be 
    the length of the program that you put.
    The one thing I don't like is that you might need to
    It may be wise to have an invariant.. that relates something,
    so that we don't have to write none..
    Something like number of instructions = 
    sum of pending..

    The challenge here is the 

    what should this step to?
    top 0
    if 0
    if 0

    -->

    None?




    
 *)

Section semantics.
  Context `{!VarPrm, !ValPrm}.
  Definition step  (c : Cfg) : Cfg. Proof.
    refine(
    let: mk_cfg store p := c in 
    if p isn't cmd :: p' then c else
    match cmd with 
    | assign d exp => 
        mk_cfg _ p'
    | cond tst b1 b2 => mk_cfg _ _
    | while tst b => mk_cfg _ _
    end


    ).
    Show Proof.
    destruct cmd.
    Show Proof.


End semantics.
