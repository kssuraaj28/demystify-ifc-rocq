From Stdlib Require Import List ssreflect.

Import ListNotations.
(* Making this into param fails. Why? TODO *)
(* 
Class VarPrm := {Vars : Type}.
 *)
Definition Vars := nat.
Definition Vals := nat.
(* 
Class ValPrm := {Vals : Type}.
 *)


Section syntax.
  (*   Context `{VarPrm} `{ValPrm}. *)
  (* v1 ∘ v2. Some binary operation *)

  Record Expression := mk_exp {v1: Vars ; v2: Vars; comp : Vals -> Vals -> Vals}.

  Notation Prog' Cmd := (list Cmd).

  Inductive Cmd :=
    | assign (x: Vars) (e: Expression) : Cmd
    | cond (cond_var: Vars) (b1 b2: Prog' Cmd) : Cmd
    | while (cond_var: Vars) (body: Prog' Cmd) : Cmd.

  Definition Prog := Prog' Cmd.
  (* TODO: I need to define the induction principle *)

End syntax.

Section ind.
  Variable P : Cmd -> Prop.
  Hypothesis assign : (forall (x : Vars) (e : Expression), P (assign x e)).

  Hypothesis cond : (forall (cond_var : Vars) (b1 b2 : list Cmd), 
          Forall P b1 ->
          Forall P b2 ->
          P (cond cond_var b1 b2)).

  Hypothesis while : (forall (cond_var : Vars) (body : list Cmd), 
          Forall P body ->
          P (while cond_var body )).

  (* I wonder how to register this as the default induction principle. *)
  (* I'm not using ssreflect's magic *)
  Fixpoint Cmd_ind' : forall c, P c. Proof.
    destruct c; first auto.

    Ltac t :=  match goal with |- Forall P ?b => induction b; auto end.

    - apply cond; t.
    - apply while; t.
  Qed.
End ind.

Section cfg.
  (* Context `{VarPrm} `{ValPrm}. *)

  Definition Store := Vars -> Vals.

  (* This seems like it should be in a module *)
  Definition get (s : Store) (v : Vars) : Vals := s v.

  Definition update (s : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if Nat.eqb v v' is true then vl else s v'.

  Record Cfg := mk_cfg {store : Store; prog : Prog}. 
End cfg.

Section semantics.
  (*Context `{VarPrm} `{ValPrm}. *)


  Definition exp_eval (e : Expression) (store : Store) : Vals :=
    let: mk_exp v1 v2 comp := e in
    let: v1val := get store v1 in
    let: v2val := get store v2 in
    comp v1val v2val.

  Definition step (cfg : Cfg) : Cfg :=
    let: mk_cfg store prog := cfg in
    if prog isn't (cmd :: prog') then cfg else 

    match cmd with 
    | assign var exp  =>  
        let: val := (exp_eval exp store) in
        mk_cfg (update store var val ) prog'

    | cond v b1 b2 =>  (* I really need to think of the right way to treat equality.. *)
        let: branch := if (Nat.eqb v 0) is true then b1 else b2 in
        mk_cfg store (branch ++ prog')

    | while v while_bdy  =>  
       if (Nat.eqb v 0) is true then
          mk_cfg store prog'
       else
         mk_cfg store (while_bdy ++ prog) (* The original program *)
    end.


End semantics.
