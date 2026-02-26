From Stdlib Require Import (*Arith*) List String ssreflect ssrbool.
Require Import Util Tacs VarVal.

Class SrcDstVarPrm := {SrcVarMeta : Type ; DstVarMeta : Type}.

(* TODO: There needs to be a good eval thing *)
Section meta_syntax.
  Context `{!VarPrm, !ValPrm}.

  Context `{!SrcDstVarPrm}.

  (* v1 ∘ v2. Some binary operation *)
  Inductive ValExpMeta := mk_vl_exp (v1 v2: SrcVarMeta) (comp : Vals -> Vals -> Vals).
  Inductive BoolExpMeta :=  mk_bl_exp (v: SrcVarMeta) (test : Vals -> bool).

  Section cmd.
    Notation ProgMeta' CmdMeta := (list CmdMeta).

    Unset Elimination Schemes. Inductive CmdMeta :=
      | assign (d : DstVarMeta) (exp : ValExpMeta)
      | cond (cond_var: BoolExpMeta) (b1 b2: ProgMeta' CmdMeta)
      | while (cond_var: BoolExpMeta) (body: ProgMeta' CmdMeta).  Set Elimination Schemes.

    Definition ProgMeta := ProgMeta' CmdMeta.
  End cmd.

  Section cmd_ind.
    Variable P : CmdMeta -> Prop.
    Generalizable All Variables.

    Hypothesis assign : `(P (assign d exp)).

    Hypothesis cond : `(Forall P b1 ->
                        Forall P b2 ->
                        P (cond cond_var b1 b2)).

    Hypothesis while : `(Forall P body ->
                          P (while cond_var body)).

    Ltac t appl :=  intros; apply appl; match goal with |- Forall P ?b => elim: b; auto end.

    (* I don't know whether I'm using the right ssreflect thing *)
    Fixpoint CmdMeta_ind : forall c, P c. Proof.
      case => c; by [t assign | t cond | t while].
    Qed.

  End cmd_ind.

  (* It is a little weird that a very syntactic  *_ind approach is used. *)
  Goal forall c : CmdMeta, c = c. Proof. elim; reflexivity. Qed. 
End meta_syntax.

Class SrcDstPredPrm `{!SrcDstVarPrm}
  := {SrcPred : (SrcVarMeta -> Prop); DstPred : (DstVarMeta -> Prop)}.

Section syntax_pred.
  Context `{!VarPrm, !ValPrm}.

  Context `{!SrcDstVarPrm,!SrcDstPredPrm}.

  Definition ValExpPred (exp: ValExpMeta): Prop := 
    let: mk_vl_exp vs1 vs2 _ := exp in
    SrcPred vs1 /\ SrcPred vs2.


  Definition BoolExpPred (exp: BoolExpMeta):  Prop :=
    let: mk_bl_exp vs test := exp in
    SrcPred vs.

  Notation ProgPred' CmdPred prog :=  
    (fold_left (fun rest cmd => rest /\ CmdPred cmd) prog True).

  Fixpoint CmdPred (cmd: CmdMeta) : Prop := 
    match cmd with
    | assign vd exp => DstPred vd /\ ValExpPred exp
    | cond exp b1 b2 => 
        BoolExpPred exp /\ 
        ProgPred' CmdPred b1 /\
        ProgPred' CmdPred b2
    | while exp while_bdy  => 
        BoolExpPred exp /\ 
        ProgPred' CmdPred while_bdy
    end.

  Definition ProgPred prog := ProgPred' CmdPred prog.
End syntax_pred.

(* Bundling is a little bit sad. *)
Class SynTransPrm := {
  Lang1: SrcDstVarPrm; 
  Lang2: SrcDstVarPrm;
  src_trans: @SrcVarMeta Lang1 -> @SrcVarMeta Lang2;
  dst_trans: @DstVarMeta Lang1 -> @DstVarMeta Lang2
}.

Section syntax_transform.
  Context `{!VarPrm, !ValPrm}.
  Context `{!SynTransPrm}.


  (* This should be refactored out. TODO *)
  Ltac clean cons := 
    let t := cons in
    let t := eval hnf in t in
    let t := eval unfold Lang1, Lang2, src_trans, dst_trans in t in
    let t := eval hnf in t in
    exact t.

  (* Don't double colon!! *)
  Fail Check ltac:(exact(_ : SrcDstVarPrm)). 

  Existing Instance Lang1. Check ltac:(exact(_ : SrcDstVarPrm)). 
    Let ValExp1 := ltac:(clean ValExpMeta).
    Let BoolExp1 := ltac:(clean BoolExpMeta).
    Let Cmd1 := ltac:(clean CmdMeta).
    Let Prog1 := ltac:(clean ProgMeta).
  Remove Hints Lang1: typeclass_instances. Fail Check ltac:(exact(_ : SrcDstVarPrm)). 


  Existing Instance Lang2. Check ltac:(exact(_ : SrcDstVarPrm)). 
    Let ValExp2 := ltac:(clean ValExpMeta).
    Let BoolExp2 := ltac:(clean BoolExpMeta).
    Let Cmd2 := ltac:(clean CmdMeta).
    Let Prog2 := ltac:(clean ProgMeta).
  Remove Hints Lang2: typeclass_instances. Fail Check ltac:(exact(_ : SrcDstVarPrm)). 

  (* I think that this can be abstracted out? *)
  Ltac unfold_clean cons :=
    let t := cons in 
    let t := eval hnf in t in
    let t := eval unfold
      ValExp1,BoolExp1,Cmd1,Prog1,
      ValExp2,BoolExp2,Cmd2,Prog2,
      Lang1, Lang2, src_trans, dst_trans
      in t in
    let t := eval hnf in t in
    exact t.

  Definition val_exp_trans (exp : ltac:(unfold_clean ValExp1)) : ltac:(unfold_clean ValExp2) :=
    ltac:(unfold_clean( 
    let: (mk_vl_exp v1 v2 comp) := exp in 
    mk_vl_exp (src_trans v1) (src_trans v2) comp
    )).

  Definition bool_exp_trans (exp : ltac:(unfold_clean BoolExp1)) : ltac:(unfold_clean BoolExp2) :=
    ltac:(unfold_clean( 
    let: (mk_bl_exp v test) := exp in 
    mk_bl_exp (src_trans v) test
    )).

  (* If map is opaque, I think that this would fail. *)
  (* The termination checker cannot handle mutual recursion. Weird.*)
  Notation prog_trans' p cmd_trans  := (map cmd_trans p).

  Fixpoint cmd_trans (a_cmd : ltac:(unfold_clean Cmd1)) : ltac:(unfold_clean Cmd2) :=
    ltac:(unfold_clean(
    match a_cmd with
    | assign v exp => assign (dst_trans v) (val_exp_trans exp)
    | cond test b1 b2 =>  cond (bool_exp_trans test) (prog_trans' b1 cmd_trans ) (prog_trans' b1 cmd_trans)
    | while test p => while (bool_exp_trans test) (prog_trans' p cmd_trans)
    end)).
  Definition prog_trans p := ltac:(unfold_clean (prog_trans' p cmd_trans)).
End syntax_transform.

