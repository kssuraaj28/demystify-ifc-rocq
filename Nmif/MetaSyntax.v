From Stdlib Require Import (*Arith*) ssreflect ssrbool.
Require Import Util Tacs VarVal.

Class SrcDstVarPrm := {SrcVarMeta : Type ; DstVarMeta : Type}.

(* TODO: There needs to be a good eval thing *)
Section meta_syntax.
  Context `{!VarPrm, !ValPrm}.

  Context `{!SrcDstVarPrm}.

  (* v1 ∘ v2. Some binary operation *)
  Inductive ValExpMeta := mk_vl_exp (v1 v2: SrcVarMeta) (comp : Vals -> Vals -> Vals).
  Inductive BoolExpMeta :=  mk_bl_exp (v: SrcVarMeta) (test : Vals -> bool).

  (* My nested ind exp :( *)
  Inductive CmdMeta :=
    | skip
    | assign (d : DstVarMeta) (exp : ValExpMeta)
    | seq (c1 c2 : CmdMeta)
    | cond (cond_var: BoolExpMeta) (b1 b2: CmdMeta)
    | while (cond_var: BoolExpMeta) (body: CmdMeta). 

End meta_syntax.

Class SyntaxPropPredPrm `{!SrcDstVarPrm} := 
  {SrcPred : (SrcVarMeta -> Prop); DstPred : (DstVarMeta -> Prop)}.

Section syntax_pred.
  Context `{!VarPrm, !ValPrm}.

  Context `{!SrcDstVarPrm,!SyntaxPropPredPrm}.

  Definition ValExpPred (exp: ValExpMeta): Prop := 
    let: mk_vl_exp vs1 vs2 _ := exp in
    SrcPred vs1 /\ SrcPred vs2.


  Definition BoolExpPred (exp: BoolExpMeta):  Prop :=
    let: mk_bl_exp vs test := exp in
    SrcPred vs.

  Fixpoint CmdPred (cmd: CmdMeta) : Prop := 
    match cmd with
    | skip => True
    | assign vd exp => DstPred vd /\ ValExpPred exp
    | seq c1 c2 => CmdPred c1 /\ CmdPred c2
    | cond exp c1 c2 => 
        BoolExpPred exp /\ 
        CmdPred c1 /\
        CmdPred c2
    | while exp while_bdy  => 
        BoolExpPred exp /\ 
        CmdPred while_bdy
    end.
End syntax_pred.

Class SyntaxBoolPredPrm `{!SrcDstVarPrm} := 
  {src_pred : (pred SrcVarMeta); dst_pred : pred DstVarMeta}.

Section syntax_pred.
  Context `{!VarPrm, !ValPrm}.

  Context `{!SrcDstVarPrm,!SyntaxBoolPredPrm}.

  Definition val_exp_pred: pred ValExpMeta :=
    fun exp =>
      let: mk_vl_exp vs1 vs2 _ := exp in
      src_pred vs1 && src_pred vs2.

  Definition bool_exp_pred : pred BoolExpMeta :=
    fun exp =>
      let: mk_bl_exp vs test := exp in
      src_pred vs.

  Fixpoint cmd_pred : pred CmdMeta :=
    fun cmd =>
      match cmd with
      | skip => true
      | assign vd exp => dst_pred vd && val_exp_pred exp
      | seq c1 c2 => cmd_pred c1 && cmd_pred c2
      | cond exp c1 c2 => 
          bool_exp_pred exp &&
          cmd_pred c1 &&
          cmd_pred c2
      | while exp while_bdy  => 
          bool_exp_pred exp &&
          cmd_pred while_bdy
      end.
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
  Remove Hints Lang1: typeclass_instances. Fail Check ltac:(exact(_ : SrcDstVarPrm)). 


  Existing Instance Lang2. Check ltac:(exact(_ : SrcDstVarPrm)). 
    Let ValExp2 := ltac:(clean ValExpMeta).
    Let BoolExp2 := ltac:(clean BoolExpMeta).
    Let Cmd2 := ltac:(clean CmdMeta).
  Remove Hints Lang2: typeclass_instances. Fail Check ltac:(exact(_ : SrcDstVarPrm)). 

  (* I think that this can be abstracted out? 
     This should be an Ltac2 thing
  *)
  Ltac unfold_clean cons :=
    let t := cons in 
    let t := eval hnf in t in
    let t := eval unfold
      ValExp1,BoolExp1,Cmd1,
      ValExp2,BoolExp2,Cmd2,
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

  Fixpoint cmd_trans (a_cmd : ltac:(unfold_clean Cmd1)) : ltac:(unfold_clean Cmd2) :=
    ltac:(unfold_clean(
    match a_cmd with
    | skip => skip
    | assign v exp => assign (dst_trans v) (val_exp_trans exp)
    | seq c1 c2 => seq (cmd_trans c1) (cmd_trans c2)
    | cond test b1 b2 =>  cond (bool_exp_trans test) (cmd_trans b1) (cmd_trans b1)
    | while test p => while (bool_exp_trans test) (cmd_trans p)
    end)).
End syntax_transform.
