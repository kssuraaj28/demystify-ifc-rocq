From Stdlib Require Import (*Arith*) List String ssreflect ssrbool.
Require Import Util Tacs VarVal Store MetaSyntax.
Require CleanSyntax. (* Should this be here? *)

Module Prms.
  (* The type of messages that the adversary leaks.
  I made this a operational typeclass for some reason... *)
  Class AdvLeakPrm := LeakVals : Type. 

  (* We also need to specify what variables the adversary has access to*)
  Class AdvLvlPrm  `{!VarPrm} := {
    is_untrusted : pred Vars ; 
    is_public : pred Vars
  }.

  Section opp.
    Context `{!VarPrm, !AdvLvlPrm}.
    Definition is_secret v := ~~ is_public v.
    Definition is_trusted v := ~~ is_untrusted v.
  End opp.

  (* Should we let the adversary leak a value initially? *)
  Class AdvDevicePrm  `{!VarPrm, !ValPrm, !AdvLvlPrm} := { 
      AdvMem : Type; 
      adv_mem_init : StoreView is_public -> AdvMem;
      adv_maul_init : {v: Vars | is_untrusted v} -> Vals -> Vals 
      (* 
        I guess that there are other things that can be done:
        - StoreView is_untrusted -> StoreView is_untrusted
        Here, you can maul in a slightly weirder way
      *)
    }.
End Prms.
Import Prms.

Section atksyntax.
  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm, !AdvDevicePrm}.

  (* When you write to an adversary readable variable, the adversary can exfiltrate the value *)
  Definition AdvExfiltrator := Vals -> AdvMem -> (LeakVals * AdvMem).

  (* When you read from  an adversary writable variable, the adversary can maul *)
  Definition AdvCorruptor := Vals -> AdvMem -> Vals. 

  (* 
     Maybe think about other ways? I use computation here.. 
     Maybe the equations plugin helps..
  *)
  Notation SrcAttachment v :=
    (if (is_untrusted v) is true then AdvCorruptor else unit).

  Notation DstAttachment v :=
    (if (is_public v) is true then AdvExfiltrator else unit).

  (* 
    In order to construct these vars, you may have to do dependent pattern matching. 
    I don't know how much it will bite us.
    The other way to do it is +
  *)
  Definition VarSrc := {v : Vars & SrcAttachment v}.  
  Definition VarDst := {v : Vars & DstAttachment v}.  

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := VarSrc; DstVarMeta := VarDst|}) : typeclass_instances.

  Definition ValExp := ValExpMeta.
  Definition BoolExp := BoolExpMeta.
  Definition Cmd := CmdMeta.
  Definition Prog := ProgMeta.
End atksyntax.

Section syntax_erase.
  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm, !AdvDevicePrm}.

  Notation AtkSrc := AtkSyntax.VarSrc.
  Notation AtkDst := AtkSyntax.VarDst.

  Notation CleanSrc := CleanSyntax.VarSrc.
  Notation CleanDst := CleanSyntax.VarDst.

  Import SigTNotations.
  Definition erase_var_src (vs : AtkSrc) : CleanSrc := 
    let: (v; _) := vs in v.
  Definition erase_var_dst (vd : AtkDst) : CleanDst := 
    let: (v; _) := vd in v.

  Notation L1 := 
    {|SrcVarMeta := AtkSrc; DstVarMeta := AtkDst |}.
  Check ltac:(exact L1).

  Notation L2 := 
    {|SrcVarMeta := CleanSrc; DstVarMeta := CleanDst |}.
  Check ltac:(exact L2).

  Hint Extern 0 SynTransPrm => (exact {|
    Lang1 := L1;
    Lang2 := L2;
    src_trans := erase_var_src;
    dst_trans := erase_var_dst;
  |}) : typeclass_instances.
  Check ltac:(exact(_ : SynTransPrm)).

  Definition erase_val_exp := Eval red in val_exp_trans.
  Definition erase_bool_exp := Eval red in bool_exp_trans.
  Definition erase_cmd := Eval red in cmd_trans.
  Definition erase_prog := Eval red in prog_trans.
End syntax_erase.
