From Stdlib Require Import (*Arith*) List String ssreflect ssrbool.
Require Import Util Tacs VarVal MetaSyntax Store.


Section nmif.
  Import MetaSyntax AtkSyntax.Prms.
  Import AtkSyntax (AdvCorruptor, AdvExfiltrator).
  Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

  Definition NmifCorruptor `{!AdvDevicePrm} (corr : AdvCorruptor) : Prop := 
    forall mem v1 v2, corr v1 mem = corr v2 mem.

  (* TODO: What happens when you make the variable thing have explicit param? 
  I think that there should be no change? *)
  Definition NmifSecurity := atk_sim_sec (fun _ => NmifCorruptor) (fun _ _ => True).
End nmif.

Section ni.
  Import MetaSyntax AtkSyntax.Prms.
  Import AtkSyntax (AdvCorruptor, AdvExfiltrator).
  Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

  (* Noop *)
  Definition NICorruptor `{!AdvDevicePrm} (corr : AdvCorruptor) : Prop := 
    forall mem v, corr v mem = v.

  Definition NIExfiltrator `{!AdvDevicePrm} (exf : AdvExfiltrator) : Prop :=
    forall v1 v2 amem,
      exf v1 amem = exf v2 amem.

  (* TODO: What happens when you make the variable thing have explicit param? 
  I think that there should be no change? *)
  Definition NISecurity := atk_sim_sec (fun _ => NICorruptor) (fun _ => NIExfiltrator).
End ni.

Section rd.
  Import MetaSyntax AtkSyntax.Prms.
  Import AtkSyntax (AdvCorruptor, AdvExfiltrator).
  Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

  (* Passive *)
  Definition RDCorruptor `{!AdvDevicePrm} (corr : AdvCorruptor) : Prop := 
    forall mem v, corr v mem = v.

  (* TODO: What happens when you make the variable thing have explicit param? 
  I think that there should be no change? *)
  Definition RDSecurity := atk_sim_sec (fun _ => RDCorruptor) (fun _ _ => True).
End rd.

(* To define program behavior, 
   we can just define mem_init, 
   So, this can initialize adversary memory, 
   and maybe leak something to the adversary initially as well.
   The order should be leak then corrupt.
   We can then think about
   

   Another thing to keep in mind is that we might want to
   count the number of while iterations.


*)
