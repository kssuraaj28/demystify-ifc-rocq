Require VarVal MetaSyntax AtkSyntax SimSecurity.
Import 
  VarVal
  MetaSyntax 
  AtkSyntax.Prms
  AtkSyntax (AdvCorruptor, AdvExfiltrator)
  SimSecurity.

#[local]  Notation AtkVarSrc := AtkSyntax.VarSrc.
#[local]  Notation AtkVarDst := AtkSyntax.VarDst.

Module nmif.
  Section nmif.
    Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

    (* 
      TODO
      Notice here we make AdvDevicePrm explicit. 
      But in atk_sim_sec it was implicit?
    *)
    Definition IdealCorruptor `(!AdvDevicePrm) (corr : AdvCorruptor) : Prop := 
      forall mem v1 v2, corr v1 mem = corr v2 mem.

    Definition IdealExfiltrator `(!AdvDevicePrm) (exf : AdvExfiltrator) : Prop := 
      True.

    Definition Security := atk_sim_sec IdealCorruptor IdealExfiltrator.
  End nmif.
End nmif.

Module ni.
  Section ni.
    Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

    (* Corruptor does not corrupt anything *)
    Definition IdealCorruptor `(!AdvDevicePrm) (corr : AdvCorruptor) : Prop := 
      forall mem v, corr v mem = v.

    (* Exfiltrator does not exfiltrate anything *)
    Definition IdealExfiltrator `(!AdvDevicePrm) (exf : AdvExfiltrator) : Prop := 
      forall v1 v2 amem,
        exf v1 amem = exf v2 amem.

    Definition Security := atk_sim_sec IdealCorruptor IdealExfiltrator.
  End ni.
End ni.

Module rd.
  Section rd.
    Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

    (* Corruptor does not corrupt anything *)
    Definition IdealCorruptor `(!AdvDevicePrm) (corr : AdvCorruptor) : Prop := 
      forall mem v, corr v mem = v.

    (* We don't place any restriction on exfiltrator *)
    Definition IdealExfiltrator `(!AdvDevicePrm) (exf : AdvExfiltrator) : Prop := 
      True.

    Definition Security := atk_sim_sec IdealCorruptor IdealExfiltrator.
  End rd.
End rd.
