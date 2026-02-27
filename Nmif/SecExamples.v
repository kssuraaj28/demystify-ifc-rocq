Require VarVal MetaSyntax AtkSyntax SimSecurity.

Import 
  VarVal
  MetaSyntax 
  AtkSyntax.Prms
  AtkSyntax (AdvCorruptor, AdvExfiltrator)
  SimSecurity.

#[local] Notation AtkVarSrc := AtkSyntax.VarSrc.
#[local] Notation AtkVarDst := AtkSyntax.VarDst.
#[local] Notation SimInput := SimSecurity.InpType.

Module nmif.
  Section nmif.
    Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

    Definition IdealPreds `(!AdvMemPrm) : SimInput := {|
        MemInitPred := fun amem_init => True;

        MaulInitPred := fun amaul_init => 
                          forall amem var v1 v2, 
                              amaul_init amem var v1 =
                              amaul_init amem var v2; 

        (* TODO: Maybe have an `is_constant` function *)
        CorruptorPred := fun corr => 
                           forall mem v1 v2, 
                             corr v1 mem = 
                             corr v2 mem ;

        ExfiltratorPred := fun exf => 
                             True ;
     |}.

    Definition Security := atk_sim_sec IdealPreds.
  End nmif.
End nmif.

Module ni.
  Section ni.
    Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

    Definition IdealPreds `(!AdvMemPrm) : SimInput := {|
        (* No restriction on initial initialization *)
        MemInitPred := fun amem_init => True;

        (* No corruption allowed initially *)
        MaulInitPred := fun amaul_init => 
                          forall amem var val,
                              amaul_init amem var val = val;

        (* No corruption allowed during runs *)
        CorruptorPred := fun corr =>
                           forall mem v,
                             corr v mem = v;

        (* Exfiltration does not get access to values*)
        ExfiltratorPred := fun exf => 
                             forall amem v1 v2,
                               exf v1 amem = exf v2 amem
     |}.

    Definition Security := atk_sim_sec IdealPreds.
  End ni.
End ni.

Module rd.
  Section rd.
    Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

    Definition IdealPreds `(!AdvMemPrm) : SimInput := {|
        (* No restriction on initial initialization *)
        MemInitPred := fun amem_init => True;

        (* No corruption allowed initially *)
        MaulInitPred := fun amaul_init => 
                          forall amem var val,
                              amaul_init amem var val = val;

        (* No corruption allowed during runs *)
        CorruptorPred := fun corr =>
                           forall mem v,
                             corr v mem = v;

        (* Declassification is allowed *)
        ExfiltratorPred := fun exf => True
     |}.

    Definition Security := atk_sim_sec IdealPreds.
  End rd.
End rd.

(* Blow people's mind by defining TE in one minute *)
