From Stdlib Require List ssreflect.
Import List List.ListNotations ssreflect.

Require VarVal MetaSyntax AtkSyntax Semantics Tacs.
Import 
  VarVal
  MetaSyntax 
  AtkSyntax.Prms 
  AtkSyntax (
    AdvCorruptor,
    AdvExfiltrator,
    AdvMemIniter,
    AdvMaulIniter,
    erase_prog)
  Semantics.Notations
  Tacs.

#[local] Notation CleanProg := CleanSyntax.Prog.
#[local] Notation AtkProg := AtkSyntax.Prog.
#[local] Notation AtkVarSrc := AtkSyntax.VarSrc.
#[local] Notation AtkVarDst := AtkSyntax.VarDst.

(* You need to have a predicate over the initial adversary strategy as well. *)
Section sim_security.
  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm}.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.
  Check ltac:(exact SrcDstVarPrm).

  (* 
    This thing is useless being :Prop because
    the elements are Props themselves
    I'd be curious what the extraction behaviour is
    TODO
  *)
  Record InpType `{!AdvMemPrm} :=
    {
      MemInitPred : AdvMemIniter -> Prop; 
      MaulInitPred : AdvMaulIniter -> Prop; 
      CorruptorPred : AdvCorruptor -> Prop;
      ExfiltratorPred : AdvExfiltrator -> Prop
    }. 

  Variable input : forall `{!AdvMemPrm}, InpType.  Fail Check _ : input.

  Notation IdealMemInit := (MemInitPred input).
  Notation IdealMaulInit := (MaulInitPred input).
  Notation IdealCorruptor := (CorruptorPred input).
  Notation IdealExfiltrator := (ExfiltratorPred input).

  Section lift.
    Context `{!AdvMemPrm}.

    Section ideal_src_var.
      Let def (vs : AtkVarSrc) : Prop. Proof.
        destruct vs as [v corr].
        destruct (is_untrusted v); ltac2:(goals [@CORR ; @CLEAN]).
        [CORR]: { exact (IdealCorruptor corr). }
        [CLEAN]: { exact (True). }
      Defined.

      Definition IdealSrcVar := ltac:(hnf_clean def).
    End ideal_src_var.

    Section ideal_dst_var.
      Let def (vd : AtkVarDst) : Prop. Proof.
        destruct vd as [v exf].
        destruct (is_public v); ltac2:(goals [@CORR ; @CLEAN]).
        [CORR]: { exact (IdealExfiltrator exf). }
        [CLEAN]: { exact (True). }
      Defined.

      Definition IdealDstVar := ltac:(hnf_clean def).
    End ideal_dst_var.

    Hint Extern 0 SrcDstPredPrm => exact ({|
        SrcPred := IdealSrcVar;
        DstPred := IdealDstVar;
    |}) : typeclass_instances.

    Definition IdealPartProg := ltac:(hnf_clean MetaSyntax.ProgPred).

    Definition IdealProg : AtkProg -> Prop :=
      fun '(p, amem_init, amaul_init) =>
        IdealPartProg p /\
        IdealMemInit amem_init/\
        IdealMaulInit amaul_init.

  End lift.

  Let ExpAtkProg (m: AdvMemPrm) : Type := AtkProg.
  Definition atk_sim_sec (p : CleanProg) := Eval unfold ExpAtkProg in
    forall rm (rp : ExpAtkProg rm),  erase_prog rp = p ->
    exists im (ip : ExpAtkProg im),  erase_prog ip = p /\
    IdealProg ip /\ 
    ⟦ rp ⟧ = ⟦ ip ⟧.

End sim_security.
