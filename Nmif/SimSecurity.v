From Stdlib Require List ssreflect.
Import List List.ListNotations ssreflect.

Require VarVal MetaSyntax AtkSyntax Semantics Tacs.
Import 
  VarVal
  MetaSyntax 
  AtkSyntax.Prms 
  AtkSyntax (AdvCorruptor, AdvExfiltrator, erase_prog)
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

  (* This itself should not be Prop I think *)
  (* Another thing we could do is make the AdvMem an operational type class..
  *)
  Fail Check 5.
  Record InpType `{!AdvDevicePrm} :=
    {
      DevPred : Prop; (* Predicate on the device itself *)
      CorruptorPred : AdvCorruptor -> Prop;
      ExfiltratorPred : AdvExfiltrator -> Prop
    }. 

  Variable input : forall `{!AdvDevicePrm}, InpType.  Fail Check _ : input.

  Notation IdealCorruptor := (CorruptorPred input).
  Notation IdealExfiltrator := (ExfiltratorPred input).
  Notation IdealDevice := ( forall `{!AdvDevicePrm}, Prop.

  Section lift.
    Context `{!AdvDevicePrm}.

    (* I don't use exact: in def. *)
    Section def.
      Let def (vs : AtkVarSrc) : Prop. Proof.
        destruct vs as [v corr].
        destruct (is_untrusted v); ltac2:(goals [@CORR ; @CLEAN]).
        [CORR]: { exact (IdealCorruptor corr). }
        [CLEAN]: { exact (True). }
      Defined.

      (* TODO: This should be refactored out.. *)
      Definition IdealSrcVar := 
        ltac:(hnf_clean def).
    End def.

    Section def.
      Let def (vd : AtkVarDst) : Prop. Proof.
        destruct vd as [v exf].
        destruct (is_public v); ltac2:(goals [@CORR ; @CLEAN]).
        [CORR]: { exact (IdealExfiltrator exf). }
        [CLEAN]: { exact (True). }
      Defined.

    Definition IdealDstVar := 
        ltac:(hnf_clean def).
    End def.

    Hint Extern 0 SrcDstPredPrm => exact ({|
        SrcPred := IdealSrcVar;
        DstPred := IdealDstVar;
    |}) : typeclass_instances.

    (* This namespacing thing is stupid. TODO *)
    Definition IdealProg := MetaSyntax.ProgPred.
  End lift.

  Let ExpAtkProg (m: AdvDevicePrm) : Type := AtkProg.

  Definition atk_sim_sec (p : CleanProg) := Eval unfold ExpAtkProg in
    forall rad (rp : ExpAtkProg rad),  erase_prog rp = p ->
    exists iad (ip : ExpAtkProg iad),  erase_prog ip = p /\
    IdealProg ip /\
    IdealAdvDevice iad /\
    ⟦ rp ⟧ = ⟦ ip ⟧.
End sim_security.
