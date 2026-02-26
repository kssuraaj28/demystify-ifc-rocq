From Stdlib Require List ssreflect.
Import List List.ListNotations ssreflect.

Require VarVal MetaSyntax AtkSyntax Semantics.
Import 
  VarVal
  MetaSyntax 
  AtkSyntax.Prms 
  AtkSyntax (AdvCorruptor, AdvExfiltrator, erase_prog)
  Semantics.Notations.

#[local] Notation CleanProg := CleanSyntax.Prog.
#[local] Notation AtkProg := AtkSyntax.Prog.
#[local] Notation AtkVarSrc := AtkSyntax.VarSrc.
#[local] Notation AtkVarDst := AtkSyntax.VarDst.

Section sim_security.
  (* You need a type and an interpretation as an AdvCorruptor *)
  (* You need a type and an interpretation as an AdvInfiltrator *)
  (* You could also have a predicate on AdvCorruptors.. *)


  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm}.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.
  Check ltac:(exact SrcDstVarPrm).

  (* What went up must come down *)
  Variable IdealCorruptor : forall `{!AdvDevicePrm},  AdvCorruptor -> Prop.
  Variable IdealExfiltrator : forall `{!AdvDevicePrm}, AdvExfiltrator -> Prop.

  Section lift.
    Context `{!AdvDevicePrm}.

    (* I don't use exact: in def. *)
    Section def.
      Let def (vs : AtkVarSrc) : Prop. Proof.
        move: vs => [v].
        case: (is_untrusted v) => [corr | _].
        - exact (IdealCorruptor corr).
        - exact (True).
      Defined.

      Definition IdealSrcVar := 
        ltac:(
          let t := def in
          let t := eval hnf in t in 
          let t := eval cbv zeta in t in
          exact t).
    End def.

    Section def.
      Let def (vd : AtkVarDst) : Prop. Proof.
        move: vd => [v].
        case: (is_public v) => [exf | _].
        - exact (IdealExfiltrator exf).
        - exact (True).
      Defined.

    Definition IdealDstVar := ltac:(
      let t := def in 
      let t := eval hnf in t in
      let t := eval cbv zeta in t in
      exact t).
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
    ⟦ rp ⟧ = ⟦ ip ⟧.
End sim_security.
