From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics
        Noninterference Combined Simulator TypeSystem WIP2.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics
       Noninterference Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".

Section TT_MRE.
  Import Simulator.
  Import WIP2.

  #[local] Instance cBoolDecEq : DecEq.DecEq bool :=
    {| DecEq.dec_eq := Bool.bool_dec |}.

  #[local] Instance cVarPrm : VarPrm :=
    {| Vars := bool; vars_deceq := cBoolDecEq |}.

  #[local] Instance cValPrm : ValPrm :=
    {| Vals := bool; val_ne := false |}.

  #[local] Instance cAdvLeakPrm : AdvLeakPrm := unit.

  #[local] Instance cAdvLvlPrm : AdvLvlPrm :=
    fun _ => mk_lbl true true.

  Definition cAtkStates : Type := unit.

  Definition cAdv : AdvNextStep cAtkStates.
  Proof.
    refine {| pre_cmd_action _ s := s;
              post_cmd_action _ _ := (tt, 0);
              pre_cmd_wf_int := _;
              pre_cmd_wf_conf := _;
              post_cmd_wf := _ |}.
    - by [].
    - rewrite /Noninterfering=> *. by [].
    - rewrite /Noninterfering=> *. by [].
  Defined.

  Definition v0 : Vars := false.
  Definition trivVE : ValExp := (v0, v0, fun a _ => a).
  Definition trivBE : BoolExp := (v0, fun b => b).

  Definition cInner : Cmd := assign v0 trivVE.
  Definition cRcmd  : Cmd := cond trivBE [cInner] [cInner].
  Definition cIcmd  : Cmd := cond trivBE [cInner] [cInner].

  Definition cStore : Store := fun _ => false.
  Definition cPclbl : TypeSystem.PcLbl := mk_lbl true true.

  Definition cB : Combined.CmbCmd :=
    {| Combined.real_cmd := Some cRcmd;
       Combined.real_atk_bit := true;   (* TT: real attacker active *)
       Combined.ideal_cmd := Some cIcmd;
       Combined.pc_lbl := cPclbl |}.

  Definition cS : Combined.CmbState :=
    {| Combined.real_store := cStore;
       Combined.ideal_store := cStore;
       Combined.sim_store := cStore;
       Combined.atk_st := tt |}.

  Definition cC : Combined.Cfg := (cS, [cB]).

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step         := (step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Eval cbn in step (extract_2cfg cC).
  Goal False.
    move e: (step (extract_2cfg cC)) => ?; move:e .
    rewrite [extract_2cfg _]/=/cRcmd/cIcmd.
    rewrite/step.
  Abort.

  Eval cbn in extract_2cfg (comb_step cC). (* I think that this is correct *)

  Definition cLhs := step (extract_2cfg cC).
  Definition cRhs := extract_2cfg (comb_step cC).

  Goal Combined.Invariant cC.
  Proof.
    rewrite /cC /Combined.Invariant /cS /Combined.StateInv.
    split.
    1:{ apply Forall_cons; [|apply Forall_nil].
        rewrite /cB /Combined.CmbCmdInv /Combined.CmbCmdCoreInv /=.
        split.
        1:{ apply: TypeSystem.wf_cond.
            1: apply Forall_cons; [apply: TypeSystem.wf_assign; reflexivity | apply Forall_nil].
            apply Forall_cons; [apply: TypeSystem.wf_assign; reflexivity | apply Forall_nil]. }
        apply: TypeSystem.wf_cond.
        1: apply Forall_cons; [apply: TypeSystem.wf_assign; reflexivity | apply Forall_nil].
        apply Forall_cons; [apply: TypeSystem.wf_assign; reflexivity | apply Forall_nil]. }
    split; reflexivity.
  Qed.

  Definition snd_atkcmd_isatk
    (cfg : Cfg (AtkStates1 := cAtkStates) (AtkStates2 := SimStates (AtkStates := cAtkStates))) : option bool :=
    match fst (fst cfg) with
    | (_, ac2) :: _ => Some ac2.(is_attacked)
    | []            => None
    end.

  Goal snd_atkcmd_isatk cLhs = Some true.
  Proof. vm_compute. reflexivity. Qed.

  Goal snd_atkcmd_isatk cRhs = Some true.
  Proof. vm_compute. reflexivity. Qed.

  Goal cLhs = cRhs.
  Proof. vm_compute. reflexivity. Qed.
End TT_MRE.
