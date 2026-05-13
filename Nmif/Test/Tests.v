From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics
        Noninterference Combined Simulator TypeSystem WIP2.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics
       Noninterference Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".

(* ============================================================
   BoolVars: degenerate single-variable instance (Vars := bool).
   All vars share one lattice level, all values are `false`, all
   stores are identical. Useful for checking purely structural
   commutation of `step` and `cmbcmd_step`.
   ============================================================ *)

Module BoolVars.

#[local] Instance cBoolDecEq : DecEq.DecEq bool :=
  {| DecEq.dec_eq := Bool.bool_dec |}.

#[local] Instance cVarPrm : VarPrm :=
  {| Vars := bool; vars_deceq := {| DecEq.dec_eq := Bool.bool_dec |} |}.
#[local] Instance cValPrm : ValPrm :=
  {| Vals := bool; val_ne := false |}.
#[local] Instance cAdvLeakPrm : AdvLeakPrm := unit.
(* All variables at secret + untrusted, so assignments are well-formed at any pc. *)
#[local] Instance cAdvLvlPrm : AdvLvlPrm :=
  fun _ => mk_lbl true false.

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

(* Adversary with a constant positive substep count, so the
   `repeat true atk_substeps` padding actually fires. *)
Definition cAdvN (n : nat) : AdvNextStep cAtkStates.
Proof.
  refine {| pre_cmd_action _ s := s;
            post_cmd_action _ _ := (tt, n);
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

(* Always-true guard, so while bodies actually unfold. *)
Definition trivBE_T : BoolExp := (v0, fun _ => true).

Definition cInner    : Cmd := assign v0 trivVE.
Definition cCondCmd  : Cmd := cond trivBE [cInner] [cInner].
Definition cAssign   : Cmd := cInner.
Definition cWhileF   : Cmd := while trivBE  [cInner].       (* guard false: cnt = []     *)
Definition cWhileT   : Cmd := while trivBE_T [cInner].      (* guard true : cnt = [_;_]  *)

Definition cStore : Store := fun _ => false.

(* Top label: public + untrusted. *)
Definition cPclblPubUntr : TypeSystem.PcLbl := mk_lbl true true.

(* Secret + untrusted: pub=false, untrusted=true.
   This is the secret-pc variant under the same untrusted bit. *)
Definition cPclblSecUntr : TypeSystem.PcLbl := mk_lbl true false.

Definition cS : Combined.CmbState :=
  {| Combined.real_store := cStore;
     Combined.ideal_store := cStore;
     Combined.sim_store := cStore;
     Combined.atk_st := tt |}.

Ltac wf_branch :=
  apply Forall_cons; [apply TypeSystem.wf_assign; vm_compute; reflexivity | apply Forall_nil].

Ltac wf_cond_two :=
  apply TypeSystem.wf_cond; [wf_branch | wf_branch].

Ltac solve_inv :=
  rewrite /Combined.Invariant /cS /Combined.StateInv;
  split;
  [ apply Forall_cons;
    [ rewrite /Combined.CmbCmdInv /Combined.CmbCmdCoreInv /cCondCmd /=;
      split; [wf_cond_two | wf_cond_two]
    | apply Forall_nil ]
  | split; reflexivity ].

(* ============================================================
   TT/TF/FT/FF: ratk × public(pclbl) corners. Invariant proved
   for each via solve_inv.
   ============================================================ *)
Section TT.
  Import Simulator. Import WIP2.

  Definition cB_TT : Combined.CmbCmd :=
    {| Combined.real_cmd := Some cCondCmd;
       Combined.real_atk_bit := true;
       Combined.ideal_cmd := Some cCondCmd;
       Combined.pc_lbl := cPclblPubUntr |}.

  Definition cC_TT : Combined.Cfg := (cS, [cB_TT]).

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step         := (step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Goal Combined.Invariant cC_TT.
  Proof. solve_inv. Qed.

  Goal step (extract_2cfg cC_TT) = extract_2cfg (comb_step cC_TT).
  Proof. vm_compute. reflexivity. Qed.
End TT.

Section TF.
  Import Simulator. Import WIP2.

  Definition cB_TF : Combined.CmbCmd :=
    {| Combined.real_cmd := Some cCondCmd;
       Combined.real_atk_bit := true;
       Combined.ideal_cmd := Some cCondCmd;
       Combined.pc_lbl := cPclblSecUntr |}.

  Definition cC_TF : Combined.Cfg := (cS, [cB_TF]).

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step         := (step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Goal Combined.Invariant cC_TF.
  Proof. solve_inv. Qed.

  Goal step (extract_2cfg cC_TF) = extract_2cfg (comb_step cC_TF).
  Proof. vm_compute. reflexivity. Qed.
End TF.

Section FT.
  Import Simulator. Import WIP2.

  Definition cB_FT : Combined.CmbCmd :=
    {| Combined.real_cmd := Some cCondCmd;
       Combined.real_atk_bit := false;
       Combined.ideal_cmd := Some cCondCmd;
       Combined.pc_lbl := cPclblPubUntr |}.

  Definition cC_FT : Combined.Cfg := (cS, [cB_FT]).

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step         := (step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Goal Combined.Invariant cC_FT.
  Proof. solve_inv. Qed.

  Goal step (extract_2cfg cC_FT) = extract_2cfg (comb_step cC_FT).
  Proof. vm_compute. reflexivity. Qed.
End FT.

Section FF.
  Import Simulator. Import WIP2.

  Definition cB_FF : Combined.CmbCmd :=
    {| Combined.real_cmd := Some cCondCmd;
       Combined.real_atk_bit := false;
       Combined.ideal_cmd := Some cCondCmd;
       Combined.pc_lbl := cPclblSecUntr |}.

  Definition cC_FF : Combined.Cfg := (cS, [cB_FF]).

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step         := (step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Goal Combined.Invariant cC_FF.
  Proof. solve_inv. Qed.

  Goal step (extract_2cfg cC_FF) = extract_2cfg (comb_step cC_FF).
  Proof. vm_compute. reflexivity. Qed.
End FF.

(* ============================================================
   Other command shapes (assignments, while loops, asymmetric
   rcmd/icmd, multi-cmbcmd lists). Invariants not re-proved —
   each scenario is constructed so it should clearly hold.
   ============================================================ *)
Section MoreShapes.
  Import Simulator. Import WIP2.

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step         := (step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Definition mkB (rc ic : Cmd) (ratk : bool) (pcl : TypeSystem.PcLbl)
    : Combined.CmbCmd :=
    {| Combined.real_cmd := Some rc;
       Combined.real_atk_bit := ratk;
       Combined.ideal_cmd := Some ic;
       Combined.pc_lbl := pcl |}.

  (* --- Plain assign, all four (ratk, pclbl) corners. --- *)
  Goal step (extract_2cfg (cS, [mkB cAssign cAssign true  cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB cAssign cAssign true  cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cAssign cAssign true  cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB cAssign cAssign true  cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cAssign cAssign false cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB cAssign cAssign false cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cAssign cAssign false cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB cAssign cAssign false cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- While with false guard (cnt = []). --- *)
  Goal step (extract_2cfg (cS, [mkB cWhileF cWhileF true  cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB cWhileF cWhileF true  cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cWhileF cWhileF false cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB cWhileF cWhileF false cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- While with true guard (cnt = [body; while ...], length 2). --- *)
  Goal step (extract_2cfg (cS, [mkB cWhileT cWhileT true  cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB cWhileT cWhileT true  cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cWhileT cWhileT false cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB cWhileT cWhileT false cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cWhileT cWhileT false cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB cWhileT cWhileT false cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Asymmetric rcmd vs icmd (only valid under untrusted pclbl). --- *)
  Goal step (extract_2cfg (cS, [mkB cAssign  cCondCmd true  cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB cAssign  cCondCmd true  cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cCondCmd cWhileT  false cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB cCondCmd cWhileT  false cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB cWhileT  cAssign  true  cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB cWhileT  cAssign  true  cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Multi-cmbcmd list (tests that the tail is propagated correctly). --- *)
  Definition cMulti : list Combined.CmbCmd :=
    [ mkB cCondCmd cCondCmd true  cPclblPubUntr
    ; mkB cAssign  cAssign  false cPclblSecUntr
    ; mkB cWhileT  cWhileT  true  cPclblPubUntr ].

  Goal step (extract_2cfg (cS, cMulti)) = extract_2cfg (comb_step (cS, cMulti)).
  Proof. vm_compute. reflexivity. Qed.

  Definition cMulti2 : list Combined.CmbCmd :=
    [ mkB cAssign  cCondCmd true  cPclblPubUntr
    ; mkB cWhileF  cWhileF  false cPclblSecUntr ].

  Goal step (extract_2cfg (cS, cMulti2)) = extract_2cfg (comb_step (cS, cMulti2)).
  Proof. vm_compute. reflexivity. Qed.
End MoreShapes.

(* ============================================================
   Non-zero attacker substeps: tests the `repeat true substeps`
   padding in zip / combine_extend that cAdv (substeps=0) skips.
   Only ratk=true cases are interesting — with ratk=false the
   substep count is forced to 0 anyway.
   ============================================================ *)
Section NonZeroSubsteps.
  Import Simulator. Import WIP2.

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step2        := (WIP2.step (cAdvN 2) (construct_simulator (cAdvN 2))).
  Notation comb_step2   := (Combined.cfg_step (cAdvN 2)).

  Notation step5        := (WIP2.step (cAdvN 5) (construct_simulator (cAdvN 5))).
  Notation comb_step5   := (Combined.cfg_step (cAdvN 5)).

  Definition mkB' (rc ic : Cmd) (ratk : bool) (pcl : TypeSystem.PcLbl)
    : Combined.CmbCmd :=
    {| Combined.real_cmd := Some rc;
       Combined.real_atk_bit := ratk;
       Combined.ideal_cmd := Some ic;
       Combined.pc_lbl := pcl |}.

  (* substeps=2, ratk=true, varying cmd shape and pclbl. *)
  Goal step2 (extract_2cfg (cS, [mkB' cAssign  cAssign  true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB' cAssign  cAssign  true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB' cCondCmd cCondCmd true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB' cCondCmd cCondCmd true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB' cCondCmd cCondCmd true cPclblSecUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB' cCondCmd cCondCmd true cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB' cWhileT  cWhileT  true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB' cWhileT  cWhileT  true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB' cWhileF  cWhileF  true cPclblSecUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB' cWhileF  cWhileF  true cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* Asymmetric rcmd/icmd with substeps=2. *)
  Goal step2 (extract_2cfg (cS, [mkB' cAssign  cCondCmd true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB' cAssign  cCondCmd true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB' cCondCmd cWhileT  true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB' cCondCmd cWhileT  true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* Larger substep count. *)
  Goal step5 (extract_2cfg (cS, [mkB' cCondCmd cCondCmd true cPclblPubUntr])) =
       extract_2cfg (comb_step5 (cS, [mkB' cCondCmd cCondCmd true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* Multi-cmbcmd list with non-zero substeps. *)
  Definition cMultiN : list Combined.CmbCmd :=
    [ mkB' cCondCmd cCondCmd true  cPclblPubUntr
    ; mkB' cAssign  cAssign  false cPclblSecUntr
    ; mkB' cWhileT  cAssign  true  cPclblSecUntr ].

  Goal step2 (extract_2cfg (cS, cMultiN)) =
       extract_2cfg (comb_step2 (cS, cMultiN)).
  Proof. vm_compute. reflexivity. Qed.
End NonZeroSubsteps.

(* ============================================================
   None real_cmd / None ideal_cmd: these arise naturally as
   padding entries from previous step iterations, and exercise
   the `sim_active` None-branch and the optcmd_stp_* defaults.
   ============================================================ *)
Section NoneCases.
  Import Simulator. Import WIP2.

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step2        := (WIP2.step (cAdvN 2) (construct_simulator (cAdvN 2))).
  Notation comb_step2   := (Combined.cfg_step (cAdvN 2)).
  Notation step         := (WIP2.step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Definition mkB_opt (rc ic : option Cmd) (ratk : bool) (pcl : TypeSystem.PcLbl)
    : Combined.CmbCmd :=
    {| Combined.real_cmd := rc;
       Combined.real_atk_bit := ratk;
       Combined.ideal_cmd := ic;
       Combined.pc_lbl := pcl |}.

  (* --- real_cmd = None, ideal_cmd = Some _. --- *)
  Goal step (extract_2cfg (cS, [mkB_opt None (Some cAssign)  false cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None (Some cAssign)  false cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt None (Some cCondCmd) false cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None (Some cCondCmd) false cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt None (Some cWhileT)  true  cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None (Some cWhileT)  true  cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt None (Some cAssign)  true  cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None (Some cAssign)  true  cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- real_cmd = Some _, ideal_cmd = None. --- *)
  Goal step (extract_2cfg (cS, [mkB_opt (Some cAssign)  None false cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt (Some cAssign)  None false cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt (Some cCondCmd) None true  cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt (Some cCondCmd) None true  cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt (Some cWhileT)  None true  cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt (Some cWhileT)  None true  cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Both None: pure padding entry. --- *)
  Goal step (extract_2cfg (cS, [mkB_opt None None false cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None None false cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt None None false cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None None false cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt None None true  cPclblPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None None true  cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB_opt None None true  cPclblSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB_opt None None true  cPclblSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- None cases with non-zero substeps (exercises padding x None). --- *)
  Goal step2 (extract_2cfg (cS, [mkB_opt None (Some cCondCmd) true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB_opt None (Some cCondCmd) true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB_opt (Some cCondCmd) None true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB_opt (Some cCondCmd) None true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB_opt None None true cPclblPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB_opt None None true cPclblPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Mixed Some/None across a multi-cmbcmd list. --- *)
  Definition cMultiNone : list Combined.CmbCmd :=
    [ mkB_opt (Some cCondCmd) (Some cCondCmd) true  cPclblPubUntr
    ; mkB_opt None            (Some cAssign)  false cPclblSecUntr
    ; mkB_opt (Some cWhileT)  None            true  cPclblSecUntr
    ; mkB_opt None            None            false cPclblPubUntr ].

  Goal step (extract_2cfg (cS, cMultiNone)) =
       extract_2cfg (comb_step (cS, cMultiNone)).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, cMultiNone)) =
       extract_2cfg (comb_step2 (cS, cMultiNone)).
  Proof. vm_compute. reflexivity. Qed.
End NoneCases.

End BoolVars.

(* ============================================================
   Var4Vars: one variable per lattice quadrant. Stores can
   genuinely differ across real / ideal / sim while respecting
   the invariant, so tests distinguish structural commutation
   from coincidence under all-equal values.
   ============================================================ *)

Module Var4Vars.

Inductive Var4 := PT | PU | ST | SU.

Definition Var4_eq_dec : forall (x y : Var4), {x = y} + {x <> y}.
Proof. decide equality. Defined.

#[local] Instance cVarPrm : VarPrm :=
  {| Vars := Var4; vars_deceq := {| DecEq.dec_eq := Var4_eq_dec |} |}.
#[local] Instance cValPrm : ValPrm :=
  {| Vals := bool; val_ne := false |}.
#[local] Instance cAdvLeakPrm : AdvLeakPrm := unit.
#[local] Instance cAdvLvlPrm : AdvLvlPrm :=
  fun v => match v with
           | PT => mk_lbl false true   (* trusted, public *)
           | PU => mk_lbl true  true   (* untrusted, public *)
           | ST => mk_lbl false false  (* trusted, secret *)
           | SU => mk_lbl true  false  (* untrusted, secret *)
           end.

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

Definition cAdvN (n : nat) : AdvNextStep cAtkStates.
Proof.
  refine {| pre_cmd_action _ s := s;
            post_cmd_action _ _ := (tt, n);
            pre_cmd_wf_int := _;
            pre_cmd_wf_conf := _;
            post_cmd_wf := _ |}.
  - by [].
  - rewrite /Noninterfering=> *. by [].
  - rewrite /Noninterfering=> *. by [].
Defined.

(* ----------------------------------------------------------------
   Distinct stores that respect the invariant:
   - real and ideal agree on trusted vars {PT, ST}
   - real and sim   agree on public  vars {PT, PU}
   real :  PT=t  PU=t  ST=t  SU=t
   ideal:  PT=t  PU=f  ST=t  SU=f   (differs on PU, SU vs real)
   sim  :  PT=t  PU=t  ST=f  SU=f   (differs on ST, SU vs real)
   ---------------------------------------------------------------- *)

Definition cReal : Store :=
  fun v => match v with PT => true | PU => true | ST => true | SU => true end.
Definition cIdeal : Store :=
  fun v => match v with PT => true | PU => false | ST => true | SU => false end.
Definition cSim : Store :=
  fun v => match v with PT => true | PU => true | ST => false | SU => false end.

Definition cS : Combined.CmbState :=
  {| Combined.real_store  := cReal;
     Combined.ideal_store := cIdeal;
     Combined.sim_store   := cSim;
     Combined.atk_st      := tt |}.

(* Sanity check: the chosen stores satisfy StateInv. *)
Goal Combined.StateInv (AtkStates := cAtkStates) cS.
Proof.
  rewrite /Combined.StateInv /cS /VarValStore.store_to_view.
  split; apply functional_extensionality; case=> //.
Qed.

(* Identity-on-first-arg value combinator. *)
Definition idVE (src : Vars) : ValExp := (src, src, fun a _ => a).

(* Identity boolean guard, reading one variable. *)
Definition idBE (src : Vars) : BoolExp := (src, fun b => b).

Definition cAssPT          : Cmd := assign PT (idVE PT).
Definition cAssPU_fromPT   : Cmd := assign PU (idVE PT).
Definition cAssSU_fromPT   : Cmd := assign SU (idVE PT).

Definition cCondPT : Cmd := cond (idBE PT) [cAssPT] [cAssPT].
Definition cCondPU : Cmd := cond (idBE PU) [cAssPT] [cAssPT].

Definition cWhilePT : Cmd := while (idBE PT) [cAssPT].
Definition cWhilePU : Cmd := while (idBE PU) [cAssPT].

Definition pcPubUntr : TypeSystem.PcLbl := mk_lbl true true.
Definition pcSecUntr : TypeSystem.PcLbl := mk_lbl true false.

Section Tests.
  Import Simulator. Import WIP2.

  Notation extract_2cfg := (extract_2cfg (AtkStates := cAtkStates)).
  Notation step         := (WIP2.step cAdv (construct_simulator cAdv)).
  Notation comb_step    := (Combined.cfg_step cAdv).

  Notation step2        := (WIP2.step (cAdvN 2) (construct_simulator (cAdvN 2))).
  Notation comb_step2   := (Combined.cfg_step (cAdvN 2)).

  Definition mkB (rc ic : option Cmd) (ratk : bool) (pcl : TypeSystem.PcLbl)
    : Combined.CmbCmd :=
    {| Combined.real_cmd := rc;
       Combined.real_atk_bit := ratk;
       Combined.ideal_cmd := ic;
       Combined.pc_lbl := pcl |}.

  (* --- Conds with a PU guard: real (PU=t) and ideal (PU=f) take opposite
         branches; identical branches still keep the invariant projections
         in sync. --- *)
  Goal step (extract_2cfg (cS, [mkB (Some cCondPU) (Some cCondPU) false pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cCondPU) (Some cCondPU) false pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cCondPU) (Some cCondPU) true  pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cCondPU) (Some cCondPU) true  pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Conds with a PT guard (all stores agree on PT). --- *)
  Goal step (extract_2cfg (cS, [mkB (Some cCondPT) (Some cCondPT) false pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cCondPT) (Some cCondPT) false pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cCondPT) (Some cCondPT) true  pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cCondPT) (Some cCondPT) true  pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Assignments touching different lattice points. --- *)
  Goal step (extract_2cfg (cS, [mkB (Some cAssPT)         (Some cAssPT)         false pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cAssPT)         (Some cAssPT)         false pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cAssPU_fromPT)  (Some cAssPU_fromPT)  false pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cAssPU_fromPT)  (Some cAssPU_fromPT)  false pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cAssSU_fromPT)  (Some cAssSU_fromPT)  false pcSecUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cAssSU_fromPT)  (Some cAssSU_fromPT)  false pcSecUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cAssPT)         (Some cAssPT)         true  pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cAssPT)         (Some cAssPT)         true  pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- While loops with public-trusted vs public-untrusted guards. --- *)
  Goal step (extract_2cfg (cS, [mkB (Some cWhilePT) (Some cWhilePT) false pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cWhilePT) (Some cWhilePT) false pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cWhilePU) (Some cWhilePU) true  pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cWhilePU) (Some cWhilePU) true  pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Asymmetric rcmd vs icmd, public pclbl (invariant case a). --- *)
  Goal step (extract_2cfg (cS, [mkB (Some cAssPT)   (Some cCondPU)  true pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cAssPT)   (Some cCondPU)  true pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cCondPT)  (Some cWhilePU) true pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cCondPT)  (Some cWhilePU) true pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- None branches (padding) with non-trivial stores. --- *)
  Goal step (extract_2cfg (cS, [mkB None (Some cCondPU) false pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB None (Some cCondPU) false pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB (Some cCondPU) None true  pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB (Some cCondPU) None true  pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step (extract_2cfg (cS, [mkB None None true pcPubUntr])) =
       extract_2cfg (comb_step (cS, [mkB None None true pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Non-zero substeps with the asymmetric stores. --- *)
  Goal step2 (extract_2cfg (cS, [mkB (Some cCondPU) (Some cCondPU) true pcPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB (Some cCondPU) (Some cCondPU) true pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB (Some cAssPU_fromPT) (Some cAssPU_fromPT) true pcPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB (Some cAssPU_fromPT) (Some cAssPU_fromPT) true pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, [mkB (Some cWhilePU) (Some cWhilePU) true pcPubUntr])) =
       extract_2cfg (comb_step2 (cS, [mkB (Some cWhilePU) (Some cWhilePU) true pcPubUntr])).
  Proof. vm_compute. reflexivity. Qed.

  (* --- Multi-cmbcmd list mixing shapes, labels, ratk, None entries. --- *)
  Definition cMulti : list Combined.CmbCmd :=
    [ mkB (Some cCondPU)        (Some cCondPU)        true  pcPubUntr
    ; mkB (Some cAssPT)         (Some cAssPT)         false pcPubUntr
    ; mkB None                  (Some cAssPU_fromPT)  false pcPubUntr
    ; mkB (Some cWhilePU)       None                  true  pcPubUntr
    ; mkB (Some cAssSU_fromPT)  (Some cAssSU_fromPT)  false pcSecUntr ].

  Goal step (extract_2cfg (cS, cMulti)) = extract_2cfg (comb_step (cS, cMulti)).
  Proof. vm_compute. reflexivity. Qed.

  Goal step2 (extract_2cfg (cS, cMulti)) = extract_2cfg (comb_step2 (cS, cMulti)).
  Proof. vm_compute. reflexivity. Qed.
End Tests.

End Var4Vars.
