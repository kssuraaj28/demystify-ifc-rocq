From Stdlib Require List ssreflect.
Import List ssreflect.

Require VarVal Store Tacs MetaSyntax AtkSyntax. 
Import VarVal Store Tacs MetaSyntax AtkSyntax.Prms.

#[local] Notation AtkFullProg := AtkSyntax.Prog.
#[local] Notation AtkPartProg := AtkSyntax.Cmd.
#[local] Notation AtkVarSrc := AtkSyntax.VarSrc.
#[local] Notation AtkVarDst := AtkSyntax.VarDst.
#[local] Notation AtkValExp := AtkSyntax.ValExp.
#[local] Notation AtkBoolExp := AtkSyntax.BoolExp.
#[local] Notation AdvMaulIniter := AtkSyntax.AdvMaulIniter.
#[local] Notation OptionalLeak := (option LeakVals).

Section cfg.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvMemPrm}.

  (* What is 'state'? *)
  Inductive Cfg := 
    mk_cfg (store : Store) (amem: AdvMem) (cont : AtkPartProg).
End cfg.

Section event.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Inductive Action :=
    | assignment (optlk : OptionalLeak)
    | if_choice (choice : bool)
    | while_choice (choice : bool)
    | epsilon
    | terminate.

  (* Our definition is super lockstep. If it works, I think it's good. *)
  Definition Event : Type :=
    Action * StoreView is_trusted.
End event.

(* This section precisely defines adversary power *)
Section store_interaction.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvMemPrm}.

  Section store_read_w_adv.
    Let def (st : Store) (vs : AtkVarSrc) (amem : AdvMem) : Vals. Proof.
      destruct vs as [v adv].
      pose (orig_val := get_from_store st v). 
      destruct (is_untrusted v); ltac2:(goals [@UNTR; @TR]).
      [UNTR]: { exact (adv orig_val amem). }
      [TR]: { exact (orig_val). }
    Defined.

    (* What does it mean to read from a store when you have an adversary *)
    Definition store_read_w_adv := ltac:(hnf_clean def).
  End store_read_w_adv.

  Section store_update_w_adv.
    Let def (s : Store) (vd : AtkVarDst) (vl : Vals) (amem : AdvMem) : 
          Store * AdvMem *  OptionalLeak. Proof.
      destruct vd as [v exf].
      pose (s' := update_to_store s v vl).
      destruct (is_public v); ltac2:(goals [@PUB; @SEC]).
      [PUB]: {
        destruct (exf vl amem) as [lk amem'].
        exact (s', amem', (Some lk)).
        }
      [SEC]: {
        exact (s', amem, None).
        }
    Defined.
  (* What does it mean to write to a store when you have an adversary *)
  Definition store_update_w_adv := ltac:(hnf_clean def).
  End store_update_w_adv.
End store_interaction.

(* Semantics of evaluation with an adversary *)
Section semantics.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvMemPrm}.
  Import Store.Notations. 
  (* 
    Where should these be imported. Probably, I need to have a notation
    delimiter key also.
  *)
  
  Definition val_exp_eval (e : AtkValExp) (store : Store) (amem : AdvMem) : Vals :=
    let: mk_vl_exp vs1 vs2 comp := e in
    let: get_val := fun vs => store_read_w_adv store vs amem in 
    let: val1 := get_val vs1 in
    let: val2 := get_val vs2 in
    comp val1 val2.

  Definition bool_exp_eval (be : AtkBoolExp) (store : Store) (amem : AdvMem) : bool :=
    let: mk_bl_exp vs test := be in
    let: val := store_read_w_adv store vs amem in 
    test val.

  Definition step (cfg : Cfg) : Cfg * Action :=  
    let: mk_cfg store amem cmd := cfg in 
    ( fix step cmd store amem {struct cmd} :=
      match cmd with 
      | skip =>  
        (mk_cfg store amem skip, terminate)

      | assign vd exp => 
          let: val := (val_exp_eval exp store amem) in
          let: (store', amem', optlk) := store_update_w_adv store vd val amem in
          (mk_cfg store' amem' skip, assignment optlk)

      (* The order matters here *)
      | seq skip c => 
        (mk_cfg store amem c, epsilon)

      (* 
        I hate this. However, maybe we can think about whether adversaries can get
        some power here..
      *)
      | seq c1 c2 => 
          let: (mk_cfg store' amem' c1', action) := step c1 store amem in
          (mk_cfg store' amem' (seq c1' c2), action)

      | cond exp b1 b2 =>
          let: test := (bool_exp_eval exp store amem) in
          let: branch := if test is true then b1 else b2 in
          (mk_cfg store amem branch, if_choice test)

      | while exp while_bdy  =>
          let: test := (bool_exp_eval exp store amem) in
          let: cont := if test is false then skip else while_bdy in
          (mk_cfg store amem cont, while_choice test)
      end
    ) cmd store amem.

  Notation NeList A := (A * list A)%type.

  Fixpoint multi_step (n : nat) (cfg: Cfg) : NeList (Cfg * Action) :=
    match n with 
    | 0 => (step cfg, nil)
    | S n' =>
        let: ((cfg', ev'), lst') := multi_step n' cfg in
        (step cfg', (cfg', ev') :: lst') (* This naming is a little stupid *)
    end.

  Definition create_event (inp : Cfg * Action) : Event :=
    let: (mk_cfg s _ _, a) := inp in
    (a, ⟨s⟩).

  (* Ideally this would be a coinductive type *)
  Definition Behavior := Store -> nat -> NeList Event.

  Section init_store_maul.
    Let def (s : Store) (amem : AdvMem) (adv_maul_init : AdvMaulIniter) : Store. Proof.
      intro v.
      pose (orig_val := s v).
      destruct (is_untrusted v) eqn: VEq; ltac2:(goals [@UNTR; @TR]).
      [UNTR]: { apply adv_maul_init; [exact amem| esplit; exact VEq | exact orig_val]. }
      [TR]: { exact (orig_val). }
    Defined.
    Definition init_store_maul := ltac:(hnf_clean def).
  End init_store_maul.

  Definition prog_behavior (p : AtkFullProg) : Behavior :=
    let: (prog, amem_init, amaul_init) := p in
    fun init_store step_cnt =>
      let: init_adv := amem_init ⟨init_store⟩ in
      let: init_store_mauled := 
        init_store_maul init_store init_adv amaul_init
      in 
      let: init_cfg := mk_cfg init_store_mauled init_adv prog in
      let: (fst, lst) := multi_step step_cnt init_cfg in
      (create_event fst, map create_event lst).
End semantics.

Module Notations.
  Notation "⟦ p ⟧" := (prog_behavior p).
End Notations.
