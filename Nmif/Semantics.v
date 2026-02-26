From Stdlib Require List ssreflect.
Import List List.ListNotations ssreflect.

Require VarVal Store Tacs MetaSyntax AtkSyntax. 
Import VarVal Store Tacs MetaSyntax AtkSyntax.Prms.

#[local] Notation AtkProg := AtkSyntax.Prog.
#[local] Notation AtkVarSrc := AtkSyntax.VarSrc.
#[local] Notation AtkVarDst := AtkSyntax.VarDst.
#[local] Notation AtkValExp := AtkSyntax.ValExp.
#[local] Notation AtkBoolExp := AtkSyntax.BoolExp.
#[local] Notation OptionalLeak := (option LeakVals).

Section cfg.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvDevicePrm}.

  (* What is 'state'? *)
  Inductive Cfg := 
    mk_cfg (store : Store) (amem: AdvMem) (cont : AtkProg).
End cfg.

Section event.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.

  Inductive Action :=
    | assignment (optlk : OptionalLeak)
    | if_choice (choice : bool)
    | while_choice (choice : bool)
    | terminate.

  (* Our definition is super lockstep. If it works, I think it's good. *)
  Definition Event : Type :=
    Action * StoreView is_trusted.
End event.

(* This section precisely defines adversary power *)
Section store_interaction.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvDevicePrm}.

  Section store_read_w_adv.
    Let def (st : Store) (vs : AtkVarSrc) (amem : AdvMem) : Vals. Proof.
      destruct vs as [v adv].
      pose (orig_val := get_from_store st v). 
      destruct (is_untrusted v); ltac2:(goals [@UNTR; @TR]).
      [UNTR]: { exact (adv orig_val amem). }
      [TR]: { exact (orig_val). }
    Defined.

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
  Definition store_update_w_adv := ltac:(hnf_clean def).
  End store_update_w_adv.
End store_interaction.

Section semantics.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvDevicePrm}.
  Import Store.Notations. (* Where should these be imported. *)

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

  Definition step (cfg : Cfg) : Cfg * Event:=
    let: mk_cfg store amem prog := cfg in
    if prog isn't (cmd :: prog') then (cfg, (terminate , ⟨store⟩)) else  (* prog is skip *)

    match cmd with 
    | assign vd exp =>  
        let: cont := prog' in
        let: val := (val_exp_eval exp store amem) in
        let: (store', amem', optlk) := store_update_w_adv store vd val amem in
        let: event := (assignment optlk , ⟨store'⟩) in
        (mk_cfg store' amem' prog', event)

    | cond exp b1 b2 =>
        let: test := (bool_exp_eval exp store amem) in
        let: branch := if test is true then b1 else b2 in
        let: cont := (branch ++ prog') in
        let: cfg := mk_cfg store amem cont in
        (cfg, (if_choice test, ⟨ store ⟩))

    | while exp while_bdy  =>  
       let: test := (bool_exp_eval exp store amem) in
       let: cont := if test is false then prog' else (while_bdy ++ prog) in
       let: cfg := mk_cfg store amem cont in
       (cfg, (while_choice test, ⟨ store ⟩))
    end.
  Notation NeList A := (A * list A)%type.

  Fixpoint multi_step (n : nat) (cfg: Cfg) : NeList (Cfg * Event) :=
    match n with 
    | 0 => (step cfg, [])
    | S n' =>
        let: ((cfg', ev'), lst') := multi_step n' cfg in
        (step cfg', (cfg', ev') :: lst') (* This naming is a little stupid *)
    end.

  (* Ideally this would be a coinductive type *)
  Definition Behavior := Store -> nat -> list Event.

  Section init_source_maul.
    Let def (s : Store) : Store. Proof.
      intro v.
      pose (orig_val := s v).
      destruct (is_untrusted v) eqn: VEq; ltac2:(goals [@UNTR; @TR]).
      [UNTR]: { apply adv_maul_init; [esplit; exact VEq | exact orig_val]. }
      [TR]: { exact (orig_val). }
    Defined.
    Definition init_source_maul := ltac:(hnf_clean def).
  End init_source_maul.

  (* These names are absolutely disgusting. TODO *)
  Definition prog_behavior (p : AtkProg) : Behavior := 
    fun store_init step_cnt =>
      let: init_adv := adv_mem_init (construct_view store_init) in
      let: init_store := init_source_maul store_init in
      let: init_cfg := mk_cfg store_init init_adv p in
      let: ((_, ev), lst) := multi_step step_cnt init_cfg in
      ev :: map snd lst.
End semantics.

Module Notations.
  Notation "⟦ p ⟧" := (prog_behavior p).
End Notations.

(* Maybe we keep in mind the number of while iterations.. *)
