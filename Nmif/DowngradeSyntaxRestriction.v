From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds ControlledDowngrade.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem IdlAtkPreds ControlledDowngrade.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section prog_restr.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Variable noend nodecl: bool.

  Notation prg_dwngrd_rstrct' cmd_fn := (forallb cmd_fn) (only parsing). 
  Fixpoint cmd_dwngrd_rstrctd (c : Cmd) : bool :=
    match c with
    | cond _ b1 b2 => 
        prg_dwngrd_rstrct' cmd_dwngrd_rstrctd b1 &&  prg_dwngrd_rstrct' cmd_dwngrd_rstrctd b2

    | while _ b => 
        prg_dwngrd_rstrct' cmd_dwngrd_rstrctd b

    | assign a => 
      let: end_chk := match noend, (extract_controlled_endorse c) with true, Some _  => false | _ , _ => true  end in
      let: decl_chk :=  match nodecl, (extract_controlled_declassify c) with  true, Some _ => false | _, _ => true  end in
      end_chk && decl_chk 
    | _ => true
    end.
  Definition prg_dwngrd_rstrct := prg_dwngrd_rstrct' cmd_dwngrd_rstrctd : Prog -> bool.
End prog_restr.

Section sugar.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Definition nonni_endorse_absent := prg_dwngrd_rstrct true false.
  Definition nonni_declassify_absent := prg_dwngrd_rstrct false true.
  Definition downgrade_absent := prg_dwngrd_rstrct true true.
End sugar.


Section thm.
  Import Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Variables noend nodecl : bool.
  Notation cmd_dwngrd_rstrctd := (cmd_dwngrd_rstrctd noend nodecl).
  Notation prg_dwngrd_rstrct := (prg_dwngrd_rstrct noend nodecl).

  Definition dwnrd_rstrct_lift {T} (c : Cfg (AtkStates := T)) : bool :=
    let (l, _) := c in 
    forallb (fun '(mk_atkcmd _ ocmd) => oapp cmd_dwngrd_rstrctd true ocmd) l.

  Notation CfgListRestr := (CfgListRestr noend nodecl).

  Lemma dwnrd_rstrct_sound p : 
    prg_dwngrd_rstrct p ->
    forall adv inp cfg,
      reachable (step (Attacker.step adv)) (init_cfg p (init adv) inp) cfg ->
      CfgListRestr cfg.
  Proof.
    move=> wtp ? ? cfg rch.
    suff: dwnrd_rstrct_lift cfg.
      { clear.
      rewrite/dwnrd_rstrct_lift/CfgListRestr.
      case cfg=> + _=> [] [] // cmd > /= /andP [] + _.
      case: cmd=> _ [] //=.
      rewrite/CmdRestr/cmd_dwngrd_rstrctd=> c.
      case: c=> [ /= _  | ? |/= _ |/= _ ]; Util.local_cook.
      move: (extract_controlled_endorse _) (extract_controlled_declassify _) noend nodecl.
      move=> [[_ _]|] [[_ _]|] [] [] //. }
    apply: (reachable_invariant _ _ dwnrd_rstrct_lift); [.. |exact: rch]=> {rch}. (* TODO: Why I have to do this dwnrd_rstrct_lift *)
      { move: wtp; clear.
      rewrite/prg_dwngrd_rstrct/dwnrd_rstrct_lift/init_cfg.
      rewrite/is_true !forallb_forall -!Forall_forall Forall_map.
      exact: Forall_impl. }
    clear=> - [] [] // acmd ? [] > /= /andP [].
    rewrite/dwnrd_rstrct_lift.
    move acmdstp: (acmd_step _ _ _)=> [[? ?] ?].
    rewrite/is_true !forallb_forall -!Forall_forall Forall_app.
    move=> rst x; split=> // {x}.
    rewrite Forall_map.
    apply: Forall_combine2_ind1; [case=> /= ? ?; apply| ..]=> //.
    rewrite Forall_map /=.
    case: acmd rst acmdstp=> isatk [] /=; cycle 1.
      { case: isatk=> _ [] <- _ //. } 
    move=> cmd rst [] <- _ _.
    move: cmd rst. rewrite/clean_cmd_stp_cnt. move: (eval_bool_exp _); clear=> ?.
    case=> //=> > => [/andP []|]; rewrite !/is_true !forallb_forall -!Forall_forall.
    1,2: case: (X in if X then _ else _)=> //.
    rewrite Forall_app=> + /ltac:(split) //.
    rewrite !Forall_forall -!forallb_forall /==> -> //.
  Qed.

End thm.

