From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.


Section asgn_lbls.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Definition asgn_dst_lbl (a : Assignment) : Label :=
    var_lbl (match a with
             | endorse _ dst => dst
             | declassify _ dst => dst
             | exp_assign _ dst => dst
             end).

  Definition asgn_src_lbl (a : Assignment) : Label :=
    match a with
    | endorse src _ => var_lbl src
    | declassify src _ => var_lbl src
    | exp_assign (s1, s2, _) _ => var_lbl s1 ⊔ var_lbl s2
    end.
End asgn_lbls.

#[local] Notation PcLbl := Lattice4pt.Label.
Section sa.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Import Lattice4pt.Notations.
  (* TODO: 
  is_ni_assign
  *)

  (* TODO: How would a parameterized thing look like, as opposed to indexed? *)
  (* WellTyped? *)
  Notation WellFormedProg' WellFormedCmd pclbl prog :=  (Forall (WellFormedCmd pclbl) prog) (only parsing).
  Unset Elimination Schemes.
  Inductive WellFormedCmd : PcLbl -> Cmd -> Prop := 
  | wf_output:
     forall v pclbl, 
       pclbl ⊑ var_lbl v ->
       (* TODO: I think that it suffices to just have a trusted check. TODO! *)
       _ pclbl (output v)

  | wf_endorse:
     forall from to,
       var_lbl from = pulbl -> var_lbl to = ptlbl -> (* Maybe just trusted *)
       _ ptlbl (assign (endorse from to))

  | wf_declassify:
     forall from to,
       var_lbl from = stlbl -> var_lbl to = ptlbl -> (* Maybe just public *)
       _ ptlbl (assign (declassify from to))

  | wf_assign:
     forall a pclbl,
       asgn_src_lbl a ⊑ asgn_dst_lbl a ->
       pclbl ⊑ asgn_dst_lbl a ->
       _ pclbl (assign a)

  | wf_cond: 
     forall gvar comp pclbl b1 b2, 
       let: gvarlbl := var_lbl gvar in
       let: newpc := gvarlbl ⊔ pclbl in
       WellFormedProg' WellFormedCmd newpc b1 -> (* TODO: How might things look without ⊔ *)
       WellFormedProg' WellFormedCmd newpc b2 ->
       _ pclbl (cond (gvar,comp) b1 b2)

  | wf_while: 
     forall gvar comp pclbl wbody,
       let: gvarlbl := var_lbl gvar in
       let: newpc := gvarlbl ⊔ pclbl in
       WellFormedProg' WellFormedCmd newpc wbody ->
       _ pclbl (while (gvar,comp) wbody).

  Set Elimination Schemes.
  
  Definition WellFormedProg pclbl prog := WellFormedProg' WellFormedCmd pclbl prog.

  Section ind.
    Variable P : PcLbl -> Cmd -> Prop.

    (* 
       However, do we even need induction? Maybe we don't need it at all.. 
       So, can we do something weaker than inductively defining this then?
    *)

    Hypothesis hyp_output :
        forall pclbl v,
          pclbl ⊑ var_lbl v ->
          P pclbl (output v).

    Hypothesis hyp_endorse :
        forall from to,
          var_lbl from = pulbl -> var_lbl to = ptlbl ->
          P ptlbl (assign (endorse from to)).

    Hypothesis hyp_declassify :
        forall from to,
          var_lbl from = stlbl -> var_lbl to = ptlbl ->
          P ptlbl (assign (declassify from to)).

    Hypothesis hyp_assign :
        forall a pclbl,
          asgn_src_lbl a ⊑ asgn_dst_lbl a ->
          pclbl ⊑ asgn_dst_lbl a ->
          P pclbl (assign a).

    (* I have no idea whether this is the right thing *)
    Hypothesis hyp_cond : 
        forall gvar comp pclbl b1 b2,
         let: gvarlbl := var_lbl gvar in
         let: newpc := gvarlbl ⊔ pclbl in
         Forall (WellFormedCmd newpc) b1 -> Forall (P newpc) b1 ->
         Forall (WellFormedCmd newpc) b2 -> Forall (P newpc) b2 ->
         P pclbl (cond (gvar, comp) b1 b2).

    Hypothesis hyp_while : 
        forall gvar comp pclbl wbody,
         let: gvarlbl := var_lbl gvar in
         let: newpc := gvarlbl ⊔ pclbl in
         Forall (WellFormedCmd newpc) wbody -> Forall (P newpc) wbody ->
         P pclbl (while (gvar, comp) wbody).

    Fixpoint WellFormedCmd_ind :
      forall p c, WellFormedCmd p c -> P p c. 
    Proof.
      move=> > [] *; 
      [apply: hyp_output|apply:hyp_endorse|apply:hyp_declassify|apply:hyp_assign|..]=> * //.
      1-2: (apply: hyp_cond; clear hyp_cond) || (apply: hyp_while; clear hyp_while)=>//.
      1-3: lazymatch goal with
             H: Forall _ ?b |- Forall _ ?b => elim: H=> // *
            end.
      1-3: constructor; auto; fail.
    Qed.
  End ind.
  Definition WellFormedOptCmd (pc: PcLbl) (ocmd : option Cmd): Prop :=
    if ocmd isn't Some cmd then True else WellFormedCmd pc cmd.

  Fact WellFormedOptCmd_Some pc c :
    ltac2:(cbn_eq (WellFormedOptCmd pc (Some c))).
  Proof. done. Qed.
End sa.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> WellFormedOptCmd_Some) "WellFormedOptCmd_Some" old.

Section test.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac cook := ltac2:(cook (keep_only this_cookbook_ ["WellFormedOptCmd_Some"])).
  Goal forall pc c (P : _ -> Prop), P (WellFormedOptCmd pc (Some c)).
  Proof. move=> *. cook. Abort.
End test.

Notation "pc ⊢ ocmd" := (WellFormedOptCmd pc ocmd) (at level 20).


Section new_pc.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Definition compute_new_pc (old_pc : PcLbl) (cmd: Cmd): PcLbl :=
    match cmd with
    | cond (gvar,_) _ _ => var_lbl gvar ⊔ old_pc (* Can this be refactored w/ static analysis? *)
    | while (gvar,_) _ => var_lbl gvar ⊔ old_pc
    | _ => old_pc
    end.

  Definition compute_new_pc_opt (old_pc : PcLbl) (cmd: option Cmd): PcLbl :=
    if cmd isn't Some cmd then old_pc else
    compute_new_pc old_pc cmd.

  Fact compute_new_pc_assign pc a : ltac2:(cbn_eq (compute_new_pc pc (assign a))).
  Proof. done. Qed.

  Fact compute_new_pc_opt_some pc cmd :
    ltac2:(cbn_eq (compute_new_pc_opt pc (Some cmd))).
  Proof. done. Qed.

  Lemma compute_new_pc_secret untr c :
    public (compute_new_pc (mk_lbl untr false) c) = false.
  Proof. case: c=> // - []  *; rewrite pub_join //.  Qed.

  Fact compute_new_pc_opt_secret untr c :
    public (compute_new_pc_opt (mk_lbl untr false) c) = false.
  Proof.
    rewrite /compute_new_pc_opt.
    case: c => [c | ] //.
    rewrite compute_new_pc_secret //.
  Qed.
End new_pc.

Ltac2 Set this_cookbook_ as old :=  add_cookstep ltac1:(rewrite -> compute_new_pc_opt_some) "compute_new_pc_opt_some" old.
Ltac2 Set this_cookbook_ as old :=  add_cookstep ltac1:(rewrite -> compute_new_pc_opt_secret) "compute_new_pc_opt_secret" old.
Ltac2 Set this_cookbook_ as old :=  add_cookstep ltac1:(rewrite -> compute_new_pc_assign) "compute_new_pc_assign" old.

Section test.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac cook := ltac2:(cook (keep_only this_cookbook_ ["compute_new_pc_opt_some"])).
  Goal forall pc c (P: _ -> Prop), P (compute_new_pc_opt pc (Some c)). 
  Proof. move=> *. cook. Abort.
End test.

Section test.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac cook := ltac2:(cook (keep_only this_cookbook_ ["compute_new_pc_opt_secret"])).
  Goal forall untr c (P: _ -> Prop), P (public (compute_new_pc_opt (mk_lbl untr false) c)).
  Proof. move=> *. cook. Abort.
End test.

Section flow_to_subtype.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Lemma flows_to_subtype_cmd c l1 l2:
      l2 ⊑ l1 -> (* TODO: I don't know whether this is true *)
      WellFormedCmd l1 c ->
      WellFormedCmd l2 c.
  Proof. 
    (* TODO: What does elim do? Is it just apply? *)  
    move: l2=> ++ h. elim: h=> *; try (constructor; eauto using flows_to_trans; fail).
    1-2: revert_hyp_pat  (is_true (_ ⊑ _))=> /flows_to_pt ->; constructor; assumption.
    1-2: constructor; (apply/Forall_impl;[ |eassumption])=> /= >; auto using join_mono_r.
  Qed.

  Lemma flows_to_subtype_prog :
    forall p l1 l2,
      l2 ⊑ l1 -> (* TODO: I don't know whether this is true *)
      WellFormedProg l1 p ->
      WellFormedProg l2 p.
  Proof. 
    rewrite/WellFormedProg=> *.
    apply/Forall_impl;[|eassumption].
    eauto using flows_to_subtype_cmd.
  Qed.
End flow_to_subtype.

Section downgrading.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Lemma wf_endorse_pc pc from to:
    var_lbl from = pulbl ->
    var_lbl to = ptlbl ->
    WellFormedCmd pc (assign (endorse from to)) ->
    pc = ptlbl.
  Proof.
    move=> efrom eto.
    move t1: (assign (_))=> ? t2; move: t2 t1=> [] // > + + /ltac:(dotop [idtac]).
    case=> <- /=. rewrite/asgn_dst_lbl {}efrom {}eto=> _.
    exact: flows_to_pt.
  Qed.

  Lemma wf_declassify_pc pc from to:
    var_lbl from = stlbl ->
    var_lbl to = ptlbl ->
    WellFormedCmd pc (assign (declassify from to)) ->
    pc = ptlbl.
  Proof.
    move=> efrom eto.
    move t1: (assign (_))=> ? t2; move: t2 t1=> [] // > + + /ltac:(dotop [idtac]).
    case=> <- /=. rewrite/asgn_dst_lbl {}efrom {}eto=> _.
    exact: flows_to_pt.
  Qed.
End downgrading.

Section untrusted_dst.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Lemma wf_untr_cmd_dst_untr p c a:
    WellFormedCmd (mk_lbl true p) c -> c = assign a ->
    untrusted (var_lbl (get_assign_dest a)).
  Proof. 
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap].
    case=> // > + + e1 e2. rewrite -{}e1. case: e2=> -> ?.
    move:(flows_from_untr)=> /[apply] /=.
    evar_spec_toph=> //.
  Qed.
End untrusted_dst.

Section output.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Lemma wf_output_inv l v: 
    WellFormedCmd l (output v) ->
    l ⊑ (var_lbl v).
  Proof.
    move e: (output v)=> ?; move: e=> /[swap]. 
    case=> // > /[swap] - [->] //.
  Qed.
End output.

Section step_soundness.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Lemma compute_new_pc_untr p c:
    exists p',
      compute_new_pc (mk_lbl true p) c = (mk_lbl true p').
  Proof.
  case: c; eauto; cbn; case=> *.
    1-2: case: (var_lbl _) => u pg. (* TODO: This could be a lemma *)
    1-2: exists (pg && p); case: u; done.
  Qed.

 Fact untr_compute_new_pc p c:
   untrusted (compute_new_pc (mk_lbl true p) c).
 Proof.
   case: c=> //=; case=> * ; rewrite untr_join //.
 Qed.

  Lemma step_soundness c pc:
      WellFormedCmd pc c ->
      forall st,
        WellFormedProg (compute_new_pc pc c) (clean_cmd_stp_cnt c st).
  Proof. 
    case=> //= * //.
    1-2: move=> * //=; move: (X in if X then _ else _)=> ?; if_easy_goals.
    apply/Forall_app. split=> //.
    constructor 2=> //.
    apply/wf_while /Forall_impl; [| eassumption]; clear=> *.
    rewrite -join_assoc join_idem=> //.
  Qed.

  Lemma step_soundness_pubuntr:
    forall c st,
      WellFormedCmd (mk_lbl true true) c ->
      WellFormedProg (mk_lbl true true) (clean_cmd_stp_cnt c st).
  Proof.
    rewrite/WellFormedProg=> >;  move l: (mk_lbl _ _)=> ?; move: l=> /[swap].
    case=> //= >; rewrite  -!/(WellFormedProg _ _)=>>.
    1: move=> ++ e; rewrite -{}e => *.
    2: move=> + e; rewrite -{}e => *.
    1-2: case: (X in if X then _ else _) => //. (* all is antipattern *)
    3: apply/Forall_app; split;[|repeat constructor=>//];
        rewrite -/(WellFormedProg _ _).
    1-3: apply/flows_to_subtype_prog;[|eassumption].
    1-3: case: (var_lbl)=> [[] []]=> //. (* TODO: This should be lemma *)
  Qed.
End step_soundness.


(* TODO: rewrite -> vs rewrite  *)
Ltac2 Set this_cookbook_ as old :=  add_cookstep  ltac1:(rewrite -> untr_compute_new_pc) "untr_compute_new_pc" old.

Section test.
  Import Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Ltac cook := ltac2:(cook (keep_only this_cookbook_ ["untr_compute_new_pc"])).
  Goal forall p c (P : _ -> Prop), P (untrusted (compute_new_pc (mk_lbl true p) c)).
  Proof. move=> *. cook. Abort.
End test.


Ltac2 this_cookbook () := this_cookbook_ ().
