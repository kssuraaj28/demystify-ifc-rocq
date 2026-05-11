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

(* TODO: Maybe elsewere *)
Definition PcLbl := Lattice4pt.Label.

Section sa.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.
  Import Lattice4pt.Notations.

  Notation WellFormedProg' WellFormedCmd pclbl prog :=
    (Forall (WellFormedCmd pclbl) prog) (only parsing).

  (* TODO: How would a parameterized thing look like, as opposed to indexed? *)
  (* WellTyped? *)
  Unset Elimination Schemes.
  Inductive WellFormedCmd : PcLbl -> Cmd -> Prop := 
  | wf_assign: 
     forall dst src1 src2 comp pclbl, 
       let: dstlbl := var_lbl dst in
       let: s1lbl := var_lbl src1 in
       let: s2lbl := var_lbl src2 in
       s1lbl ⊑ dstlbl -> s2lbl ⊑ dstlbl -> pclbl ⊑ dstlbl -> (* Using ssrbool coercion *)
       _ pclbl (assign dst (src1, src2, comp))

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
    (* This is the right IH, I think because I made another toy example without nested inductive types *)
    (* 
       However, do we even need induction? Maybe we don't need it at all.. 
       So, can we do something weaker than inductively defining this then?
    *)

    Hypothesis hyp_assign : 
        forall dst src1 src2  comp pclbl,
          let: dstlbl := var_lbl dst in
          let: s1lbl := var_lbl src1 in
          let: s2lbl := var_lbl src2 in
          s1lbl ⊑ dstlbl -> s2lbl ⊑ dstlbl -> pclbl ⊑ dstlbl ->
          P pclbl (assign dst (src1, src2, comp)).

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
      move=> > []; [apply:hyp_assign|..]=> *.
      1-2: (apply: hyp_cond; clear hyp_cond) || (apply: hyp_while; clear hyp_while)=>//.
      1-3: lazymatch goal with
             H: Forall _ ?b |- Forall _ ?b => elim: H=> // *
            end.
      1-3: constructor 2=> //; auto.
    Qed.
  End ind.
  Definition WellFormedOptCmd (pc: PcLbl) (ocmd : option Cmd): Prop :=
    if ocmd isn't Some cmd then True else WellFormedCmd pc cmd.

End sa.
Notation "pc ⊢ ocmd" := (WellFormedOptCmd pc ocmd) (at level 20).

Section thms.
  Import VarValStore.Notations Lattice4pt.Notations.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.


  Lemma flows_to_subtype_cmd c l1 l2:
      l2 ⊑ l1 -> (* TODO: I don't know whether this is true *)
      WellFormedCmd l1 c ->
      WellFormedCmd l2 c.
  Proof. 
    (* TODO: What does elim do? Is it just apply? *)  
    move: l2=> ++ h; elim: h=> *; [constructor=> //; eauto using flows_to_trans|..].
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

  Lemma wt_cmd_st_conf c l st1 st2:
      WellFormedCmd l c ->
      ⟨ st1 | is_public ⟩ = ⟨ st2 | is_public ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_public ⟩ = ⟨ clean_cmd_stp_store c st2 | is_public ⟩.
  Proof. 
    move=> [] // d s1 s2 ? ?. 
    case de: ([elaborate is_public d])=> fs1d fs2d _ pubeq /=; [| rewrite !update_storeview_nochange //].
    move: (flows_to_pub _ _ de fs1d)=> {fs1d} ps1. (* TODO: Tactic *)
    move: (flows_to_pub _ _ de fs2d)=> {fs2d} ps2.
    set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
    set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
    suff: v1 = v2; [move=> ->; apply/update_same_varval=> //|subst v1 v2].
    f_equal; eauto using storeview_eq. 
  Qed.

  (* In a secret context, the public view is constant *)
  Lemma wt_cmd_st_conf_sec:
    forall c i st, 
      WellFormedCmd (mk_lbl i false) c ->
      ⟨ clean_cmd_stp_store c st | is_public ⟩ =
      ⟨ st | is_public ⟩.
  Proof. 
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap]. 
    case=> //= > +++e; rewrite -{}e=> _ _ flw.
    rewrite update_storeview_nochange=> //.
    rewrite/is_public. 
    apply/negbTE/flows_from_sec; rewrite/secret; eauto; done.
  Qed.

  Lemma wt_cmd_st_int c l st1 st2: 
      WellFormedCmd l c ->
      ⟨ st1 | is_trusted ⟩ = ⟨ st2 | is_trusted ⟩ ->
      ⟨ clean_cmd_stp_store c st1 | is_trusted ⟩ = ⟨ clean_cmd_stp_store c st2 | is_trusted ⟩.
  Proof.  
    move=> [] // d s1 s2 ? ?. 
    case de: ([elaborate is_untrusted d])=> fs1d fs2d _ treq /=;
      [do 2 (rewrite update_storeview_nochange{1}/is_trusted; [rewrite de //|])=> //|].  
    rewrite/is_trusted/is_untrusted/= in de.
    move: de=>/untrusted_false td. (* TODO: Automation *)
    move: (flows_to_tr _ _ td fs1d)=> {fs1d} ts1. (* TODO: Tactic *)
    move: (flows_to_tr _ _ td fs2d)=> {fs2d} ts2.
    set v1 := (X in ⟨update_to_store _ _ X | _ ⟩ = _ ).
    set v2 := (X in _ = ⟨update_to_store _ _ X | _ ⟩).
    suff: v1 = v2; [move=> ->; apply/update_same_varval=> //|subst v1 v2].
    f_equal; eauto using storeview_eq.
  Qed.

  Lemma wt_cmd_st_int_untr:
    forall p c st, 
    WellFormedCmd (mk_lbl true p) c ->
    ⟨ clean_cmd_stp_store c st | is_trusted ⟩ =
    ⟨ st | is_trusted ⟩.
  Proof. 
    move=> >; move e: (mk_lbl _ _)=> ?; move:e=> /[swap]. 
    case=> //= > +++e; rewrite -{}e=> _ _ flw.
    rewrite update_storeview_nochange=> //.
    rewrite/is_trusted/is_untrusted negbF //.
    apply/flows_from_untr; eauto; done.
  Qed.

  Lemma pubuntr_wf_cont: 
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
End thms.

Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1
    ltac1:(unshelve erewrite wt_cmd_st_int_untr;[..|eassumption])
    "wt_cmd_st_int_untr" old.

Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1
    ltac1:(unshelve erewrite wt_cmd_st_conf_sec;[..|eassumption])
    "wt_cmd_st_conf_sec" old.

Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1
    ltac1:(apply/wt_cmd_st_int; [eassumption|])
    "wt_cmd_st_int" old.

Ltac2 Set this_cookbook_ as old :=
  add_stirstep 1
    ltac1:(apply/wt_cmd_st_conf; [eassumption|])
    "wt_cmd_st_conf" old.

Ltac2 this_cookbook () := this_cookbook_ ().
