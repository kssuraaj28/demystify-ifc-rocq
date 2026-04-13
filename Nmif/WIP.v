(* Time to cook *)
From Stdlib Require Import ssreflect ssrbool List FunctionalExtensionality.
Import ListNotations.

From Ltac2 Require Import Ltac2.

Require Import Util VarValStore Syntax Semantics Attacker Util Noninterference Tacs. 
Import Util.DecEq Util.List. 


Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.



Import VarValStore.Notations. 

(* Stepping tactics will not take any arguments.  *)
(* TODO:  *)
Ltac stp_corr_wf_gl :=
  lazymatch goal with
  |- context [ ⟨ corruptor ?atk ?ast ?st | is_trusted ⟩] => 
    let t := constr:(⟨ corruptor atk ast st | is_trusted ⟩) in
    have: t = ⟨ st | is_trusted ⟩=> [| ->]; [ 
    move: (corruptor_wf atk);  ⟨ evar_spec ⟩=> - [] + _; intros ->;done|]
  end.

Section test.
  Context `{!VarPrm,!ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Generalizable All Variables.
  Goal `(forall P, P ⟨ corruptor (AtkStates := A) adv ast st  | is_trusted ⟩).
  Proof. move=> *. stp_corr_wf_gl. Abort.
End test.

(* You ideally want to make everything tt  *)
Ltac stp_abstract_units_gl :=
  do !(let f := fresh in 
  set (f := _ :> unit); 
  move: [elaborate f]);
  idtac.
  (*assert_goal 1. The issue is that there needs to be some focusing done. all: things stress this out. TODO: How to fix?*)

Section test.
  Goal `(forall P (x : unit),  P tt x).
  Proof. move=> *.   stp_abstract_units_gl.   Abort.
End test.


Section ts.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  (* Should this be inductive? *)
  Inductive CmdRestriction: Cmd -> Prop :=
    | nitr : forall comp, 
        Noninterfering (store_to_view is_trusted) comp (store_to_view is_trusted) ->
        CmdRestriction (assign comp).

  Definition ProgRestriction: Prog -> Prop :=
    Forall CmdRestriction.

  (* This name is stupid *)
  Definition AtkCmdRestriction '(mk_cstep _ c) : Prop :=
    if c isn't Some c then True else
    CmdRestriction c.

  Definition ContinuationRestriction: Continuation -> Prop :=
    Forall AtkCmdRestriction.

  (* TODO: Maybe show some safety lemma..
    If x sats continuation restruction and takes a step to x', then x' also satisfies that.
    This is true for all states, and whatnot
  *)

  (* 
    I think that constructor is okay to be part of finisher. 
    Don't make it part of forward reasoning
  *)
  Lemma pure_atk_wt : AtkCmdRestriction pure_atk. 
  Proof. constructor. Qed.

  Lemma pure_atklst_wt: forall n, 
    Forall AtkCmdRestriction (nlist  pure_atk n).
  Proof. 
    elim=> /=; auto using pure_atk_wt.
  Qed.

  Lemma restrict_rel: forall p,
    ProgRestriction p -> 
    (forall n, ContinuationRestriction (prog_zip p n)).
  Proof.
    rewrite/ContinuationRestriction/ProgRestriction. 
    elim=> [_ n|]; first (elim: n=> //= >; constructor; easy).
    move=> c l ih; ⟨ Forall_inv ⟩.
    move=> cr t; move: ih=> /(_ t) {t}=> cl n.
    case: n c l cr cl=> [> ? /(_ 0) |]; last constructor=> //. 
    rewrite !prog_zip_noatk /=; auto.
  Qed.

End ts.

Parameter vli : ValPrm. Existing Instance vli.
Parameter vri : VarPrm. Existing Instance vri.
Parameter lvli : AdvLvlPrm. Existing Instance lvli.
Parameter lki : AdvLeakPrm. Existing Instance lki.

Parameter myprog : Prog. Axiom myprog_wt : ProgRestriction myprog.

Definition AtkRealStates := unit.
Parameter atkreal : AdvStateMachine AtkRealStates.
 

Section idealatk.
  Record SimExtraStates := mk_sim_extra {
      sim_cont : list (option Cmd) ; 
  }.
   


  Record SimStates := mk_sim_state {real_sim : AtkRealStates ; extra: SimExtraStates}.


  Definition sim_init_state (inp: StoreView):  SimStates := 
    let: init_realatk := init_state atkreal inp in 
    let: init_realsubstps := init_substeps atkreal init_realatk in 
    let: init_cont := prog_zip myprog init_realsubstps in
    let: init_optprog := map cmd (filter is_attacked init_cont) in 
    mk_sim_state init_realatk (mk_sim_extra init_optprog).

  Definition sim_learner (s : SimStates) (_: Store):  SimStates :=
    let: mk_sim_state real_st (mk_sim_extra cont) := s in 
    let: substeps := substeps atkreal real_st in
    let: real_st' := real_st in (* TODO: This should be fixed eventually *)
    mk_sim_state real_st' (mk_sim_extra ((nlist None substeps) ++ (tl cont))). 

  Obligation Tactic := idtac. (* TODO: Program cases or whatnot *)
  Program Definition atkideal : AdvStateMachine SimStates := {|
      init_state := sim_init_state ;
      learner := sim_learner;

      (* These  things are fixed. Things probably can be refactored better, but I don't care *)

      init_substeps st := init_substeps atkreal (real_sim st);
      corruptor _ := id; (* TODO: We need to show a stronger property, which we don't.. But which is obvious.. We need to say that simulator only does things at x or y*)
      leaker st := leaker atkreal (real_sim st);
      substeps st := substeps atkreal (real_sim st)
      |}.
  

  Next Obligation. easy. Qed.
  Next Obligation. 
    move=> [] /= arst ?.
    move: (learner_wf atkreal)=> /(_ arst).
    move: (store_to_view _) (learner _ _)=> > nirl.
    move=> s1 s2; move: nirl=> /(_ s1 s2) /[apply]. 
    dst_hyp_type SimExtraStates=>//=.
  Qed.
End idealatk.

Import Semantics.Notations.
Definition b1 := ⟦ myprog ☠︎︎ atkreal ⟧.
Definition b2 := ⟦ myprog ☠︎︎ atkideal ⟧.

Notation CfgR := (Cfg AtkRealStates).
Notation CfgI := (Cfg SimStates).

Record CombObj := {
     cont : Continuation; (* A single continuation is shared between everything *)
     real_st : Store; (* Store for the real system *)
     ideal_st : Store; (* Store for the ideal system *)
     sim_extra: SimExtraStates;
     trace: ObservationTrace; (* Trace for everything *)
    }. 

Definition CombObjInv (c : CombObj): Prop :=
     ContinuationRestriction (cont c) /\
     ⟨ real_st c | is_trusted ⟩ = ⟨ ideal_st c | is_trusted ⟩.

Definition extract_r (comb : CombObj): CfgR :=
    (cont comb, real_st comb, tt , trace comb).

Definition extract_i (comb : CombObj): CfgI :=
    (cont comb, ideal_st comb, mk_sim_state tt (sim_extra comb), trace comb).
(* Make a list of things which are happening *)

Definition comb_init (s_init : Store):  CombObj :=
    (* TODO: There should be attacker state also, which we'll do later  *)
    let: (cont, st, (mk_sim_state _ sim_extra), init_tr) := initial_cfg myprog atkideal s_init in 
    {|
     cont := cont ;
     real_st := st ;
     ideal_st := st ;
     sim_extra := sim_extra ;
     trace := init_tr 
    |}.

Lemma comb_init_inv: forall s, CombObjInv (comb_init s).
Proof.
    rewrite/comb_init/initial_cfg/CombObjInv/=.
    auto using restrict_rel, myprog_wt.
Qed.

Lemma comb_init_extraction: forall s,
    extract_r (comb_init s) = initial_cfg myprog atkreal s /\
    extract_i (comb_init s) = initial_cfg myprog atkideal s.
Proof.
    move=> ?; rewrite /initial_cfg/extract_r/extract_i /=. 
    case: (init_state _ _)=> //. 
    split=> //. do ! congr (_,_).
    rewrite/sim_init_state.
    stp_abstract_units_gl; do 2 case.
    congr mk_sim_state.
    (*  Here, we are doing something  sus*)
Qed.

Definition comb_step (c: CombObj): CombObj :=
    let: 
        {| cont := cont; 
           real_st := real_st; 
           ideal_st := ideal_st; 
           sim_extra := sim_extra ; 
           trace := trace |} := c
    in
    let: (cont', real_st', ideal_st', sim_extra', leak') :=
      (* If the program is empty *)
      if cont isn't (cmd :: cont') then ([], real_st, ideal_st, sim_extra, None) else 

      (* If the program is not empty *)
      let: (real_st', _, _, _) := atk_cmd_step atkreal cmd real_st tt in
      let: (ideal_st', mk_sim_state _ sim_extra', extra_cont', leak') := 
        atk_cmd_step atkideal cmd ideal_st (mk_sim_state tt sim_extra) 
      in


      (extra_cont' ++ cont', real_st', ideal_st', sim_extra', leak')
    in
    {| cont := cont'; 
       real_st := real_st'; 
       ideal_st := ideal_st'; 
       sim_extra := sim_extra'; 
       trace := (⟨real_st'| is_trusted⟩, leak') :: trace |}.



(* TODO: This seems like a very very inefficient way to do this*)
Ltac stp_cnt_dst_gl :=
        match goal with
        |- context [match ?cnt with [] => _ | _ => _ end] => 
        let t := type of cnt in 
        unify t Continuation; (* I don't get this unify, etc. *)
        destruct cnt
        end.

Ltac stp_dst_atkcmd :=
    lazymatch goal with
    [ H : AtkCmdRestriction ?a |- _ ] => 
      let isatk := fresh in let cmd := fresh in 
      is_var a; destruct a as [isatk cmd];
      destruct isatk; destruct cmd;
      destruct H
    end.

Ltac stp_ni :=
    lazymatch goal with
    H : Noninterfering (store_to_view ?p) ?comp (store_to_view ?p) |-⟨ ?comp _ | is_trusted ⟩ =⟨ ?comp _ | is_trusted ⟩ => apply:H
    end.

(* TODO: Need to think about the right way to structure proofs and so on 
finisher backtracking proofs?
*)

(* TODO: Make this better. 
This should ideally take a tactic

*)


Ltac grind_step engine finisher := engine; try finisher.

Ltac grind engine finisher :=  do ! [grind_step engine finisher].
    
Ltac engine := 
  (
  stp_Forall_app_gl ||
  stp_cnt_dst_gl ||
  stp_dst_atkcmd ||
  stp_corr_wf_gl ||
  stp_ni ||
  apply/ pure_atklst_wt ||
  hnf ||
  split ||
  unfold id in * ||
  ⟨⟨ Forall_inv ⟩⟩ ||
  congr (_, _) ||
  congr (_::_) ||
  intros ||
  idtac
  ).

Ltac finisher := do ! progress(simpl; auto). (* (simpl + auto + done); fail does not work. Why? *)

Ltac mygrind := grind engine finisher.


Lemma comb_step_inv: forall c, 
                        CombObjInv c ->
                        CombObjInv (comb_step c).
Proof.
    case; rewrite /CombObjInv=> cnt >  /= [cr treq].
    mygrind.
    all: (dst_hyp_type SimExtraStates).
    all: (mygrind).
Qed.



Section thm.
  Lemma comb_step_valid : forall c , 
      CombObjInv c ->
      extract_i (comb_step c) = step atkideal (extract_i c) /\
      extract_r (comb_step c) = step atkreal (extract_r c). 
  Proof.
      case=> c ? ? ? ?; case :c=> [[_ -]| [isatk cmd] ? [wt treq]]; first 
          rewrite/CombObjInv/extract_i/extract_r/==> - -> //.
      rewrite/CombObjInv/= in wt treq.
      move: wt; ⟨ Forall_inv ⟩=> wtc ?.
      (* I'm so bad. Need  more automation !! *)
      case: cmd wtc=> [|_]; [rewrite/AtkCmdRestriction=> ? [? ni]|].  (* I think that CPDT style automation might be useful here *)
      all: dst_hyp_type bool.
      all: mygrind.
      all:
        do !(
          case: isatk ||
          rewrite/extract_i/extract_r/comb_step/id/=||
          (dst_hyp_type SimExtraStates) ||
          case: (learner _ _ _) || 
          idtac
          ). (* I need to think of the best way to this. The one downside I might see is destruct. *)
      all: mygrind.
  Qed.
End thm.

Theorem comb_extract: 
    forall c, extract_trace (extract_i c) = extract_trace (extract_r c). 
Proof. case=> //. Qed.



Goal b1 = b2. 
Proof.
    rewrite/b1/b2/⟦ _ ☠︎︎  _⟧.
    apply/functional_extensionality=> s; apply/functional_extensionality=> n.
    set msr:= (multistep _ _ _); set msi := (multistep _ _ _).
    suff: exists c, CombObjInv c /\ msr = extract_r c  /\ msi = extract_i c;
      first (move=> [? [_ [-> ->]]]; rewrite comb_extract //).
    rewrite{}/msr{}/msi.

    elim: n=> [|> [c [cinv [e1 e2]]]].
    - exists (comb_init s) => /=.
      split; first apply/comb_init_inv.    
      move:(comb_init_extraction)=> /(_ s).
      intuition.

    - exists (comb_step c)=> /=. 
      split; first apply/comb_step_inv=> //.
      move: (comb_step_valid c cinv) e1 e2 => [-> ->] -> -> //.
Qed.
