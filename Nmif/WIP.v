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

(*  
    If t is a tactic that takes in a hypothesis, 
    this tactic will apply the top hypothesis on it
    The top hypothesis might go away
*)
(* TODO: Can I make this part of ssr => *)
(* TODO: I use ⟨  ⟩ too much *)
Tactic Notation "⟨" tactic(t)  "⟩" := let f := fresh in (move=> f); t f. (* Tactic Notation vs Ltac Notation *)
Tactic Notation "⟨⟨" tactic(t) "⟩⟩" :=
    match goal with
    H : _ |- _ => t H
    end.
Section test.
  Ltac t H := idtac H.
  Goal False -> False.  Proof.  ⟨ t ⟩. Abort.
  Goal False -> False.  Proof.  move=> *; ⟨⟨ t ⟩⟩. Abort.
End test.


Ltac2 assert_goals n :=
  if Int.equal (Control.numgoals ()) n then ()
  else Control.throw (Tactic_failure (Some (Message.of_string "Expected exactly one goal"))).

Ltac assert_single_goal := ltac2:(assert_goals 1).
Goal False. assert_single_goal. Abort.
Goal False /\ False. Fail split; assert_single_goal. Abort.

(* TODO: What naming conventions am I using? *)
Ltac stp_Forall_app_gl :=
  lazymatch goal with |- Forall _ (_ ++ _) => apply/Forall_app end;  assert_single_goal.

Section test.
  Generalizable All Variables.
  Goal `(Forall (A := A) P (l1 ++ l2)).
  Proof.  move=> *; stp_Forall_app_gl.  Abort.
End test.

(* A high good tactic consumes 'low grade' hypotheses (in context), 
  and produces high grade hypotheses *)
Ltac Forall_inv H :=  
    move: H=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _).
(* TODO: Test for these also *)

Ltac evar_spec H :=  
    move: H;
    let t := open_constr:(_) in 
    let f := fresh in 
    pose f := t=> /(_ f); subst f.
(* TODO: Test for these also *)


Import VarValStore.Notations. 

(* Stepping tactics will not take any arguments.  *)
(* TODO:  *)
Ltac stp_corr_wf_gl :=
  lazymatch goal with
  |- context [ ⟨ corruptor ?atk ?ast ?st | is_trusted ⟩] => 
    let t := constr:(⟨ corruptor atk ast st | is_trusted ⟩) in
    have: t = ⟨ st | is_trusted ⟩=> [| ->]; [ 
    move: (corruptor_wf atk);  ⟨ evar_spec ⟩=> - [] + _; intros ->;done|]
  end;
  assert_single_goal.

Section test.
  Context `{!VarPrm,!ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Generalizable All Variables.
  Goal `(forall P, P ⟨ corruptor (AtkStates := A) adv ast st  | is_trusted ⟩).
  Proof. move=> *. stp_corr_wf_gl. Abort.
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
   (*

    Okay, there are the following things to do:
    There must be

    - real store
    - ideal store
    - sim store

    Moreover, there will be invariants.
    ⟨ real_store | is_trusted  ⟩ = ⟨ ideal_store | is_trusted ⟩
    ⟨ real_store | is_public  ⟩ = ⟨ sim_store | is_public ⟩

    Moreover, different from viaduct, we will also have:

    - real continuation
    - ideal continuation
    - sim continuation

    The invariants should be:
    - When the PC is public trusted, all three should be equal
    - When the PC is secret trusted, real = ideal continuation. the sim continuation must be 'I don't know'
    - When the PC is untrusted,  ??. 

    The proof sketch maybe should look like this..

   * When the pc is untrusted, there should not be any changes to the real store
     trusted or ideal store trusted in any substep

   * When the pc is secret, there should not be any changes to the real store public.
    
     trusted or ideal store trusted in any substep


   *)
  (* For now, just assert that you will have P*)
  Record SimExtraStates := {
     (* 
       The simulator keeps in its head the program. Moreover, it does not need
       to keep the attacked program, because it will only keep the subset of
       the real program which will
     *)
      clean_cont : Prog ;
  }.
  Print AtkCmd.

  Check filter is_attacked _.
  Definition s_init : SimExtraStates := {|
     clean_cont := myprog (* This is not the case. *)
  |}.

  Record SimStates := mk_sim_state {real_sim : AtkRealStates ; extra: SimExtraStates}.
  Parameter f : SimStates -> SimExtraStates.
   
  Definition sim_init_substeps ast := init_substeps atkreal ast.
  Definition sim_init_state mem := mk_sim_state (init_state atkreal mem) s_init.

  Obligation Tactic := idtac. (* TODO: Program cases or whatnot *)
  Program Definition atkideal : AdvStateMachine SimStates := {|
      init_state mem := mk_sim_state (init_state atkreal mem) s_init;
      init_substeps st := sim_init_substeps (real_sim st);
      corruptor _ := id; (* TODO: We need to show a stronger property, which we don't.. But which is obvious.. We need to say that simulator only does things at x or y*)
      learner st mem := mk_sim_state (learner atkreal (real_sim st) mem) (f st);
      leaker st := leaker atkreal (real_sim st);
      substeps st := substeps atkreal (real_sim st)
      |}.

  Next Obligation. easy. Qed.
  Next Obligation. 
    move=> [] /= arst ?.
    move: (learner_wf atkreal)=> /(_ arst).
    move: (store_to_view _) (learner _ _)=> > nirl.
    move=> s1 s2; move: nirl=> /(_ s1 s2) /[apply]. 
    rewrite /id=> -> //. 
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
    case: (init_state _ _)=> //. (*  Here, we are doing something  sus*)
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


Ltac stp_destruct_units_gl :=
  match goal with
  |- context [?x : unit] => 
    let t := type of x in 
    assert_fails (is_constructor x);
    convert t unit;
    destruct x
  end;
  assert_single_goal.
Section test.
  Generalizable All Variables.
  Goal `(P (x :> unit)).
  Proof. move=> *; stp_destruct_units_gl. Abort.
End test.

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

(* TODO: Make this better *)
Ltac grind := 
  (
  stp_Forall_app_gl ||
  stp_destruct_units_gl ||
  stp_cnt_dst_gl ||
  stp_dst_atkcmd ||
  stp_corr_wf_gl ||
  stp_ni ||
  apply/ pure_atklst_wt ||
  hnf ||
  split ||
  unfold id in * ||
  ⟨⟨ Forall_inv ⟩⟩ ||
  intros ||
  idtac
  )=> //.


Lemma comb_step_inv: forall c, 
                        CombObjInv c ->
                        CombObjInv (comb_step c).
Proof.
    case; rewrite /CombObjInv=> cnt >  /= [cr treq].
    do !grind=> //=; auto.
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
      all:
        do !(
          case: isatk ||
          rewrite/extract_i/extract_r/comb_step/id/=||
          case: (learner _ _ _) || 
          split || 
          apply: ni ||
          congr (_, (_,_) :: _) ||
          rewrite -{}treq  ||
          stp_corr_wf_gl
          ). (* I need to think of the best way to this. The one downside I might see is destruct. *)
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
