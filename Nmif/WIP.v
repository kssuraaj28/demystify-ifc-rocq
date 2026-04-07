(* Time to cook *)
From Stdlib Require Import ssreflect ssrbool List FunctionalExtensionality.
Import ListNotations.


(* This may be useful *)
From QuickChick Require Import Decidability.

Require Import Util VarValStore Syntax Semantics Attacker Util Noninterference Tacs. 
Import Util.Dec Util.List. 

(* An *_ssr tactic follows the ssr philosophy*)
Ltac Forall_inv_ssr :=  move=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _).

Ltac evar_spec_ssr :=  
    let t := open_constr:(_) in 
    let f := fresh in 
    pose f := t=> /(_ f); subst f.

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
  Proof. by constructor. Qed.

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
    elim=> [_ n|]; first by elim: n=> //= >; constructor; easy.
    move=> c l ih /ltac:(Forall_inv_ssr).
    move=> cr t; move: ih=> /(_ t) {t}=> cl n.
    case: n c l cr cl=> [> ? /(_ 0) |]; last by constructor. (* Can I make 0 an evar? *)
    by rewrite !prog_zip_noatk /=; auto.
  Qed.

End ts.

Parameter vli : ValPrm. Existing Instance vli.
Parameter vri : VarPrm. Existing Instance vri.
Parameter lvli : AdvLvlPrm. Existing Instance lvli.
Parameter lki : AdvLeakPrm. Existing Instance lki.


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
  Parameter SimExtraStates : Type.
  Parameter s_init : SimExtraStates.
  Record SimStates := mk_sim_state {real_sim : AtkRealStates ; extra: SimExtraStates}.
  Parameter f : SimStates -> SimExtraStates.
  (* TODO: Add more things here 
      Maybe add a counter? 
      Maybe add the program configuration? + Store? We can
      just add some whole store, 
      but maintain the invariant that 
  *)

  Obligation Tactic := idtac. (* TODO: Program cases or whatnot *)
  Program Definition atkideal : AdvStateMachine SimStates := {|
      init_state mem := mk_sim_state (init_state atkreal mem) s_init;
      init_substeps st := init_substeps atkreal (real_sim st);
      corruptor _ := id; (* TODO: We need to show a stronger property, which we don't.. But which is obvious.. We need to say that simulator only does things at x or y*)
      learner st mem := mk_sim_state (learner atkreal (real_sim st) mem) (f st);
      leaker st := leaker atkreal (real_sim st);
      substeps st := substeps atkreal (real_sim st)
      |}.

  Next Obligation. by easy. Qed.
  Next Obligation. 
    move=> [] /= arst ?.
    move: (learner_wf atkreal)=> /(_ arst).
    move: (store_to_view _) (learner _ _)=> > nirl.
    move=> s1 s2; move: nirl=> /(_ s1 s2) /[apply]. 
    by rewrite /id=> ->. 
  Qed.
End idealatk.

Import Semantics.Notations.
Parameter myprog : Prog. Axiom myprog_wt : ProgRestriction myprog.
Definition b1 := ⟦ myprog ☠︎︎ atkreal ⟧.
Definition b2 := ⟦ myprog ☠︎︎ atkideal ⟧.

Notation CfgR := (Cfg AtkRealStates).
Notation CfgI := (Cfg SimStates).

Import VarValStore.Notations. 
Record CombObj := {
     cont : Continuation; (* A single continuation is shared between everything *)
     real_st : Store; (* Store for the real system *)
     ideal_st : Store; (* Store for the ideal system *)
     sim_extra: SimExtraStates;
     trace: ObservationTrace; (* Trace for everything *)
     cont_wf : ContinuationRestriction cont;
     tr_match : ⟨ real_st | is_trusted ⟩ = ⟨ ideal_st | is_trusted ⟩
    }. 

Definition extract_r (comb : CombObj): CfgR :=
    (cont comb, real_st comb, tt , trace comb).

Definition extract_i (comb : CombObj): CfgI :=
    (cont comb, ideal_st comb, mk_sim_state tt (sim_extra comb), trace comb).

(*
Cfg =
fun (H : VarPrm) (H0 : ValPrm) (H2 : AdvLeakPrm) (AtkStates : Type) =>
(Continuation * Store * AtkStates * ObservationTrace)%type
     : VarPrm -> ValPrm -> AdvLeakPrm -> Type -> Type

Arguments Cfg {H H0 H2} AtkStates%type_scope
*)
(* TODO: Take more things as input? *)
Section def.
    Obligation Tactic := try done. (* TODO: Program cases or whatnot *)
    Program Definition comb_init (s_init : Store):  CombObj :=
        (* TODO: There should be attacker state also, which we'll do later  *)
        let: (cont, st, (mk_sim_state _ sim_extra), init_tr) := initial_cfg myprog atkideal s_init in 
        {|
         cont := cont ;
         real_st := st ;
         ideal_st := st ;
         sim_extra := sim_extra ;
         trace := init_tr 
        |}.
    Next Obligation.
      move=> /= > [] -> *; clear.
      by auto using restrict_rel, myprog_wt.
    Qed.
End def.

Lemma comb_init_valid: forall s,
    extract_r (comb_init s) = initial_cfg myprog atkreal s /\
    extract_i (comb_init s) = initial_cfg myprog atkideal s.
Proof.
    move=> ?; rewrite /initial_cfg/extract_r/extract_i /=. 
    by case: (init_state _ _). (*  Here, we are doing something  sus*)
Qed.

Section def.
    Obligation Tactic := try done. (* TODO: Program cases or whatnot *)

    Ltac comp_ni := 
       let comp := fresh in 
       set comp := (X in ⟨ X _ | is_trusted ⟩ = _);
       (have: Noninterfering (store_to_view is_trusted) comp (store_to_view is_trusted)
          by match goal with H : Forall AtkCmdRestriction _ |- _ => 
                subst; move: H; Forall_inv_ssr=> + _; inversion 1
             end);
        subst comp.

    Program Definition comb_step (c: CombObj): CombObj :=
        let: 
            {| cont := cont; 
               real_st := real_st; 
               ideal_st := ideal_st; 
               sim_extra := sim_extra ; 
               trace := trace |} := c
        in
        if cont isn't (cmd :: cont') 
            then {| cont := cont; 
                    real_st := real_st; 
                    ideal_st := ideal_st; 
                    sim_extra := sim_extra ; 
                    trace := (⟨real_st| is_trusted⟩, None) :: trace |} else
        if cmd isn't (mk_cstep is_atk (assign comp)) then False_rect _ _ else (* Here, we throw an exception *)
        if is_atk is false then 
            {| 
               real_st := comp real_st; 
               ideal_st := comp ideal_st; 
               sim_extra := sim_extra;
               cont :=  cont';
               trace := ((⟨comp real_st |is_trusted ⟩,None)::trace)  (* You could also use ⟨ ideal_st | is_trusted ⟩ here! *)
               (* I 'dont like the fact that we repeat comp. This can lead to bugs.. *)
            |}
         else  
            {| 
               real_st := comp (corruptor atkreal tt real_st);
               ideal_st := comp ideal_st; (* Does this even get corrupted? *)
               sim_extra := f (mk_sim_state tt sim_extra);
               cont :=  (nlist pure_atk (substeps atkreal tt)) ++ cont'; (* This is not correct.. *)
               trace := ((⟨comp real_st |is_trusted ⟩, Some (leaker atkreal tt))::trace)  (* You could also use ⟨ ideal_st | is_trusted ⟩ here! *)
            |}.
    Next Obligation. 
        rewrite/ContinuationRestriction => *.
        by subst; eauto using Forall_inv_tail.
    Qed.

    Next Obligation. 
       rewrite/ContinuationRestriction=> *.
       by comp_ni; auto.
    Qed.

    Next Obligation. 
       rewrite/ContinuationRestriction=> *.
       apply/Forall_app; split; first by apply/pure_atklst_wt.
       by subst; apply: Forall_inv_tail; eauto.
    Qed.

    Next Obligation. 
       rewrite/ContinuationRestriction=> *.
       comp_ni; apply.
       match goal with H : _ = ?rhs |- _ = ?rhs => 
         move: (H) (corruptor_wf atkreal tt); clear
       end.
       by move=> <-; firstorder.
    Qed.

    Next Obligation. 
      rewrite/ContinuationRestriction=> *.
      suff: [elaborate forall cmd cont, 
              Forall AtkCmdRestriction (cmd:: cont) ->
              (forall (is_atk : bool) (comp : Store -> Store),
              mk_cstep is_atk (assign comp) <> cmd) ->
              False] by subst; eauto. (* I don't understand this elaborate thing *)
      clear=> - [] >; Forall_inv_ssr=> + _=> -; rewrite /AtkCmdRestriction=> - [? _].
      by apply.
    Qed.
End def.

Lemma comb_step_valid : forall c , 
    extract_i (comb_step c) = step atkideal (extract_i c) /\
    extract_r (comb_step c) = step atkreal (extract_r c). 
Proof.
    case=> c ? ? ? ?; case :c; first 
        by rewrite/extract_i/extract_r/==> _ ->.
    move=> [is_atk ?]  ? /[dup];  Forall_inv_ssr; rewrite{1}/AtkCmdRestriction=> - []; rewrite/Noninterfering=> ? ni _.
    case: is_atk;rewrite /extract_i/extract_r/==> _; last by split;  congr (_, (_,_) :: _); auto.
    repeat case: (learner _ _ _)=> *;rewrite /id.
    split;  congr (_, (_,_) :: _); apply: ni; auto.
    by move: (corruptor_wf atkreal); evar_spec_ssr=>-  [] eq _; erewrite eq.
Qed.

Theorem comb_extract: 
    forall c, extract_trace (extract_i c) = extract_trace (extract_r c). 
Proof. by case. Qed.

Goal b1 = b2. 
Proof.
    rewrite/b1/b2/⟦ _ ☠︎︎  _⟧.
    apply/functional_extensionality=> s; apply/functional_extensionality=> n.
    set msr:= (multistep _ _ _); set msi := (multistep _ _ _).
    suff: exists c, msr = extract_r c  /\ msi = extract_i c by move=> [? [-> ->]]; rewrite comb_extract.
    subst msr msi;  elim: n=> [|> [c [*]]]; first by
        exists (comb_init s); move: (comb_init_valid s)=> [-> ->].
    exists (comb_step c); move: (comb_step_valid c)=> [-> ->].
    move ? : (step atkreal _)=> ?;  move ? : (step atkideal _)=> ? /=. (* Controlled simpl. Locking is actually sick *)
    by intuition; congruence.
Qed.
