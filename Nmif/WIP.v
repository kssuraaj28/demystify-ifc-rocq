(* Time to cook *)
From Stdlib Require Import ssreflect ssrbool List FunctionalExtensionality.
Import ListNotations.


(* This may be useful *)
From QuickChick Require Import Decidability.

Require Import Util VarValStore Syntax Semantics Attacker Util Noninterference Tacs. 
Import Util.Dec Util.List. 


Ltac Forall_inv :=  move=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _).

Ltac evar_spec :=  
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

  (* 
    I think that constructor is okay to be part of finisher. 
    Don't make it part of forward reasoning
  *)
  Lemma restrict_rel: forall p,
    ProgRestriction p -> 
    (forall n, ContinuationRestriction (prog_zip p n)).
  Proof.
    rewrite/ContinuationRestriction/ProgRestriction. 
    elim=> [_ n|]; first by elim: n=> //= >; constructor; easy.
    move=> c l ih /ltac:(Forall_inv).
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

Definition AtkIdealStates := AtkRealStates.
Section idealatk.
  Import Tacs.SsrHack.
  Obligation Tactic := idtac.
  Program Definition atkideal : AdvStateMachine AtkIdealStates := {|
      init_state := fun _ => tt ; 
      init_substeps := init_substeps atkreal;
      corruptor _ := id;
      corruptor_wf := _;
      learner := learner atkreal; 
      learner_wf := _;
      leaker := leaker atkreal;
      substeps := substeps atkreal
      |}.
  Next Obligation. by easy. Qed.
  Next Obligation. by move: (learner_wf atkreal); firstorder. Qed.
End idealatk.

Import Semantics.Notations.
Parameter myprog : Prog. Axiom myprog_wt : ProgRestriction myprog.
Definition b1 := ⟦ myprog ☠︎︎ atkreal ⟧.
Definition b2 := ⟦ myprog ☠︎︎ atkideal ⟧.



(* TODO: More test. 
  TODO: Leak test.
  Define in terms of real attacker

*)

(* Can I construct a proof object with more state? 

Parameter Po : Type.
Parameter BisimRel : Po -> Type.
You need to lift step to Po..
*)
Section bisim.
  Notation CfgR := (Cfg AtkRealStates).
  Notation CfgI := (Cfg AtkIdealStates).

  Import VarValStore.Notations.

  Definition BisimRel (cr : CfgR) (ci: CfgI) : Prop :=
    let: (contr, storer, asr, trr) :=  cr in
    let: (conti, storei, asi, tri) :=  ci in
    ContinuationRestriction contr /\ (* I don't like this. Uniform object is better *)
    (conti = contr) /\
    (asr = asi) /\
    ⟨ storer | is_trusted ⟩ = ⟨ storei | is_trusted ⟩ /\
    (trr = tri). 
  

  Lemma bisim_extract: forall c1 c2,
                  BisimRel c1 c2 -> extract_trace c1 = extract_trace c2.
  Proof.
    move=> [[[? ?]?]?].
    move=> [[[? ?]?]?] /=.
    by intuition.
  Qed.

  Lemma bisim_init: 
    forall s,
    BisimRel 
      (initial_cfg myprog atkreal  s)
      (initial_cfg myprog atkideal s).
  Proof.
    move=> s; split; first by apply/restrict_rel/myprog_wt.
    by repeat split=> //; repeat case: (init_state _ _).
  Qed.

  Lemma bisim_step: forall c1 c2,
                          BisimRel c1 c2 ->
                          BisimRel (step atkreal c1) (step atkideal c2).
  Proof.
    move=> [[[cont ? ]astr] ?] [[[? ?]asti]?].
    move=> /= [wt [-> [-> [trseq ->]]]] /=.
    case: cont wt=> [|atkcmd ? wt]; first by rewrite /= trseq //=.
    case rst: (atk_cmd_step atkreal _ _ _) => [[[sr []] contr ] lkr]. (* Note how I make tt. TODO *)
    case ist: (atk_cmd_step atkideal _ _ _) => [[[si []] conti ] lki].
    move: wt=>/ltac:(Forall_inv) wth wttl /=.
    clear- trseq rst ist wth wttl; set rsv := ⟨ sr | _ ⟩; set isv := ⟨ si | _⟩.
    suff: ([elaborate ContinuationRestriction contr /\ conti = contr /\  rsv = isv /\ lkr = lki])
      by intuition; try congruence; apply/Forall_app.
    rewrite {}/rsv {}/isv; case: atkcmd wth ist rst=> [isatk cmd]. 
    rewrite/AtkCmdRestriction=> [[]]; rewrite/Noninterfering=> > ni.
    move: (corruptor_wf atkreal)=> wfr; clear -wfr ni trseq.
    rewrite/atk_cmd_step.
    move cs1: (clean_cmd_step _ _)=> [? k1].
    move cs2: (clean_cmd_step _ _)=> [? k2].
    repeat move: (learner _ _ _)=> [] /=. (* TODO. This has to be two*)
    move: (substeps _ _)=> ?. (* TODO: I think that this can just be one. Same for bottom also *)
    move: (leaker _ _)=> ?. 
    move=> e1 e2. 
    case: isatk e1 e2 cs1 cs2=> 
      [[<-<-<-] [<-<-<-]| [<-<-<-<-] [<-<-<-]]/=[<-<-][<-<-];
      (repeat split; first by apply/restrict_rel; red; auto);
      apply: ni; last by [].
    rewrite/id -{}trseq. (* Okay, we cannot allow arbitrary computation in the attacker! *)
    move: wfr =>/(_ asti) [+ _]; clear=> wtint.
    by move: (corruptor _ _) (store_to_view _) wtint => comp view /(equal_f); apply. (* TODO: I proved an useless lemma in storeview *)
  Qed.

End bisim.

(*
BisimRel (step atkreal (multistep atkreal _n_ c1))
  (step atkideal (multistep atkideal _n_ c2))
  *)

Goal b1 = b2 . Proof.
  apply: functional_extensionality=> s; apply: functional_extensionality=> n.
  rewrite /b1 /b2 !/(⟦_☠︎︎_⟧).
  set c1 := (initial_cfg _ _ _); set c2 := (initial_cfg _ _ _). (* Set second? *) 
  move e1: (multistep _ _ c1) => ms1; move e2: (multistep _ _ c2) => ms2. 
  apply/bisim_extract.
  elim: n ms1 ms2 e1 e2=> [> | > ? >] <- <- /=; first by apply/ bisim_init.
  by apply/bisim_step; auto. (* What the hell is this *)
Qed.

(* There three admits exactly correspond to 
the three things you need to prove when you have bisimulation relations
- The first is BisimRel -> property you want
- The second is what you want for initial states.
- The third is your stepping relation

*)
