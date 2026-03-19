(* Time to cook *)
From Stdlib Require Import ssreflect ssrbool List FunctionalExtensionality.
Import ListNotations.


(* This may be useful *)
From QuickChick Require Import Decidability.

Require Import Util VarValStore Syntax Semantics Attacker Util. 
Import Util.Dec. 

Section ni.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm}.

  (* Is this the right definition? I don't even know *)
  Definition Noninterfering (p: pred Vars) (comp : Store -> Store) :=
    forall s1 s2,
    ⟨ s1 | p ⟩ = ⟨ s2 | p⟩ ->
    ⟨ comp s1 | p ⟩ = ⟨ comp s2 | p⟩.
      
End ni.

Section ts.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  (* Should this be inductive? *)
  Inductive CmdRestriction: Cmd -> Prop :=
    nitr : forall comp, 
        Noninterfering is_trusted comp ->
        CmdRestriction (assign comp).

  (* This name is stupid *)
  Definition AtkCmdRestriction '(mk_cstep _ c) : Prop :=
    CmdRestriction c.

  Definition ContinuationRestriction: Continuation -> Prop :=
    Forall AtkCmdRestriction.

End ts.

Instance vli : ValPrm := {Vals := nat}.
Inductive EgVars := st | pt | pu | su. Instance eg_dec : DecEq EgVars. Proof. by dec_eq. Qed. (* I wonder whether there are better tactics *)
Instance vri : VarPrm := {Vars := EgVars}.

Instance lvli : AdvLvlPrm := {| 
                  is_untrusted := 
                    fun v => 
                      match v with
                      | st => false
                      | pt => false
                      | pu => true
                      | su => true
                      end ;
                  is_public := 
                    fun v =>
                      match v with
                      | st => false
                      | pt => true
                      | pu => true
                      | su => false
                      end ;
                |}.

Definition simple_cmd : Cmd := 
      assign (fun _ => (fun _ => 1 )). (* Sets all variables to 1 *)

Instance lki : AdvLeakPrm := nat.

Definition AtkRealStates := unit.
Obligation Tactic := idtac. (* TODO: There is  *)
Program Definition atkreal : AdvStateMachine AtkRealStates := {|
    init_state := fun _ => tt ; 
    init_substeps := fun _ => 1 ;
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
  |}.
  Next Obligation.
    admit.
  Admitted.

  Next Obligation.
  Admitted.


Definition AtkIdealStates := unit.
Program Definition atkideal : AdvStateMachine AtkIdealStates := {|
    init_state := fun _ => tt ; 
    init_substeps := fun _ => 1 ;
    corruptor := fun _ sv _=>  None;
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
    |}.
  Next Obligation.
    by [].
  Defined.


Import Semantics.Notations.
Definition b1 := ⟦ [simple_cmd] ☠︎︎ atkreal ⟧.
Definition b2 := ⟦ [simple_cmd] ☠︎︎ atkideal ⟧.


Definition init_s :Store := 
  fun v => 10.

(* Can I quickchick this? *)
Goal 
  let: s := 1000 in
  b1 init_s s = b2 init_s s. by []. Qed.

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
      (initial_cfg [simple_cmd] atkreal  s)
      (initial_cfg [simple_cmd] atkideal s).
  Proof.
    move=> s /=; split => //=.
    by constructor => //=.
  Qed.

  Lemma bisim_step: forall c1 c2,
                          BisimRel c1 c2 ->
                          BisimRel (step atkreal c1) (step atkideal c2).
  Proof.
    move=> [[[cont ?]?]?] [[[? ?]?]?].
    move=> /= [wt [-> [-> [trseq ->]]]] /=.    (* How to simpl only in Hypothesis *)
    case: cont wt=> [|atkcmd ? wt]; first by rewrite /= trseq //=.
    case rst: (atk_cmd_step atkreal _ _ _) => [[[sr ?] ? ] ?].
    case ist: (atk_cmd_step atkideal _ _ _) => [[[si ?] ? ] ?].
    move: wt=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _)=> wth wttl /=.
    clear- trseq rst ist wth wttl.
    set rsv := ⟨ sr | _ ⟩; set isv := ⟨ si | _⟩.
    case: atkcmd wth ist rst=> [isatk cmd]. 
    rewrite/AtkCmdRestriction=> - [].
    rewrite/Noninterfering=> > ni.
    move: (corruptor_wf atkreal)=> wtr.
    case: isatk=> /= => e1 e2; 
    case: e1=> e1 <-<-<-; case: e2=> e2 <-<-<- /=;
    (suff ->: rsv=isv by repeat split=> //=); rewrite {}/rsv {}/isv; (* How to subst *)
    move: e1 e2=> <- <-; 
    move: ni; apply; 
    clear -trseq wtr; last by [].
    rewrite/⟨_ →_⟩ /⟨_|_⟩/=; apply/functional_extensionality=> v.
    case v_tr:(is_trusted v) => //=; apply/f_equal.
    set atk_out := (X in match X with | None => _ | _ => _  end).
    (have->: atk_out = None by apply/wtr); clear -trseq v_tr. (* Is this the best style? *)
    move: trseq v_tr; rewrite /⟨_|_⟩. 
    by move=>/equal_f/(_ v)/[swap]->[].
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
