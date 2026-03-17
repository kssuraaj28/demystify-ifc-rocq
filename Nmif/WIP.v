(* Time to cook *)
From Stdlib Require Import ssreflect List FunctionalExtensionality.
Import ListNotations.


(* This may be useful *)
From QuickChick Require Import Decidability.

Require Import Util VarValStore Syntax Semantics Attacker.
Import Util.Dec.

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
Definition atkreal : AdvStateMachine AtkRealStates := {|
    init_state := fun _ => tt ; 
    init_substeps := fun _ => 1 ;
    corruptor := fun _ sv => (fun v => 5) ;  (* Set all untrusted vars to 5 *)
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
  |}.

Definition AtkIdealStates := unit.
Definition atkideal : AdvStateMachine AtkIdealStates := {|
    init_state := fun _ => tt ; 
    init_substeps := fun _ => 1 ;
    corruptor := fun _ sv => sv ;  (* Need to modify this appropriately *)
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
    |}.


Import Semantics.Notations.
Definition b1 := ⟦ [simple_cmd] ☠︎︎ atkreal ⟧.
Definition b2 := ⟦ [simple_cmd] ☠︎︎ atkideal ⟧.


Definition init_s :Store := 
  fun v => 1.

(* Can I quickchick this? *)
Goal 
  let: s := 100 in
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
Section assumptions.
  Notation CfgR := (Cfg AtkRealStates).
  Notation CfgI := (Cfg AtkIdealStates).

  Definition BisimRel (cr : CfgR) (ci: CfgI) : Prop :=
    let: (contr, storer, asr, trr) :=  cr in
    let: (conti, storei, asi, tri) :=  ci in
    (conti = contr) /\
    (asr = asi) /\
    (trr = tri). (* TODO Store equality *)
  

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
    by [].
  Qed.


  Parameter bisim_step: forall c1 c2,
                          BisimRel c1 c2 ->
                          BisimRel (step atkreal c1) (step atkideal c2).


End assumptions.

(*
BisimRel (step atkreal (multistep atkreal _n_ c1))
  (step atkideal (multistep atkideal _n_ c2))
  *)

Goal b1 = b2 . Proof.
  apply: functional_extensionality=> s; apply: functional_extensionality=> n.
  rewrite /b1 /b2 !/(⟦_☠︎︎_⟧).
  
  set c1 := (initial_cfg _ _ _); set c2 := (initial_cfg _ _ _). (* Set second? *) 
  move e1: (multistep _ _ c1) => ms1; move e2: (multistep _ _ c2) => ms2. 

  apply: bisim_extract. Undo.
  apply/bisim_extract.

  elim: n ms1 ms2 e1 e2=> [> | > ih >] <- <- /=.
    rewrite /c1 /c2 /=.
    by apply: bisim_init.

  by apply: bisim_step; apply: ih. Undo.
  by apply/bisim_step /ih. (* What the hell is this *)
Qed.

(* There three admits exactly correspond to 
the three things you need to prove when you have bisimulation relations
- The first is BisimRel -> property you want
- The second is what you want for initial states.
- The third is your stepping relation

*)
