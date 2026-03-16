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

Instance atk1i : AdvSMPrm := {
    AtkStates := unit ;
    init_state := fun _ => tt ; 
    init_substeps := fun _ => 1 ;
    corruptor := fun _ sv => (fun v => 5) ;  (* Set all untrusted vars to 5 *)
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
    }.

Instance atk2i : AdvSMPrm := {
    AtkStates := unit ;
    init_state := fun _ => tt ; 
    init_substeps := fun _ => 1 ;
    corruptor := fun _ sv => sv ;  (* Need to modify this appropriately *)
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
    }.


Import Semantics.Notations.
Definition b1 := ⟦ [simple_cmd] ☠︎︎ atk1i ⟧.
Definition b2 := ⟦ [simple_cmd] ☠︎︎ atk2i ⟧.


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

Parameter BisimRel: forall {a: AdvSMPrm}, Cfg -> 
                    forall {a': AdvSMPrm}, Cfg -> Prop.
Reset BisimRel.
Parameter BisimRel: Cfg -> Cfg -> Prop.


Check @initial_cfg.

Goal b1 = b2 . Proof.
  apply: functional_extensionality=> s; apply: functional_extensionality=> n.
  rewrite /b1 /b2 !/(⟦_☠︎︎_⟧).
  (* Set second? *) 
  set c1 := (initial_cfg _ _); set c2 := (initial_cfg _ _).
  set ms1 := (multistep _ _); set ms2 := (multistep _ _).

  suff: BisimRel ms1 ms2 by admit. (* You need this *)


  (* I don't like this.. *)
  have: ms1 = multistep n c1 by [].
  have: ms2 = multistep n c2 by [].

  elim:n ms1 ms2=> [/= > -> ->| ]; first by admit.
  move=> n ih ? ? -> ->.

  suff: BisimRel (multistep n c1) (multistep n c2) by admit. (* You need this *)
  by apply: ih.
Admitted.

(* There three admits exactly correspond to 
the three things you need to prove when you have bisimulation relations
- The first is BisimRel -> property you want
- The second is what you want for initial states.
- The third is your stepping relation

*)
