(* Time to cook *)
From Stdlib Require Import ssreflect List.
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
    corruptor := fun _ sv => sv ; (* Need to modify this appropriately  *)
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
    }.

Instance atk2i : AdvSMPrm := {
    AtkStates := unit ;
    init_state := fun _ => tt ; 
    init_substeps := fun _ => 1 ;
    corruptor := fun _ sv => sv ; (* Need to modify this appropriately  *)
    learner := fun _ _ => tt; (* This is lemunsnokun attacker *)
    leaker := fun _ => 67 ;
    substeps := fun _ => 0; (* simple man *)
    }.


Import Semantics.Notations.
Definition b1 := ⟦ [simple_cmd] ☠︎︎ atk1i ⟧.
Definition b2 := ⟦ [simple_cmd] ☠︎︎ atk2i ⟧.

Goal b1 = b2. Proof.
  by [].
Qed.
