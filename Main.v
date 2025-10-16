(* I would eventually like to have a module or a typeclass for lattices *)

Inductive PartialOrderExample : Set :=
  | root
  | alice
  | bob
  | chuck
  | any.


Reserved Notation "x ≼ y" (at level 20).
(* I really need to have maybe a module or a typeclass *)
Inductive PartialOrderFlows : PartialOrderExample -> PartialOrderExample -> Prop :=
  | root_top (e : _) : e ≼ root
  | any_bot (e : _) : any ≼ e
  | refl (e : _) : e ≼ e
where "x ≼ y" :=  (PartialOrderFlows x y).

(* This is essentially the M3 lattice.. *)

Section Examples.
  Hint Constructors PartialOrderFlows : core.
  Hint Extern 10 => match goal with [ H : _ ≼ _ |- _ ] => inversion H end : core.

  Goal root ≼ root. Proof. auto. Qed.
  Goal any ≼ root. Proof. auto. Qed.
  Goal alice ≼ root. Proof. auto. Qed.
  Goal any ≼ bob. Proof. auto. Qed.
  Goal any ≼ bob. Proof. auto. Qed.
  Goal ~ alice ≼ bob. Proof. auto.  Qed.
  Goal ~ bob ≼ alice. Proof. auto. Qed.
  Goal forall x, x ≼ x. Proof. auto. Qed.
  Goal forall x y z, x ≼ y -> y ≼ z -> x ≼ z. Proof. auto. Qed.
End Examples.


(* TODO: Have a confidentiality partial order, and integrity partial order, etc. *)
(* 
In an ideal world. I would define the partial order 'interface' - A typeclass perhaps. 
Then, everything else takes that thing as input. Perhaps the best idea is to
start with bare dependent records, and feel the pain, before migrating to
typeclasses
*)

Definition ConfPO :=  PartialOrderExample.
Definition IntPO :=  PartialOrderExample.

Record Label : Set := { 
  conf : ConfPO ;
  int : ConfPO
  }.

Notation " ⟨ l1 , l2 ⟩ " := {| conf := l1 ; int := l2 |}.
Check ⟨ root , alice ⟩ : Label.

Record VarName :  Set := {
  lbl : Label ;
  name : nat
  }.

(* TODO: Can we automatically generate equality check for this? *)

Notation " l ~ id " := {| lbl := l ; name := id |} (at level 30).
Check ⟨ root , alice ⟩ ~ 5 : VarName.

(* This is our 'Value' set. This should be abstracted out *)
Definition Value : Set := nat.
Definition val_eqb : Value -> Value -> bool := Nat.eqb. (* TODO: Do we need this? *)

Definition Store := VarName -> Value.
Example s1 : Store := fun _ => 5. (* TODO: Module this? *)
Example s2 : Store := fun v => 
  match v with 
  | ⟨ root , root ⟩ ~ 0 => 0
  | ⟨ root , root ⟩ ~ 1 => 1 
  | ⟨ root , root ⟩ ~ _ => 4
  |  _ => 42 
  end. (* TODO: Module this? *)

(* The set of commands we have in our langauge *)
Inductive LanguageCommand : Set :=
  | assignment (v : VarName) (f : Store -> Value)  (* Mixing syntax and semantics like a pro *)
  | input (v : VarName)
  | output (v : VarName)
.

Notation " x ← f " := (assignment x f) (at level 50).
Notation " ? x  " := (input x) (at level 50).
Notation " ! x  " := (output x) (at level 50).


Definition LanguageProgram := list LanguageCommand. (* Only straightline code for now *)


(* I really feel like this should be 'Module'. Maybe I should ask Gary. *)
Module AttackSem.
  Parameter attack_level : Label.
  Notation attack_conf :=  (conf attack_level).
  Notation attack_int :=  (int attack_level).

  Section Aux.
    Variable element_label : Label. 
    Notation element_conf := (conf element_label).
    Notation element_int := (int element_label).

    (* TODO: Why can't I make this Notation? *)
    Definition public := element_conf ≼ attack_conf. 
    Definition secret := ~public. 

    Definition untrusted := element_int ≼ attack_int.
    Definition trusted := ~untrusted.


    (* My naming convention is different for Prop and Set *)
    Definition public_trusted   : Prop := public /\ trusted.
    Definition secret_trusted   : Prop := secret /\ trusted.
    Definition public_untrusted : Prop := public /\ untrusted.
    Definition secret_untrusted : Prop := secret /\ untrusted.

    (* I don't know why I do this *)
    Print Section Aux.
  End Aux.



  (* TODO: If I make this a definition and view it outside a section what happens? *)
  (* This is a subset type. I hope that coq gods are friendly to me, as I am using a dependent type *)
  (* 
    Essentially, we restrict the domain of the store.
  *)
  Notation StoreView := (fun P => { x : VarName | P (lbl x) } -> Value).

  (* TODO: What's the easiest way to test these close to where they are defined? 
  I think I'd like to have a way where I can just instantiate a section variable with something, and I test this example 'model'
  Maybe, I could use Modules and Parameters?
  The idea would be to define a module M that takes in a parameter p.
  Then you would use it as follows: m_example := M<4>
  *)

  Definition PTStore : Set := StoreView public_trusted.
  Definition STStore : Set := StoreView secret_trusted.
  Definition PUStore : Set := StoreView public_untrusted.
  Definition SUStore : Set := StoreView secret_untrusted.

  (* An attack is the following information *)
  Record AttackSnippet : Set := {
   (* How do the public untrusted values get transformed? *)
    pu_trans_strat : (PTStore * PUStore) -> PUStore; 

   (* How do the secret untrusted values get transformed? *)
    su_trans_strat : (PTStore * STStore * PUStore * SUStore ) -> SUStore;

   (* What information is the attacker learning for themselves? *)
    leak_strat : (PTStore * PUStore) -> list Value; 
    }.

  (* 
  This is one way to do this, 
  and probably not the correct way to do it. 
  We'd need a way to define composition of attack with program?
  I think that this might be okay though...
  *)

  Inductive AttackedLanguageCommand : Set :=  
  |  code (c : LanguageCommand )
  |  atk (a : AttackSnippet )
  . (* Could I coerce LanguageCommand into AttackedLanguageCommand*)

  Definition AttackedProgram := list AttackedLanguageCommand.

  Module OperationalSemantics.
    Inductive Event : Set := 
      | input (v : Value)
      | output (v : Value)
      | epsilon 
      | adv_leak (lv : list Value).



    (* TODO: I need to define this later
    Moreover, I feel like this should be something coq should be able to do automatically.
    TODO: Is this naming convention okay?
    *)
    Axiom eqb_VarName : VarName -> VarName -> bool.
    Definition update_store (s : Store) (idx : VarName) (v : Value) : Store :=  
      fun idx' => 
      if (eqb_VarName idx idx') then v
      else s idx.

    (* TODO: Test this *)



    Inductive lang_cmd_eval : 
      Store -> (* Input store *)
      LanguageCommand ->  (* Command to run *)
      Event ->  (* Resulting event *)
      Store ->  (* Resulting store *)
      Prop := 

      | assignment_eval (store var comp_fn : _) : 
          let new_val := comp_fn store in
          let new_store := update_store store var new_val in
          lang_cmd_eval store (var ← comp_fn) epsilon new_store

      | input_eval (store var val : _) : 
          let new_store := update_store store var val in
          lang_cmd_eval store (? var) (input val) new_store

      | output_eval (store var : _) : 
          let val := store var in
          lang_cmd_eval store (! var) (output val) store
    .

    (* Maybe we prove that this is deterministic? *)

    Record Configuration := {
      prog : AttackedProgram ;
      store : Store
      }.


    (* Evaluate an attack on a store *)
    Inductive TransitionRel : AttackedProgram -> Events -> AttackedProgram -> Prop := 
    .




  End OperationalSemantics.


End AttackSem.

(* This really should be module *)
Section OperationalSemantics.

End OperationalSemantics.
