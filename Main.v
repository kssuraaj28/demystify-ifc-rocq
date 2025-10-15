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

Notation " l ~ id " := {| lbl := l ; name := id |} (at level 30).
Check ⟨ root , alice ⟩ ~ 5 : VarName.

(* This is our 'Value' set *)
Definition Value := nat.

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
  | assignment (v : VarName) (f : Store -> Store)  (* Mixing syntax and semantics like a pro *)
  | input (v : VarName)
  | output (v : VarName)
.

Notation " x ← f " := (assignment x f) (at level 50).
Notation " ? x  " := (input x) (at level 50).
Notation " ! x  " := (output x) (at level 50).


Definition LanguageProgram := list LanguageCommand. (* Only straightline code for now *)


(* I really feel like this should be 'Module'. Maybe I should ask Gary. *)
Section AttackSem.
  Variable attack_level : Label.
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
    Print Section AttackSem.
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

End AttackSem.


(* TODO: There does seem to be some duplication here... I don't like this at all. *)
Fail Module FourPointProg (attacklevel : nat). (* Hmm. You can only parameterize modules by 'module types'. Actually, you can use this Parameter thing *)

  Inductive FourPoint := ST | PT | PU | SU.
  Record VarName : Set := {
    point : FourPoint ;
    name : nat 
  }.

  Notation " p ~ id " := {| point := p ; name := id |} (at level 50).
  Check ST~5.

  Definition Value := nat. (* Maybe this really needs to be argument to a module *)
  Definition Store := VarName -> Value.



  (* This is really a basic block *)
  Inductive LanguageCommand : Set :=
    | assignment ( v : VarName ) ( f : Store -> Store)
    | input ( v : VarName )
    | output ( v : VarName )
  .

  (* An AdversaryAttack is a pair of functions.
  - state transform : Store -> Store, but you don't read the secret variables and dont' corrupt the trusted variables
  - leak transform : Store -> LeakedVals, but the you don't read the secret variables.

  What is the right way to do this?
  - We could require that it is any function but require a proof that of this property.
  - We could syntactically construct something. How exactly will this work out?

  *)
  Record AdversaryAttack := 
  {
    state_trans: Store -> Store  ;
    leak_info: Store -> list Value 
  }. (* This is not exactly correct. *)


  



  (* Eventually we need to do something like forall adv, exists sim. You need to define a composition operation with these single attack programs. 
  Q: Can this be a partial operation? Does it make sense to have a type system here?
  *)



End FourPointProg.
