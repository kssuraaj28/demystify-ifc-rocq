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

Section example.
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
End example.


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

  Section aux.
    Variable element_label : Label. 
    Notation element_conf := (conf element_label).
    Notation element_int := (int element_label).

    Definition Public : Prop := element_conf ≼ attack_conf. 
    Definition Secret : Prop := ~Public. 

    Definition Untrusted : Prop := element_int ≼ attack_int.
    Definition Trusted   : Prop := ~Untrusted.


    (* My naming convention is same for Prop and Set *)
    Definition PublicTrusted   : Prop := Public /\ Trusted.
    Definition SecretTrusted   : Prop := Secret /\ Trusted.
    Definition PublicUntrusted : Prop := Public /\ Untrusted.
    Definition SecretUntrusted : Prop := Secret /\ Untrusted.

    (* I don't know why I do this *)
    Print Section aux.
  End aux.




  (* TODO: If I make this a definition and view it outside a section what happens? *)
  (* This is a subset type. I hope that coq gods are friendly to me, as I am using a dependent type *)
  (* 
    Essentially, we restrict the domain of the store.
  *)
  Definition StoreView (P : VarName -> Prop) : Set := 
    { x : VarName | P x } -> Value.



  (* TODO: What's the easiest way to test these close to where they are defined? 
  I think I'd like to have a way where I can just instantiate a section variable with something, and I test this example 'model'
  Maybe, I could use Modules and Parameters?
  The idea would be to define a module M that takes in a parameter p.
  Then you would use it as follows: m_example := M<4>
  *)

  Notation LiftLblPred := (fun Pred => fun idx => Pred (lbl idx)).


  Notation StoreViewAll := (StoreView (fun _ => True)). (* This is isomorphic to Store *)
  Notation StoreViewP := (StoreView (LiftLblPred Public)). (* Watchout, for Notations are not type checked! *)
  Notation StoreViewPU := (StoreView (LiftLblPred PublicUntrusted)).
  Notation StoreViewSU := (StoreView (LiftLblPred SecretUntrusted)).

  (* An attack is the following information *)
  Record AttackSnippet : Set := {
   (* How do the public untrusted values get transformed? *)
    pu_trans_strat : StoreViewP -> StoreViewPU ; 

   (* How do the secret untrusted values get transformed? *)
    su_trans_strat : StoreViewAll -> StoreViewSU;

   (* What information is the attacker learning for themselves? *)
    leak_strat : StoreViewP -> list Value; 
    }.

  Notation "☠︎︎⟨ x |  y | z ⟩" := {| pu_trans_strat := x ; su_trans_strat := y ; leak_strat := z |}.


  Section check.
    Variable pu_tr : StoreViewP -> StoreViewPU. 
    Variable su_tr : StoreViewAll -> StoreViewSU.
    Variable leak : StoreViewP -> list Value.
    Check ☠︎︎⟨ pu_tr | su_tr | leak⟩. (* I'm soo good *)
  End check.

  (* 
  This is one way to do this, 
  and probably not the correct way to do it. 
  We'd need a way to define composition of attack with program?
  I think that this might be okay though...
  *)

  Inductive AttackedLanguageCommand : Set :=  
  |  code (c : LanguageCommand)
  |  atk (a : AttackSnippet)
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

    Definition extract_StoreView (s : Store) (Pred : VarName -> Prop) : StoreView Pred :=
      fun c => 
        match c with 
          exist _ idx _ => (s idx)
        end.

    (* Algorithms are overrated. *)
    Definition UpdatedStore (oldstore : Store) {P} (update : StoreView P) (newstore : Store) : Prop := 
      forall (var : VarName), 
        ~(P var) -> newstore var = oldstore var /\
        forall (prf : P var), newstore var = update (exist _ var prf). 
        (* TODO: Is there notation for exist? Also, could I use Ltac to define this?*)

    (* Helper when the update is just for a single value. 
       I am a little bit sad that this is not a function
    *)
    Definition UpdatedStoreVal (oldstore var val newstore : _) := 
            let P := fun x => x = var in
            let storeslice := fun (inp : { x : VarName | P x }) =>  val in
            UpdatedStore oldstore storeslice newstore.



        (*
    (* TODO: Define these *)
    Axiom extract_PUStore : Store -> PUStore.
    Axiom extract_PTStore : Store -> PTStore.
    Axiom extract_STStore : Store -> STStore.
    Axiom extract_SUStore : Store -> SUStore.

    (*TODO: This is pretty bad. I should probably refactor this sooo good. *)
    Axiom update_storepu : Store -> PUStore -> Store.
    Axiom update_storept : Store -> PTStore -> Store.
    Axiom update_storest : Store -> STStore -> Store.
    Axiom update_storesu : Store -> SUStore -> Store.

    *)


    Inductive lang_cmd_eval : 
      Store -> (* Input store *)
      LanguageCommand ->  (* Command to run *)
      Event ->  (* Resulting event *)
      Store ->  (* Resulting store *)
      Prop := 

      | assignment_eval (store new_store var comp_fn : _) : 
          let new_val := comp_fn store in
          UpdatedStoreVal store var new_val new_store ->
          lang_cmd_eval store (var ← comp_fn) epsilon new_store

      | input_eval (store new_store var val : _) : 
          UpdatedStoreVal store var val new_store ->
          lang_cmd_eval store (? var) (input val) new_store

      | output_eval (store var : _) : 
          let val := store var in
          lang_cmd_eval store (! var) (output val) store.


    Inductive atk_snip_eval : 
      Store -> (* Input store *)
      AttackSnippet ->  (* Command to run *)
      list Value ->  (* Leaked data *)
      Store ->  (* Resulting store *)
      Prop := 
      | atk_eval (store pu_tr su_tr leak_fn : _) : 
          let ststore := extract_STStore store in
          let pustore := extract_PUStore store in
          let ptstore := extract_PTStore store in
          let sustore := extract_SUStore store in

          let leak := leak_fn (ptstore, pustore)  in

          (* There is some type level something happening *)
          let pustore' := pu_tr (ptstore, pustore) in
          let sustore' := su_tr (ptstore, ststore,  pustore, sustore) in

          let store' := update_storepu (update_storesu store sustore') pustore' in

          let atk := (☠︎︎⟨ pu_tr | su_tr | leak_fn ⟩) in
          
          atk_snip_eval store atk leak store.




    Record Configuration := {
      prog : AttackedProgram ;
      store : Store
      }.


    (* Evaluate an attack on a store *)
    Inductive TransitionRel : AttackedProgram -> Events -> AttackedProgram -> Prop := 
    .


  End OperationalSemantics.

End AttackSem.
