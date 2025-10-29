(* I would eventually like to have a module or a typeclass for lattices *)
From Stdlib Require Import List.
Import ListNotations.

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
(* Watchout! When you do _, PartialOrderFlows is defined okay, but the notation is messed up! TODO *)


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
  Goal ~ chuck ≼ alice. Proof. auto. Qed.
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
  int : IntPO
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

  (* Watchout, for notations are not type checked *)
  Notation AllVar := (fun _ => True).
  Notation PubVar := (LiftLblPred Public).
  Notation PUVar := (LiftLblPred PublicUntrusted).
  Notation SUVar := (LiftLblPred SecretUntrusted).

  (* TODO: Attacks need to have private memory  *)

  (* An attack is the following information *)
  Record AttackSnippet : Set := {
   (* How do the public untrusted values get transformed? *)
    pu_trans_strat : (StoreView PubVar) -> (StoreView PUVar); 

   (* How do the secret untrusted values get transformed? *)
    su_trans_strat : (StoreView AllVar) -> (StoreView SUVar);

   (* What information is the attacker learning for themselves? *)
    leak_strat : (StoreView PubVar) -> list Value; 
    }.

  Notation "☠︎︎⟨ x |  y | z ⟩" := {| pu_trans_strat := x ; su_trans_strat := y ; leak_strat := z |}.

  Check let pu_tr := _ in let su_tr := _ in  let leak := _ in
      ☠︎︎⟨ pu_tr | su_tr | leak⟩. (* I'm soo good *)

  Check fun pu_tr su_tr leak => (☠︎︎⟨ pu_tr | su_tr | leak⟩ : _). (* I'm soo good. Note how there is a difference between this and the previous one *)


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
    TODO: Is this naming convention okay?
    *)

    Definition extract_storeview (s : Store) (Pred : VarName -> Prop) : StoreView Pred :=
      fun c => 
        match c with 
          exist _ idx _ => (s idx)
        end.


    (* 
    Algorithms are overrated. Here, this P is a predicate. 
    This means that getting computational things might turn out to be bad 
    *)
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


    (* What does it mean to combine two store views*)
    (* I also don't know whether this works. I would like to have an example to check. Moreover, I think that this is not deterministic*)
    (* I wonder if an inductive definition is clearer *)
    (* TODO: Can I use Ltac for this? *)
    Definition CombinedStoreView {P1} {P2} (sv1 : StoreView P1) (sv2 : StoreView P2) (sres : StoreView (fun var => P1 var \/ P2 var)) : Prop :=
      forall var, 
        forall (prf : P1 var), 
          let val := sv1 (exist _ var prf) in 
          let resval := sres (exist _ var (or_introl prf)) in (* TODO: Why is it that I can (or_introl _ prf) also?*)
          resval = val
      \/
        forall (prf : P2 var), 
          let val := sv2 (exist _ var prf) in 
          let resval := sres (exist _ var (or_intror prf)) in 
          resval = val.



    Inductive LangCmdEval : 
      Store -> (* Input store *)
      LanguageCommand ->  (* Command to run *)
      Event ->  (* Resulting event *)
      Store ->  (* Resulting store *)
      Prop := 

      | assignment_eval (store new_store var comp_fn : _) : 
          let new_val := comp_fn store in
          UpdatedStoreVal store var new_val new_store ->
          _ store (var ← comp_fn) epsilon new_store

      | input_eval (store new_store var val : _) : 
          UpdatedStoreVal store var val new_store ->
          _ store (? var) (input val) new_store

      | output_eval (store var : _) : 
          let val := store var in
          _ store (! var) (output val) store.


    Inductive AtkSnipEval : 
      Store -> (* Input store *)
      AttackSnippet ->  (* Command to run *)
      list Value ->  (* Leaked data *)
      Store ->  (* Resulting store *)
      Prop := 
      | atk_eval (store new_store combined_view (* Make it exists?*) pu_tr su_tr leak_fn : _) : 
          let pubstore := extract_storeview store PubVar in
          let allstore := extract_storeview store AllVar in

          let atk := (☠︎︎⟨ pu_tr | su_tr | leak_fn ⟩) in
          let newpustore := pu_tr pubstore in 
          let newsustore := su_tr allstore in
          let leak := leak_fn pubstore in

          CombinedStoreView newpustore newsustore combined_view -> (* Maybe this combined view thing should really be exists *)
          UpdatedStore store combined_view new_store -> (* Maybe this combined view thing should really be exists *)

          _ store atk leak new_store. 

    Record Configuration := {
      prog : AttackedProgram;
      store : Store
      }.

    (* Evaluate an attack on a store *)
    Inductive TransitionRel : 
      Configuration ->  (*Starting state*)
      Event ->  (* Event, if any *)
      Configuration -> (* Resulting state *)
      Prop := 
      | atk_step (store store' atk_snip leak remaining : _) :
          let cfg := ({| prog := (atk atk_snip) :: remaining ; store := store |}) in
          let cfg' := ({| prog := remaining ; store := store' |}) in
          AtkSnipEval store atk_snip leak  store' ->
          TransitionRel cfg (adv_leak leak) cfg'

      | prg_step  (store store' cmd event remaining : _) :
          let cfg := ({| prog := (code cmd) :: remaining ; store := store |}) in
          let cfg' := ({| prog := remaining ; store := store' |}) in
          LangCmdEval store cmd event store' ->
          TransitionRel cfg event cfg'.


    (* I'd like to define what NMIF means semantically. 
    - Single attack nmif. There are multiple choices here. 
        The attacker that does not touch SU. The attacker that sets them to 0, etc.
        Are all these definitions equivalent?
    - Lifting this to multiple attacks. 
    *)

  End OperationalSemantics.
End AttackSem.
