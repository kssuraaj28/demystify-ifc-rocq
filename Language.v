From Stdlib Require Import List.

From NMIF Require Import PartialOrder.

Set Implicit Arguments. 

(* I think that this is probably the better way? *)
(* TODO: This should be typeclass eventually, I think *)
Record PartOrderParam : Type := {
  conf_po : PartialOrder;
  int_po : PartialOrder;
 }.

Section label. 
  Variable (params : PartOrderParam).  (* This is my convention for abstraction. *)

  Let conf_po := conf_po params.
  Let ConfCarrier := Carrier (data conf_po).
  Let ConfOrder := Ordering (data conf_po).

  Let int_po := int_po params.
  Let IntCarrier := Carrier (data int_po).
  Let IntOrder := Ordering (data int_po).


  Notation "x '≼c' y" := (ConfOrder x y)(at level 70).
  Check _ ≼c _. (* Is there a useful place where we'd want to have notations but the check will fail? *)

  Notation "x '≼i' y" := (IntOrder x y)(at level 70).
  Check _ ≼i _.


  Record Label : Type := { 
    conf : ConfCarrier;
    int : IntCarrier
    }.

  Notation " ⟨ l1 , l2 ⟩ " := {| conf := l1 ; int := l2 |}.

  Section test.
    Variables (root : ConfCarrier) (alice : IntCarrier).
    Check ⟨ root , alice ⟩ : Label.
  End test.
End label.


(* Again, I think that this should be typeclasses :). I really should learn how to do this typeclass magic. *)
Record ValueParam : Type := {
  ValCarrier : Type ;
  val_eq_dec : forall v v' : ValCarrier, {v = v'} + {v <> v'} ;
  }.


Section varname.
  Variable p : PartOrderParam.
  Let Label := Label p. 
  (* Maybe this is good enough, for now.
  However, I think that once I become soo good, I can use typeclasses, 
  and become a god
  *)

  Record VarParam : Type := {
    VarCarrier : Type ;
    var_lbl : VarCarrier -> Label ; (* Is it possible that this can be inferred using the typeclass mechanism?*)
    var_eq_dec : forall v v' : VarCarrier, {v = v'} + {v <> v'} ;
    }.
End varname.



Section store.
  (* I really like my sections to be short. *)
  Variables po   : PartOrderParam.
  Let VarParam := VarParam po. (* This is what I want to do.. *)

  Variables vals : ValueParam.
  Variables vars : VarParam.

  Let VarName := VarCarrier vars.
  Let Value := VarCarrier vars.

  Definition Store := VarParam -> Value.

  Section storeview.
    Variable VarPred : VarName -> Prop. (* If you make this a bool, then you need to make a whole bunch of things decidable, which I am not going to do now.. *)
    Let FilteredVars := {x : VarName | VarPred x}. (* Refinement type *)
    Definition Storeview := FilteredVars -> Value.
  End storeview.

End store.


    Section example.
      Variable (natval : nat -> Value).
      Coercion natval : nat >-> Value. 
      (* TODO: Learn coertions correctly.. 
      Is there a way to make this more concise?
      That is, can we make the above thing in one line?
      Can I do reversible / bidirectional coertions?
      There was some limitation also, I think*)

      Variable (v1 v2 v3 v4 : VarName).


      Notation "v == v'" := (var_eq_dec v v')(at level 10).
      Print Notation "_ == _".
 
      Let ex1 : Store := fun _ => 5.
      Let ex2 : Store := fun v => 
        if v == v1 then 4 else 
        if v == v2 then 97 else 
        if v == v3 then 43 else 
        if v == v4 then 0 else 
        42.

      Set Printing Coercions. Print ex2. Unset Printing Coercions.
    End example.
    Fail Print Notation "_ == _".


    (* TODO: Have input vars, etc. *)

    Inductive LanguageCommand : Type :=
      | assignment (v : VarName) (f : Store -> Value)  (* Mixing syntax and semantics like a pro *)
      | input (v : VarName)
      | output (v : VarName).

    (* These are locally defined notations. *)
    Notation " x ← f " := (assignment x f) (at level 50).
    Notation " ? x  " := (input x) (at level 50).
    Notation " ! x  " := (output x) (at level 50).

    Definition LanguageProgram := list LanguageCommand. (* Only straightline code for now *)

    Section atk_sem.
      Variable attack_level : Label.
      Let attack_conf :=  (conf attack_level).
      Let attack_int :=  (int attack_level).

      Section defs.
        Variable element_label : Label.  (* I feel like these could be typeclasses.. *)
        Let element_conf := (conf element_label).
        Let element_int := (int element_label).

        Definition Public : Prop := element_conf ≼c attack_conf. 
        Definition Secret : Prop := ~Public.  

        Definition Untrusted : Prop := element_int ≼i attack_int.
        Definition Trusted   : Prop := ~Untrusted.

        Definition PublicTrusted   : Prop := Public /\ Trusted.
        Definition SecretTrusted   : Prop := Secret /\ Trusted.
        Definition PublicUntrusted : Prop := Public /\ Untrusted.
        Definition SecretUntrusted : Prop := Secret /\ Untrusted.

      End defs.

      Definition FullStore := Storeview (fun _ => True).
      (* Is it possible to make this x a Variable? *)
      Definition PubStore := Storeview (fun x => Public (var_lbl x)).
      Definition PUStore := Storeview (fun x => PublicTrusted (var_lbl x)).
      Definition SUStore := Storeview (fun x => SecretUntrusted (var_lbl x)).


      Section atk_code.
        (* An attacker has memory. *)
        Variable AttackerMem : Type.
        Record AttackSnippet := {
         (* How do the public untrusted values get transformed? *)
          pu_trans_code : AttackerMem -> PubStore -> PUStore;

         (* What information is the attacker learning for themselves? *)
          leak_code : AttackerMem -> PubStore -> list Value; 

         (* How is the attacker memory changed? *)
          mem_code : AttackerMem -> PubStore -> AttackerMem; 

         (* How do the secret untrusted values get transformed? *)
          su_trans_code : AttackerMem -> FullStore -> SUStore;
        }.

        Inductive AttackedLanguageCommand : Type :=  
        |  code (c : LanguageCommand)
        |  atk (a : AttackSnippet)
        . 
        (* Could I coerce LanguageCommand into AttackedLanguageCommand
          Coercion code : LanguageCommand >-> AttackedLanguageCommand.
          This needs to be exported, and things..
        *)

        Definition AttackedProgram := list AttackedLanguageCommand.

      End atk_code.
    End atk_sem.
  End varval. 
End po_ctx.















Module AttackSem.




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


    Section attackermem.
      Variable AtkMem : Set.

      Inductive AtkSnipEval : 
        Store -> (* Input store *)
        AtkMem -> (* Attacker memory*)
        AttackSnippet (AtkMem) ->  (* Command to run *)
        list Value ->  (* Leaked data *)
        Store ->  (* Resulting store *)
        AtkMem -> (* Attacker memory*)
        Prop := 
        | atk_eval (store new_store combined_view (* Make it exists?*) pu_tr su_tr leak_fn  : _) : 
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
