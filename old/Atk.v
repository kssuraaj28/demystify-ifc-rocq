From NMIF Require Import Common Store.
Import Common.Notations.

Module Syntax.
  Section atklvl.
    Context {p : PartOrderParam}. 
    Class AtkLblParam := {attack_level : Label}. (* TODO: Is there an implicit coerction into this? *)
  End atklvl.

  Section defs.
    Context {p : PartOrderParam} {atkprm : AtkLblParam}.
    Let attack_conf :=  (conf attack_level).
    Let attack_int :=  (int attack_level).

    Section defs.
      Variable element_label : Label. 
      Let element_conf := (conf element_label).
      Let element_int := (int element_label).

      Definition Public : Prop := element_conf ≼c attack_conf. 
      Definition Secret : Prop := ~Public.  
      Definition Untrusted : Prop := element_int ≼i attack_int.
      Definition Trusted   : Prop := ~Untrusted.
    End defs.
  End defs.


  (* Attackers have private memory. *)
  Class AtkMemParam : Type := {AttackerMem : Type}.

  Section atk_code.
    Context {p : PartOrderParam} 
            {vars : VarParam} 
            {vals : ValueParam} 
            {atkprm : AtkLblParam} 
            {atkmem : AtkMemParam}.

    Let AllPred : VarPred := fun _ => 
      True.

    Let PubPred : VarPred := fun x => 
      Public (var_lbl x).

    Let PUPred : VarPred := fun x => 
      let x_lbl := var_lbl x in
      Public x_lbl /\ Untrusted x_lbl.

    Let SUPred : VarPred := fun x => 
      let x_lbl := var_lbl x in
      Secret x_lbl /\ Trusted x_lbl.

    Definition FullStore := Storeview AllPred.
    Definition PubStore := Storeview PubPred.
    Definition PUStore := Storeview PUPred.
    Definition SUStore := Storeview SUPred.

    (* Can I make this a class (temporarily)? TODO.. *)
    Record AttackSnippet := {
     (* How do the secret untrusted values get transformed? *)
      su_trans_code : AttackerMem -> FullStore -> SUStore;

     (* How do the public untrusted values get transformed? *)
      pu_trans_code : AttackerMem -> PubStore -> PUStore;

     (* How is the attacker memory changed? *)
      mem_code : AttackerMem -> PubStore -> AttackerMem; 

     (* What information is the attacker learning for themselves? *)
      leak_code : AttackerMem -> PubStore -> list Value; 
    }.
  End atk_code.
End Syntax.

Module Semantics.
  Section ev.
    Context {vals : ValueParam}. (* I wonder if it is possible to throw an error when there are useless things in the context *)
    Inductive Event : Type :=
      leak_ev (vs: list Value).
  End ev.

  Section atkeval. 
    Import Syntax.

    Context {p: PartOrderParam} 
            {vars : VarParam} 
            {vals : ValueParam}
            {atkprm : AtkLblParam}
            {atkmem : AtkMemParam}.


    Inductive AtkSnipEval (atk_code : AttackSnippet) :
                  Store -> (* Input store *)
                  Store -> (* Output store *)     
                  AttackerMem -> (* Input attacker memory *)
                  AttackerMem -> (* Output attacker memory *)
                  Event -> (* Leaked information *)
                  Prop := 

        atk_snip_eval : 
            forall (store : Store) (amem : AttackerMem),
            (* TODO: Can I refactor this? Notation? *)
            let sustore' := su_trans_code atk_code amem (extract_storeview store _) in 
            let pustore' := pu_trans_code atk_code amem (extract_storeview store _) in
            let amem' := mem_code atk_code amem (extract_storeview store _) in 
            let leak := leak_code atk_code amem (extract_storeview store _) in 

            forall (supustore' : _), 
            CombinedStoreView sustore' pustore' supustore' ->

            forall (store' : _), (* Here, you might want to show that this is deterministic. *)
            UpdatedStore store supustore' store' ->

            _ _ store store' amem amem' (leak_ev leak).

  End atkeval.

End Semantics.
