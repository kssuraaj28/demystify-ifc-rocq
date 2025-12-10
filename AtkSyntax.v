From NMIF Require Import Common Store Syntax.
Import CommonNotations LangSyntaxNotations.

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
