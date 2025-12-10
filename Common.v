From NMIF Require Import PartialOrder.

(* I think that this is probably the better way? *)
Class PartOrderParam : Type := {
  conf_po : PartialOrder;
  int_po : PartialOrder;
 }.

Section label. 
  Context {params : PartOrderParam}. 

  Definition ConfCarrier := Carrier (data conf_po).
  Definition ConfOrder := Ordering (data conf_po). 

  Definition IntCarrier := Carrier (data int_po).
  Definition IntOrder := Ordering (data int_po). 

  Record Label : Type := { 
    conf : ConfCarrier;
    int : IntCarrier
    }.
End label.


Class ValueParam : Type := {
  Value : Type ;
  val_eq_dec : forall v v' : Value, {v = v'} + {v <> v'} ;
  }.


Inductive VarCategory : Type := inp_var | out_var | internal_var. 
Definition varcat_eq_dec : forall k k' : VarCategory, {k = k'} + {k <> k'}. Proof.  decide equality. Defined.

Section varname.
  Context {p : PartOrderParam}. (* TODO:  What happens when this is not an implicit parameter? What about `  *)

  Class VarParam : Type := {
    VarName : Type ;
    var_lbl : VarName -> Label ; 
    var_kind : VarName -> VarCategory ; 
    var_eq_dec : forall v v' : VarName, {v = v'} + {v <> v'} ; (* Do I need this actually? *)
    }.

End varname.

Section varsubset.
  Context {p: PartOrderParam} {vars: VarParam}. 

  Definition VarPred := VarName -> Prop.
  Definition VarSubset (P : VarPred) := {v : VarName | P v}.
End varsubset.


Module Notations.
  (* Should I export? TODO: *)
  Notation "x '≼c' y" := (ConfOrder x y)(at level 70). Check _ ≼c _. 

  Notation "x '≼i' y" := (IntOrder x y)(at level 70). Check _ ≼i _.

  Notation "⟨ l1 , l2 ⟩" := {| conf := l1 ; int := l2 |}. Check ⟨ _ , _ ⟩.
End Notations.
