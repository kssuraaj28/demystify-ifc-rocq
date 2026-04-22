Require ssreflect.
Import ssreflect.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section var_lbl.
  #[local] Set Primitive Projections. (* TODO: All records need to have this? Maybe in prelude? *)
  (* 4 point lattice *) (* TODO: Maybe this should go elsewhere  *)
  Record Label: Type := mk_lbl {
    untrusted : bool;  (* The variable is maulable *)
    public: bool
  }.
End var_lbl.

Definition flows_to_conf (pubfrom pubto: bool) : bool :=
  match pubfrom, pubto with 
  | false, true => false (* secret to public *)
  | _, _ => true
  end.

Definition flows_to_int (untrfrom untrto: bool) : bool :=
  match untrfrom, untrto with 
  | true, false => false (* Untrusted to trusted *)
  | _, _ => true
  end.

Section flows.
  Open Scope bool_scope.
  Definition flows_to (lfrom lto: Label) : bool :=
    let: mk_lbl untrfrom pubfrom := lfrom in 
    let: mk_lbl untrto pubto := lto in 
    (flows_to_int untrfrom untrto) && (flows_to_conf pubfrom pubto).
End flows.


Module Notations.
  Notation "from ⊑ to"  := (flows_to from to) (at level 20). (* TODO: Why does || in Init.Datatypes not have this level?  *)
  Notation "to ⊒ from"  := (flows_to from to) (at level 20, only parsing). 

  Check (_ ⊑ _).  Check (_ ⊒ _).
End Notations.
