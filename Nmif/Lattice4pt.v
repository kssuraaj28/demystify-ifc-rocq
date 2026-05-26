Require ssreflect ssrbool.
Import ssreflect ssrbool.

From Ltac2 Require Import Ltac2.
Require Tacs.
Import Tacs Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

#[local] Open Scope bool_scope.

Section var_lbl.
  #[local] Set Primitive Projections. (* TODO: All records need to have this? Maybe in prelude? *)
  (* 4 point lattice *) (* TODO: Maybe this should go elsewhere  *)
  Record Label: Type := mk_lbl {
    untrusted : bool;  (* The variable is maulable *)
    public: bool
  }.
  Definition secret l := ~~ public l.
  Definition trusted l := ~~ untrusted l.

  Fact untrusted_mk u p : ltac2:(cbn_eq (untrusted (mk_lbl u p))).
  Proof. done. Qed.

  Fact public_mk u p : ltac2:(cbn_eq (public (mk_lbl u p))).
  Proof. done. Qed.
End var_lbl.

Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> untrusted_mk) "untrusted_mk" old.
Ltac2 Set this_cookbook_ as old := add_cookstep ltac1:(rewrite -> public_mk) "public_mk" old.

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

Definition flows_to (lfrom lto: Label) : bool :=
  let: mk_lbl untrfrom pubfrom := lfrom in 
  let: mk_lbl untrto pubto := lto in 
  (flows_to_int untrfrom untrto) && (flows_to_conf pubfrom pubto).
Definition join (l1 l2: Label) : Label := 
  let: mk_lbl untr1 pub1 := l1 in
  let: mk_lbl untr2 pub2 := l2 in
  mk_lbl (untr1 || untr2) (pub1 && pub2). (* Is this correct?*)

Module Notations.
  Notation "from ⊑ to"  := (flows_to from to) (at level 20). (* TODO: Why does || in Init.Datatypes not have this level?  *)
  Notation "to ⊒ from"  := (flows_to from to) (at level 20, only parsing). 

  Check (_ ⊑ _).  Check (_ ⊒ _).

  Infix "⊔" := join (at level 20).
End Notations.

Import Notations.
(* TODO: Maybe automation here as well *)
Lemma untr_join x p:
    untrusted (x ⊔ (mk_lbl true p)) = true.
Proof.
  case: p; case: x=> - [] [] //.
Qed.

Lemma pub_join x u:
    public (x ⊔ (mk_lbl u false)) = false.
Proof. case: x=> - [] [] //. Qed.

Lemma join_flow:
  forall l1 l2 l3,
    l1 ⊔ l2  ⊑  l3 = l1 ⊑ l3 && l2 ⊑ l3.
Proof. do 3 (case=> - [] [])=> //=. Qed.


Lemma join_assoc:
  forall l1 l2 l3,
    (l1 ⊔ l2) ⊔ l3  =  l1 ⊔ (l2 ⊔ l3).
Proof. case=> - [] [] //. Qed.

Lemma join_idem:
  forall l,  (l ⊔ l) = l.
Proof. case=> - [] [] //. Qed.

Lemma join_sym:
  forall l1 l2,  
    (l1 ⊔ l2)  =  (l2 ⊔ l1).
Proof. do 2 (case=> - [] [])=> //. Qed.

Lemma flows_to_trans:
  forall l1 l2 l3, l1 ⊑ l2 -> l2 ⊑ l3 -> l1 ⊑ l3.
Proof. do 3 (case=> - [] [])=> //. Qed.

Lemma join_mono_r:
  forall l a b, a ⊑ b -> (l ⊔ a) ⊑ (l ⊔ b).
Proof. do 3 (case=> - [] [])=> //. Qed.

(* TODO: This must be automated! *)
Lemma untrusted_false:
  forall l,
   untrusted l = false ->
   trusted l.
Proof.  case=> - [] [] //. Qed.

Lemma secret_false:
  forall l,
   secret l = false ->
   public l.
Proof.  case=> - [] [] //. Qed.

Lemma public_false:
  forall l,
   public l = false ->
   secret l.
Proof.  case=> - [] [] //. Qed.

Lemma trusted_false:
  forall l,
   trusted l = false ->
   untrusted l.
Proof.  case=> - [] [] //. Qed.

Lemma flows_from_untr:
  forall l1 l2,
    untrusted l1 -> l1 ⊑ l2 ->
    untrusted l2.
Proof. do 2 (case=> - [] [])=> //. Qed.

Lemma flows_from_sec:
  forall l1 l2,
    secret l1 -> l1 ⊑ l2 ->
    secret l2.
Proof. do 2 (case=> - [] [])=> //. Qed.

Lemma flows_to_tr:
  forall l1 l2,
    trusted l2 -> l1 ⊑ l2 ->
    trusted l1.
Proof. do 2 (case=> - [] [])=> //. Qed.

Lemma flows_to_pub:
  forall l1 l2,
    public l2 -> l1 ⊑ l2 ->
    public l1.
Proof. do 2 (case=> - [] [])=> //. Qed.

Lemma flows_to_pt l : l ⊑ mk_lbl false true -> l = mk_lbl false true.
Proof. case: l=> - [] [] //. Qed.

Ltac2 this_cookbook () := this_cookbook_ ().
