Require ssreflect ssrbool ssrfun.
Import ssreflect ssrbool ssrfun.

From Ltac2 Require Import Ltac2.
Require Tacs Lattice4pt.
Import Tacs Lattice4pt Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

#[local] Open Scope bool_scope.

(* The full security lattice is the product P × P over an abstract principal
   lattice P, where *more powerful principals are lower in P*. A label (c, i)
   pairs a confidentiality principal c with an integrity principal i. The
   information-flow order is P^op × P (confidentiality flipped). *)

Class PrincipalLatticePrm := {
  P : Type;
  leqP : P -> P -> bool;
  meetP : P -> P -> P;
  joinP : P -> P -> P;
  topP : P;
  botP : P;
  leqP_refl : forall x, leqP x x;
  leqP_trans : forall x y z, leqP x y -> leqP y z -> leqP x z;
  leqP_antisym : forall x y, leqP x y -> leqP y x -> x = y;
  leqP_meet : forall x y z, leqP z (meetP x y) = leqP z x && leqP z y;  (* glb *)
  leqP_join : forall x y z, leqP (joinP x y) z = leqP x z && leqP y z;  (* lub *)
  leqP_bot : forall x, leqP botP x;
  leqP_top : forall x, leqP x topP;
}.

(* Bridges between the 4-point primitives and boolean implication: they keep the
   projection proofs short. flows_to_int / flows_to_conf live at the top level of
   Lattice4pt. *)
Lemma flows_to_intE u1 u2 : flows_to_int u1 u2 = (u1 ==> u2).
Proof. case: u1; case: u2=> //. Qed.

Lemma flows_to_confE p1 p2 : flows_to_conf p1 p2 = (p2 ==> p1).
Proof. case: p1; case: p2=> //. Qed.

Section full_lattice.
  Context `{!PrincipalLatticePrm}.

  Definition FLabel : Type := P * P.
  Definition conf (l : FLabel) : P := fst l.
  Definition integ (l : FLabel) : P := snd l.

  (* Information-flow order (P^op × P): confidentiality may only increase
     (become less powerful / more secret), integrity may only decrease. *)
  Definition fflows_to (l1 l2 : FLabel) : bool :=
    leqP (conf l2) (conf l1) && leqP (integ l1) (integ l2).

  Definition fjoin (l1 l2 : FLabel) : FLabel :=
    (meetP (conf l1) (conf l2), joinP (integ l1) (integ l2)).

  (* A label is uncompromised (robust) when its writers are at least as powerful
     as its readers: integ ≤_P conf. *)
  Definition uncompromised (l : FLabel) : bool := leqP (integ l) (conf l).

  (* Meet / join bounds, derived from the lub/glb characterisations. *)
  Lemma meet_le_l x y : leqP (meetP x y) x.
  Proof. move: (leqP_meet x y (meetP x y)); rewrite (leqP_refl (meetP x y))=> /esym /andP[Hl _]; exact: Hl. Qed.

  Lemma meet_le_r x y : leqP (meetP x y) y.
  Proof. move: (leqP_meet x y (meetP x y)); rewrite (leqP_refl (meetP x y))=> /esym /andP[_ Hr]; exact: Hr. Qed.

  Lemma join_ge_l x y : leqP x (joinP x y).
  Proof. move: (leqP_join x y (joinP x y)); rewrite (leqP_refl (joinP x y))=> /esym /andP[Hl _]; exact: Hl. Qed.

  Lemma join_ge_r x y : leqP y (joinP x y).
  Proof. move: (leqP_join x y (joinP x y)); rewrite (leqP_refl (joinP x y))=> /esym /andP[_ Hr]; exact: Hr. Qed.

  Lemma fflows_to_refl l : fflows_to l l.
  Proof. apply/andP; split; exact: leqP_refl. Qed.

  Lemma fflows_to_trans l1 l2 l3 : fflows_to l1 l2 -> fflows_to l2 l3 -> fflows_to l1 l3.
  Proof.
    rewrite /fflows_to=> /andP[Hc1 Hi1] /andP[Hc2 Hi2]; apply/andP; split.
    - exact: (leqP_trans _ _ _ Hc2 Hc1).
    - exact: (leqP_trans _ _ _ Hi1 Hi2).
  Qed.

  Lemma fjoin_flow l1 l2 l3 :
    fflows_to (fjoin l1 l2) l3 = fflows_to l1 l3 && fflows_to l2 l3.
  Proof.
    rewrite /fflows_to /fjoin /conf /integ /= leqP_meet leqP_join.
    rewrite -!andbA; congr (_ && _); rewrite andbCA //.
  Qed.

  Lemma fjoin_mono_r l a b : fflows_to a b -> fflows_to (fjoin l a) (fjoin l b).
  Proof.
    rewrite /fflows_to /fjoin /conf /integ /= => /andP[Hc Hi]; apply/andP; split.
    - rewrite leqP_meet; apply/andP; split.
      + exact: meet_le_l.
      + exact: (leqP_trans _ _ _ (meet_le_r _ _) Hc).
    - rewrite leqP_join; apply/andP; split.
      + exact: join_ge_l.
      + exact: (leqP_trans _ _ _ Hi (join_ge_r _ _)).
  Qed.

  (* Lowering a label can only help robustness: integ falls, conf rises. *)
  Lemma uncompromised_mono a b : fflows_to a b -> uncompromised b -> uncompromised a.
  Proof.
    rewrite /fflows_to /uncompromised=> /andP[Hc Hi] Hb.
    apply: (leqP_trans _ _ _ Hi). apply: (leqP_trans _ _ _ Hb Hc).
  Qed.

  Lemma uncompromised_anti l1 l2 x :
    fflows_to l2 l1 -> uncompromised (fjoin x l1) -> uncompromised (fjoin x l2).
  Proof. move=> Hl. apply: uncompromised_mono. exact: fjoin_mono_r. Qed.

  (* Attacker: a pair of principals with a_c ≤_P a_i (confidentiality at least as
     powerful as integrity). a_c <_P a_i is the semi-honest / passive attacker. *)
  Record Attacker := { atk_c : P; atk_i : P; atk_le : leqP atk_c atk_i }.

  (* Componentwise projection of a full label to the 4-point lattice: visible iff
     the attacker controls the confidentiality principal; corruptible iff it
     controls the integrity principal. *)
  Definition to4pt (A : Attacker) (l : FLabel) : Lattice4pt.Label :=
    mk_lbl (leqP (atk_i A) (integ l)) (leqP (atk_c A) (conf l)).

  Lemma to4pt_mono A l1 l2 :
    fflows_to l1 l2 -> flows_to (to4pt A l1) (to4pt A l2).
  Proof.
    rewrite /fflows_to /to4pt /flows_to /= flows_to_intE flows_to_confE=> /andP[Hc Hi].
    apply/andP; split; apply/implyP=> H.
    - exact: (leqP_trans _ _ _ H Hi).
    - exact: (leqP_trans _ _ _ H Hc).
  Qed.

  Lemma to4pt_join_le A l1 l2 :
    flows_to (join (to4pt A l1) (to4pt A l2)) (to4pt A (fjoin l1 l2)).
  Proof.
    rewrite /to4pt /fjoin /join /flows_to /conf /integ /= flows_to_intE flows_to_confE.
    apply/andP; split; apply/implyP.
    - move=> /orP[H|H].
      + exact: (leqP_trans _ _ _ H (join_ge_l _ _)).
      + exact: (leqP_trans _ _ _ H (join_ge_r _ _)).
    - move=> H; apply/andP; split.
      + exact: (leqP_trans _ _ _ H (meet_le_l _ _)).
      + exact: (leqP_trans _ _ _ H (meet_le_r _ _)).
  Qed.
End full_lattice.

Module Notations.
  Notation "from ⊑ to" := (fflows_to from to) (at level 20).
  Notation "to ⊒ from" := (fflows_to from to) (at level 20, only parsing).
  Infix "⊔" := fjoin (at level 20).
End Notations.

(* Sanity: the abstract principal lattice is inhabited. The two-point lattice
   over bool — implb as the order, with false the most powerful principal —
   satisfies every axiom, so the development does not rest on a vacuous class.
   With a confidentiality principal more powerful than the integrity one
   (false ≤ true), this is exactly the semi-honest attacker. *)
Section sanity.
  Definition bool_plat : PrincipalLatticePrm.
  Proof.
    refine {| P := bool; leqP := implb; meetP := andb; joinP := orb;
              topP := true; botP := false |}.
    - case=> //.
    - move=> x y z; case: x; case: y; case: z=> //.
    - move=> x y; case: x; case: y=> //.
    - move=> x y z; case: x; case: y; case: z=> //.
    - move=> x y z; case: x; case: y; case: z=> //.
    - case=> //.
    - case=> //.
  Defined.

  Definition semihonest : @Attacker bool_plat.
  Proof. refine (@Build_Attacker bool_plat false true _). exact: erefl. Defined.

  (* The projection of a public-untrusted label (true public conf, true
     untrusted integ) lands on the 4-point public-untrusted point. *)
  Goal @to4pt bool_plat semihonest (true, true) = mk_lbl true true.
  Proof. exact: erefl. Qed.
End sanity.

Ltac2 this_cookbook () := this_cookbook_ ().
