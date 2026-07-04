Require ssreflect ssrbool ssrfun.
Import ssreflect ssrbool ssrfun.

From Ltac2 Require Import Ltac2.
Require Tacs Lattice4pt.
Import Tacs Lattice4pt Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

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

(* "Acts for" / "at least as powerful as": since more powerful principals are
   lower in P, A acts for B exactly when A ≤_P B. The glyph looks reversed but
   matches the standard decentralised-label notation (A ⪰ B = A speaks for B). *)
Notation "A ≽ B" := (leqP A B) (at level 70, no associativity).

(* flows_to_intE / flows_to_confE now live in Lattice4pt and arrive via Import. *)

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

  (* A label is uncompromised when its writers are at least as powerful as its
     readers: the integrity principal acts for the confidentiality principal. *)
  Definition uncompromised (l : FLabel) : bool := integ l ≽ conf l.

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

  (* Attacker label: a pair of principals with a_c acting for a_i (confidentiality
     at least as powerful as integrity). a_c <_P a_i is the semi-honest / passive
     attacker — it can read more than it can write. *)
  Record AttackerLabel := { atk_c : P; atk_i : P; reasonable_atk : atk_c ≽ atk_i }.

  (* Componentwise projection of a full label to the 4-point lattice: visible iff
     the attacker controls the confidentiality principal; corruptible iff it
     controls the integrity principal. *)
  Definition to4pt (A : AttackerLabel) (l : FLabel) : Lattice4pt.Label :=
    mk_lbl (atk_i A ≽ integ l) (atk_c A ≽ conf l).

  Lemma to4pt_mono A l1 l2 :
    fflows_to l1 l2 -> flows_to (to4pt A l1) (to4pt A l2).
  Proof.
    rewrite /fflows_to /to4pt /flows_to /= flows_to_intE flows_to_confE=> /andP[Hc Hi].
    apply/andP; split; apply/implyP=> H; apply: leqP_trans; eauto.
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

  (* A label flows to its join, so the join being uncompromised forces each
     component to be. *)
  Lemma fle_join_l l1 l2 : fflows_to l1 (fjoin l1 l2).
  Proof.
    rewrite /fflows_to /fjoin /conf /integ /=; apply/andP; split.
    - exact: meet_le_l.
    - exact: join_ge_l.
  Qed.

  Lemma uncompromised_join_l l1 l2 : uncompromised (fjoin l1 l2) -> uncompromised l1.
  Proof. exact: (uncompromised_mono _ _ (fle_join_l l1 l2)). Qed.

  (* When an endorse's source does NOT flow to its target in the 4-point
     projection (from ⋢ to), the source/target must be exactly the canonical
     public-untrusted / public-trusted points. The other "from ⋢ to" candidate
     (secret-untrusted source) is excluded because an uncompromised source is
     never secret-untrusted for a reasonable attacker (a_c ≤ a_i). *)
  Lemma to4pt_endorse_canonical (A : AttackerLabel) from to :
    conf from = conf to -> uncompromised from ->
    ~~ flows_to (to4pt A from) (to4pt A to) ->
    to4pt A from = mk_lbl true true /\ to4pt A to = mk_lbl false true.
  Proof.
    move=> Hc Hunc Hnf.
    rewrite /to4pt /flows_to /= flows_to_intE flows_to_confE Hc implybb andbT negb_imply in Hnf.
    move: Hnf => /andP[Huf Hut].
    have Hcf := Hunc; rewrite /uncompromised Hc in Hcf.
    have Hpub : leqP (atk_c A) (conf to) :=
      leqP_trans _ _ _ (reasonable_atk A) (leqP_trans _ _ _ Huf Hcf).
    split.
    - rewrite /to4pt Hc Huf Hpub //.
    - rewrite /to4pt (negbTE Hut) Hpub //.
  Qed.

  (* Dual for declassify: from ⋢ to forces secret-trusted source / public-trusted
     target (an uncompromised source is never secret-untrusted). *)
  Lemma to4pt_declassify_canonical (A : AttackerLabel) from to :
    integ from = integ to -> uncompromised from ->
    ~~ flows_to (to4pt A from) (to4pt A to) ->
    to4pt A from = mk_lbl false false /\ to4pt A to = mk_lbl false true.
  Proof.
    move=> Hi Hunc Hnf.
    rewrite /to4pt /flows_to /= flows_to_intE flows_to_confE Hi implybb andTb negb_imply in Hnf.
    move: Hnf => /andP[Hpt Hsf].
    have Hcf := Hunc; rewrite /uncompromised in Hcf.
    have Himp : leqP (atk_i A) (integ from) -> leqP (atk_c A) (conf from) :=
      fun Huf => leqP_trans _ _ _ (reasonable_atk A) (leqP_trans _ _ _ Huf Hcf).
    have Htf : ~~ leqP (atk_i A) (integ from).
    { apply/negP => Huf. apply: (negP Hsf). exact: Himp Huf. }
    split; rewrite /to4pt.
    - rewrite (negbTE Htf) (negbTE Hsf) //.
    - rewrite -Hi (negbTE Htf) Hpt //.
  Qed.
End full_lattice.

(* ⊑ / ⊔ deliberately reuse the 4-point glyphs but live in a separate Notations
   module, so a client imports at most one of Lattice4pt.Notations /
   FullLattice.Notations and there is no genuine clash. *)
Module Notations.
  Notation "from ⊑ to" := (fflows_to from to) (at level 20).
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

  Definition semihonest : @AttackerLabel bool_plat.
  Proof. refine (@Build_AttackerLabel bool_plat false true _). exact: erefl. Defined.

  (* The projection of a public-untrusted label (true public conf, true
     untrusted integ) lands on the 4-point public-untrusted point. *)
  Goal @to4pt bool_plat semihonest (true, true) = mk_lbl true true.
  Proof. exact: erefl. Qed.
End sanity.
