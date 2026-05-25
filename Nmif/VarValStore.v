From Stdlib Require ssreflect ssrbool FunctionalExtensionality. 
Import ssreflect ssrbool FunctionalExtensionality.

Require Util Tacs.
Import Util.DecEq.

Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Class VarPrm := {Vars : Type ; vars_deceq :: DecEq Vars}. 
Class ValPrm := {Vals : Type; val_ne : Vals}.

Section store.
  Import Util.DecEq.Notations.
  Context `{!VarPrm, !ValPrm}.

  Definition Store := Vars -> Vals.
  Definition update_to_store (st : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if (v =? v') is true then vl else st v'.  (* The double colon in vars_deceq is needed here. *)

  (* I don't get dependent types :(. Maybe once I am good, I will use them *)
  Definition StoreView := Vars -> option Vals.

  Definition store_to_view (p: pred Vars) (s: Store) : StoreView :=
    fun v => if p v is true then Some (s v) else None.

  Definition view_to_store (sv: StoreView) (s_old: Store) : Store :=
    fun v => if sv v is (Some vl) then vl else s_old v. 
End store.

(* Without dependent types, you lose the cool type inference.. *)
Module Notations.
  (* TODO: Perhaps we want to have something like a notation key / delimiter?  *)
  Notation "⟨ s | p ⟩" := (store_to_view p s).
  Notation "⟨ sv → s ⟩" := (view_to_store sv s). (* TODO: Some warning here. *)
  Section test.
    Context `{!VarPrm, !ValPrm}.
    Variable (s: Store) (sv: StoreView) (p : pred Vars).
    Check ⟨ s | p ⟩.
    Check ⟨ sv → s ⟩.
  End test.
End Notations.

Section thms.
  Import Notations.
  Context `{!VarPrm, !ValPrm}.

  Theorem storeview_eq s1 s2 p inp:
      ⟨ s1 | p ⟩ = ⟨ s2 | p ⟩ -> p inp -> 
      s1 inp = s2 inp.
  Proof.
    rewrite/⟨_|_⟩.
    move=> /equal_f/(_ inp)/[swap]->[] //.
  Qed.

  Lemma update_storeview_nochange p st var val:
      p var = false ->
      ⟨ update_to_store st var val | p⟩ = ⟨ st | p ⟩.
  Proof.
    move=>h; apply/functional_extensionality=> ?.
    rewrite/⟨_|_⟩. case pe: (p _)=> //.
    congr (_ _). rewrite /update_to_store.
    case (dec_eq _ _)=> //.
    congruence.
  Qed.

  Lemma update_same_varval s1 s2 vr vl p:
    ⟨ s1 | p ⟩ = ⟨ s2 | p ⟩ ->
    ⟨update_to_store s1 vr vl | p⟩ = ⟨update_to_store s2 vr vl | p⟩.
  Proof.
    move=> h; apply/functional_extensionality=> inp.
    rewrite/⟨_|_⟩. case pe: (p _)=> //.
    congr (_ _). rewrite /update_to_store.
    case (dec_eq _ _)=> //=> _.
    move: h=> /equal_f/(_ inp).
    rewrite/⟨_|_⟩ pe=> - [] //.
  Qed.
End thms.
