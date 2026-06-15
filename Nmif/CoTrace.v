From Stdlib Require ssreflect.
Import ssreflect.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

(* Would be good to have this unbundled *)
Class EventPrm := {
  Events : Type;
  stutter : Events;
}.

Section trace.
  Context `{!EventPrm}.

  CoInductive Trace : Type := tcons : Events -> Trace -> Trace.
End trace.

Section build.
  Context `{!EventPrm} {State : Type} (step : State -> State) (event : State -> Events).

  CoFixpoint build (s : State) : Trace := tcons (event s) (build (step s)).

  Lemma build_unfold s : build s = tcons (event s) (build (step s)).
  Proof.
    suff: (build s = match build s with tcons e t' => tcons e t' end)=> //.
    case: (build s)=> //.
  Qed.
End build.

Section trace_weq.
  Context `{!EventPrm}.

  CoInductive Trace_weq : Trace -> Trace -> Prop :=
    | weq_match : forall e t1 t2,
        Trace_weq t1 t2 ->
        Trace_weq (tcons e t1) (tcons e t2)
    | weq_skip_l : forall t1 t2,
        Trace_weq t1 t2 ->
        Trace_weq (tcons stutter t1) t2
    | weq_skip_r : forall t1 t2,
        Trace_weq t1 t2 ->
        Trace_weq t1 (tcons stutter t2).

  Lemma Trace_weq_coind (R : Trace -> Trace -> Prop) :
    (forall t1 t2, R t1 t2 ->
         (exists e t1' t2',
            t1 = tcons e t1' /\ t2 = tcons e t2' /\ R t1' t2')
      \/ (exists t1', t1 = tcons stutter t1' /\ R t1' t2)
      \/ (exists t2', t2 = tcons stutter t2' /\ R t1 t2')) ->
    forall t1 t2, R t1 t2 -> Trace_weq t1 t2.
  Proof.
    move=> Hstep. cofix self=> t1 t2 /Hstep.
    case=> [[e [t1' [t2' [-> [-> HR]]]]]
           |[[t1' [-> HR]]
            |[t2' [-> HR]]]].
    - apply: weq_match. exact: self _ _ HR.
    - apply: weq_skip_l. exact: self _ _ HR.
    - apply: weq_skip_r. exact: self _ _ HR.
  Qed.
End trace_weq.

Notation "t1 ≈ʷ t2" := (Trace_weq t1 t2) (at level 70, no associativity).

Section trace_seq.
  Context `{!EventPrm}.

  CoInductive Trace_seq : Trace -> Trace -> Prop :=
    | seq_match : forall e t1 t2,
        Trace_seq t1 t2 ->
        Trace_seq (tcons e t1) (tcons e t2).

  Lemma Trace_seq_coind (R : Trace -> Trace -> Prop) :
    (forall t1 t2, R t1 t2 ->
       exists e t1' t2', t1 = tcons e t1' /\ t2 = tcons e t2' /\ R t1' t2') ->
    forall t1 t2, R t1 t2 -> Trace_seq t1 t2.
  Proof.
    move=> Hstep. cofix self=> t1 t2 /Hstep [e [t1' [t2' [-> [-> HR]]]]].
    apply: seq_match. exact: self _ _ HR.
  Qed.
End trace_seq.

Notation "t1 ≈ˢ t2" := (Trace_seq t1 t2) (at level 70, no associativity).

Section trace_lemmas.
  Context `{!EventPrm}.

  Lemma Trace_seq_inv {e t1 t2} :
    Trace_seq (tcons e t1) t2 -> exists t2', t2 = tcons e t2' /\ Trace_seq t1 t2'.
  Proof.
    move E: (tcons e t1)=> t H.
    case: H E=> e0 u1 u2 Hs [-> ->].
    exists u2; split=> //.
  Qed.

  Lemma weq_seq_trans t1 t2 t3 :
    t1 ≈ʷ t2 -> t2 ≈ˢ t3 -> t1 ≈ʷ t3.
  Proof.
    move=> Hw Hs.
    apply: (Trace_weq_coind (fun a c => exists b, Trace_weq a b /\ Trace_seq b c));
      [| exists t2; split=> //].
    move=> a c [b [Hab Hbc]].
    case: Hab Hbc=> [e a' b' Hab' | a' b' Hab' | a' b' Hab'] Hbc.
    - move: (Trace_seq_inv Hbc)=> [c' [-> Hb'c']].
      left. exists e, a', c'. split=> //. split=> //. exists b'; split=> //.
    - right; left. exists a'. split=> //. exists b'; split=> //.
    - move: (Trace_seq_inv Hbc)=> [c' [-> Hb'c']].
      right; right. exists c'. split=> //. exists b'; split=> //.
  Qed.
End trace_lemmas.


Section bisim.
  Context `{!EventPrm} {S1 S2 : Type}
          (step1 : S1 -> S1) (event1 : S1 -> Events)
          (step2 : S2 -> S2) (event2 : S2 -> Events).

  Lemma trace_wbisim (R : S1 -> S2 -> Prop) :
    (forall s1 s2, R s1 s2 ->
         (R (step1 s1) (step2 s2) /\ event1 s1 = event2 s2)
      \/ (R (step1 s1) s2 /\ event1 s1 = stutter)
      \/ (R s1 (step2 s2) /\ event2 s2 = stutter)) ->
    forall s1 s2, R s1 s2 ->  (build step1 event1 s1) ≈ʷ (build step2 event2 s2).
  Proof.
    move=> Hstep s1 s2 HR.
    pose R' (t1 t2 : Trace) :=
      exists s1' s2', R s1' s2' /\ t1 = build step1 event1 s1' /\ t2 = build step2 event2 s2'.
    apply: (Trace_weq_coind R').
    - move=> t1 t2 [s1' [s2' [HRss [-> ->]]]].
      case: (Hstep s1' s2' HRss)=> [[HR' Heq]
                                   |[[HR' Hstut]
                                    |[HR' Hstut]]].
      + left. exists (event1 s1'),
          (build step1 event1 (step1 s1')), (build step2 event2 (step2 s2')).
        split; [rewrite build_unfold //|].
        split; [rewrite build_unfold -Heq //|].
        exists (step1 s1'), (step2 s2'). split=> //.
      + right; left. exists (build step1 event1 (step1 s1')).
        split; [rewrite build_unfold Hstut //|].
        exists (step1 s1'), s2'. split=> //.
      + right; right. exists (build step2 event2 (step2 s2')).
        split; [rewrite build_unfold Hstut //|].
        exists s1', (step2 s2'). split=> //.
    - exists s1, s2. split=> //.
  Qed.

  Lemma trace_sbisim (R : S1 -> S2 -> Prop) :
    (forall s1 s2, R s1 s2 -> R (step1 s1) (step2 s2) /\ event1 s1 = event2 s2) ->
    forall s1 s2, R s1 s2 -> (build step1 event1 s1) ≈ˢ (build step2 event2 s2).
  Proof.
    move=> Hstep s1 s2 HR.
    pose R' (t1 t2 : Trace) :=
      exists s1' s2', R s1' s2' /\ t1 = build step1 event1 s1' /\ t2 = build step2 event2 s2'.
    apply: (Trace_seq_coind R').
    - move=> t1 t2 [s1' [s2' [HRss [-> ->]]]].
      case: (Hstep s1' s2' HRss)=> HR' Heq.
      exists (event1 s1'),
        (build step1 event1 (step1 s1')), (build step2 event2 (step2 s2')).
      split; [rewrite build_unfold //|].
      split; [rewrite build_unfold -Heq //|].
      exists (step1 s1'), (step2 s2'). split=> //.
    - exists s1, s2. split=> //.
  Qed.
End bisim.
