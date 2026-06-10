From Stdlib Require ssreflect.
Import ssreflect.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Class EventPrm := {
  Events : Type;
  stutter : Events;
}.

Section trace.
  Context `{!EventPrm}.

  CoInductive Trace : Type := tcons : Events -> Trace -> Trace.
End trace.

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

Notation "t1 ≈ t2" := (Trace_weq t1 t2) (at level 70, no associativity).

Section build.
  Context `{!EventPrm} {State : Type} (step : State -> State) (event : State -> Events).

  CoFixpoint build (s : State) : Trace := tcons (event s) (build (step s)).

  Lemma build_unfold s : build s = tcons (event s) (build (step s)).
  Proof.
    suff: (build s = match build s with tcons e t' => tcons e t' end)=> //.
    case: (build s)=> //.
  Qed.
End build.

Section bisim.
  Context `{!EventPrm} {S1 S2 : Type}
          (step1 : S1 -> S1) (event1 : S1 -> Events)
          (step2 : S2 -> S2) (event2 : S2 -> Events).

  Lemma trace_bisim (R : S1 -> S2 -> Prop) :
    (forall s1 s2, R s1 s2 ->
         (R (step1 s1) (step2 s2) /\ event1 s1 = event2 s2)
      \/ (R (step1 s1) s2 /\ event1 s1 = stutter)
      \/ (R s1 (step2 s2) /\ event2 s2 = stutter)) ->
    forall s1 s2, R s1 s2 -> Trace_weq (build step1 event1 s1) (build step2 event2 s2).
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
End bisim.
