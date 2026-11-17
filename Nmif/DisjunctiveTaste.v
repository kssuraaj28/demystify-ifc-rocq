From Stdlib Require List ssreflect ssrfun ssrbool Strings.String.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.
 
Require Tacs Util VarValStore Syntax FullLattice FullTypeSystem Attacker Noninterference Semantics CoTrace WfFinisher.
Import Util VarValStore FullLattice FullTypeSystem Nmif.Syntax Noninterference Semantics CoTrace WfFinisher.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Section secret_sharing.
  Context `{Attacker.AdvLeakPrm, ValPrm}.

  (* Need to annotate secret1 and secret2 with fancy policies *)
  Variant Var := secret1 | secret2 | public.

  #[local] Instance ss_vals : ValPrm := {| Vals := list nat; val_ne := [] |}.


  #[refine, local] Instance ss_vars : VarPrm := {| Vars := Var |}.
  Proof. constructor; rewrite /decidable; decide equality. Defined.

  #[local] Instance alvl : Attacker.AdvLvlPrm := 
    fun v => Lattice4pt.ptlbl.  (* All variables are trusted, because secret sharing is about secrets *)

  Definition Attacker := Attacker.Attacker.

  (* 
    We will define secrecy restrctions as predicates, 
    which will enable us to take unions.
    TODO: I wonder how I could do it with +
   *)


  Section atkpreds.
    Variables (a: Attacker).
    Notation ainit := (Attacker.init_fn (Attacker.init a)).
    Notation astep := (Attacker.post_cmd_action (Attacker.step a)).

    (* The ideal attack gets to learn public + svar initially *)
    Definition idlatk_meta (svar : Vars) : Prop :=
      Noninterfering (fun st => (st public, st svar)) ainit id /\  (* Constant function *)
      forall ast, Noninterfering (fun st => tt) (astep ast) id.

    Definition idlatk_s1 := idlatk_meta secret1.
    Definition idlatk_s2 := idlatk_meta secret2.
    Definition idlatk_disjunctive := idlatk_s1 \/ idlatk_s2.

    (* The real attack gets to learn public always *)
    Definition rlatk : Prop :=
      Noninterfering (fun st => st public) ainit id /\  (* Constant function *)
      forall ast, Noninterfering (fun st => st public) (astep ast) id.
  End atkpreds.


  (* Real--ideal definition of secret sharing *)
  Definition ss_policy (p: Prog) : Prop :=
    forall ratk, rlatk ratk -> 
    exists iatk, idlatk_disjunctive iatk /\
      forall st,  ⟦ p | ratk ⟧ st  ≈ˢ ⟦ p  | iatk ⟧ st.


  (* Examples *)
  Definition p1 : Prog :=
    [assign (exp_assign (secret1, secret2 , fun s1 s2 => s1) public)]. 

  (* A bunch of AI slop that makes me sad *)
  Section slop.
    Variable (ratk : Attacker).
    Hypothesis (rok : rlatk ratk).
    Notation RS := (Attacker.States ratk).
    Notation rinit := (Attacker.init_fn (Attacker.init ratk)).
    Notation rstep := (Attacker.step ratk).

    Lemma rpre_pt a st x : Attacker.pre_cmd_action rstep a st x = st x.
    Proof. apply: storeview_eq; [wf_finisher| ]; done. Qed.

    Lemma rpost_public a s1 s2 : s1 public = s2 public ->
      Attacker.post_cmd_action rstep a s1 = Attacker.post_cmd_action rstep a s2.
    Proof. exact: rok.2. Qed.

    (* The ideal attacker remembers the initial [secret1], which [p1] copies
       into [public], and feeds it to the real attacker's step. *)
    Definition i_post (ast : RS * Vals) (_ : Store) : (RS * Vals) * nat :=
      let: (a, v) := ast in
      let: (a', n) := Attacker.post_cmd_action rstep a (fun _ => v) in ((a', v), n).

    Definition i_init_fn (st : Store) : RS * Vals := (rinit st, st secret1).

    Lemma i_init_wf : Noninterfering (store_to_view Attacker.is_public) i_init_fn id.
    Proof. move=> s1 s2 h. f_equal. apply/store_eq_ext=> ?. apply:storeview_eq; [eassumption|]; done. Qed. 

    Definition i_init : Attacker.AdvInit (AtkStates := RS * Vals) :=
      {| Attacker.init_fn := i_init_fn; Attacker.init_wf := i_init_wf |}.

    Definition i_step : Attacker.AdvNextStep (AtkStates := RS * Vals).
    Proof.
      refine {|
        Attacker.pre_cmd_action ast := Attacker.pre_cmd_action rstep ast.1;
        Attacker.pre_cmd_event ast := Attacker.pre_cmd_event rstep ast.1;
        Attacker.post_cmd_action := i_post;
      |}.
      - move=> ast. exact: (Attacker.pre_cmd_wf_int rstep ast.1).
      - move=> ast. exact: (Attacker.pre_cmd_wf_conf rstep ast.1).
      - move=> ast s1 s2 _. reflexivity.
    Defined.

    Definition iatk : Attacker := Attacker.mk_attacker (RS * Vals) i_init i_step.

    Lemma iatk_s1 : idlatk_s1 iatk.
    Proof.
      split.
      - move=> s1 s2 [hp hs]. rewrite /= /i_init_fn hs. f_equal. exact: (rok.1 s1 s2 hp).
      - move=> ast s1 s2 _. reflexivity.
    Qed.

    Lemma substeps_cont n :
      map (fun '(oc, a) => mk_atkcmd a oc)
        (Util.List.combine_extend2 (map Some []) (repeat true n) None false)
      = repeat (mk_atkcmd true None) n.
    Proof. elim: n=> [|n ih] //=. rewrite ih //. Qed.

    Definition c1 : Cmd := assign (exp_assign (secret1, secret2 , fun s1 s2 => s1) public).

    (* Same commands, store and real state; the ideal's extra value is
       [secret1] before [c1] runs and [public] afterwards. *)
    Definition p1_rel (cf : Cfg (AtkStates := RS)) (cf' : Cfg (AtkStates := RS * Vals)) : Prop :=
      exists cmds st a v,
        cf = (cmds, (st, a)) /\ cf' = (cmds, (st, (a, v))) /\
        ((cmds = [mk_atkcmd true (Some c1)] /\ v = st secret1) \/
         (exists k, cmds = repeat (mk_atkcmd true None) k /\ st public = v)).

    Lemma p1_rel_event cmds st a v :
      event rstep (cmds, (st, a)) = event i_step (cmds, (st, (a, v))).
    Proof. case: cmds=> [|[isatk oc] rest] //. Qed.

    Lemma p1_bisim st : ⟦ p1 | ratk ⟧ st ≈ˢ ⟦ p1 | iatk ⟧ st.
    Proof.
      apply: (trace_sbisim _ _ _ _ p1_rel); cycle 1.
      { exists [mk_atkcmd true (Some c1)], st, (rinit st), (st secret1).
        split; [reflexivity|]. split; [reflexivity|]. left. split; reflexivity. }
      move=> cf cf' [cmds [s [a [v [-> [-> hph]]]]]].
      split; [|exact: p1_rel_event].
      case: hph=> [[-> ->] | [k [-> hv]]].
      - rewrite /step /= (rpost_public _ _ (fun _ => s secret1)); [exact: rpre_pt|].
        case: (Attacker.post_cmd_action rstep a _)=> a' n /=.
        rewrite app_nil_r substeps_cont.
        do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
        right. exists n. split; [reflexivity | exact: rpre_pt].
      - case: k=> [|k].
        + do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
          right. exists 0. split; [reflexivity | exact: hv].
        + rewrite /step /= (rpost_public _ _ (fun _ => v)); [rewrite rpre_pt; exact: hv|].
          case: (Attacker.post_cmd_action rstep a _)=> a' n /=.
          rewrite substeps_cont -repeat_app.
          do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
          right. exists (n + k). split; [reflexivity | rewrite rpre_pt; exact: hv].
    Qed.
  End slop.

  Example p1_secure1 : ss_policy p1.
  Proof.
    move=> ratk rok. exists (iatk ratk). split.
    - constructor; exact: iatk_s1.
    - exact: p1_bisim.
  Qed.

  Definition p2 : Prog :=
    [assign (exp_assign (secret1, secret2 , (fun s1 s2 => s1 ++ s2)) public)]. 

  Section slop.
    (* The real attacker announces [length public] as its substep count, so
       the second trace event is [mk_terminate_event] iff [secret1 ++ secret2]
       is empty. An ideal attacker only knows [public] and one secret. *)
    Definition r2_post (_ : unit) (st : Store) : unit * nat := (tt, length (st public)).

    Definition r2_init : Attacker.AdvInit (AtkStates := unit).
    Proof. refine {| Attacker.init_fn _ := tt |}. move=> ? ? _. reflexivity. Defined.

    Definition r2_step : Attacker.AdvNextStep (AtkStates := unit).
    Proof.
      refine {|
        Attacker.pre_cmd_action _ st := st;
        Attacker.pre_cmd_event _ := None;
        Attacker.post_cmd_action := r2_post;
      |}.
      - move=> ? st. reflexivity.
      - move=> ? s1 s2 h. exact: h.
      - move=> ? s1 s2 h. have hp : s1 public = s2 public; [apply: (storeview_eq _ _ _ _ h); done|].
        rewrite /= /r2_post hp. reflexivity.
    Defined.

    Definition ratk2 : Attacker := Attacker.mk_attacker unit r2_init r2_step.

    Lemma ratk2_ok : rlatk ratk2.
    Proof.
      split.
      - move=> ? ? _. reflexivity.
      - move=> ? s1 s2 h. rewrite /= /r2_post h. reflexivity.
    Qed.

    (* The second event of a trace. *)
    Definition ev1 `{EventPrm} (t : Trace) : Events :=
      match t with tcons _ (tcons e _) => e end.

    Lemma ev1_seq `{EventPrm} t1 t2 : t1 ≈ˢ t2 -> ev1 t1 = ev1 t2.
    Proof.
      case: t1=> e t. case: t=> e' t.
      move=> /Trace_seq_inv [t2' [-> /Trace_seq_inv [t2'' [-> _]]]].
      reflexivity.
    Qed.

    Lemma ev1_trace p a st :
      ev1 (⟦ p | a ⟧ st) =
      event (Attacker.step a) (step (Attacker.step a) (init_cfg p (Attacker.init a) st)).
    Proof. rewrite /trace /cfg_trace build_unfold build_unfold. reflexivity. Qed.

    (* An ideal attacker's second event depends only on its initial state. *)
    Lemma idl_ev1 iatk svar st1 st2 :
      idlatk_meta iatk svar -> st1 public = st2 public -> st1 svar = st2 svar ->
      ev1 (⟦ p2 | iatk ⟧ st1) = ev1 (⟦ p2 | iatk ⟧ st2).
    Proof.
      move=> [hinit hpost] hp hs.
      have hi : Attacker.init_fn (Attacker.init iatk) st1 = Attacker.init_fn (Attacker.init iatk) st2.
      { apply: hinit. rewrite /= hp hs. reflexivity. }
      have hq a s : Attacker.post_cmd_action (Attacker.step iatk) a s =
                    Attacker.post_cmd_action (Attacker.step iatk) a (fun _ => []).
      { exact: (hpost a s _ erefl). }
      rewrite !ev1_trace /init_cfg hi /step /= hq.
      rewrite [Attacker.post_cmd_action _ _ (update_to_store _ _ _)]hq.
      case: (Attacker.post_cmd_action _ _ _)=> a' [|n]; reflexivity.
    Qed.

    Definition stA : Store := fun _ => [].
    Definition stB : Store := fun v => if v is secret2 then [0] else [].
    Definition stC : Store := fun v => if v is secret1 then [0] else [].

    Lemma r2_evA : ev1 (⟦ p2 | ratk2 ⟧ stA) = mk_terminate_event.
    Proof. rewrite ev1_trace. reflexivity. Qed.

    Lemma r2_evB : ev1 (⟦ p2 | ratk2 ⟧ stB) = mk_acmd_evnt None None.
    Proof. rewrite ev1_trace. reflexivity. Qed.

    Lemma r2_evC : ev1 (⟦ p2 | ratk2 ⟧ stC) = mk_acmd_evnt None None.
    Proof. rewrite ev1_trace. reflexivity. Qed.
  End slop.

  Example p2_insecure :  ~ ss_policy p2.
  Proof.
    move=> /(_ ratk2 ratk2_ok) [iatk [hidl hsim]].
    move: (ev1_seq _ _ (hsim stA)). rewrite r2_evA=> hA.
    case: hidl=> hidl.
    - move: (ev1_seq _ _ (hsim stB)). rewrite r2_evB=> hB.
      move: (idl_ev1 _ _ stA stB hidl erefl erefl). rewrite -hA -hB. done.
    - move: (ev1_seq _ _ (hsim stC)). rewrite r2_evC=> hC.
      move: (idl_ev1 _ _ stA stC hidl erefl erefl). rewrite -hA -hC. done.
  Qed.

End secret_sharing.
