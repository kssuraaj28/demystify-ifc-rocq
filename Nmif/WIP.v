(* Time to cook *)
From Stdlib Require Import ssreflect ssrbool List FunctionalExtensionality.
Import ListNotations.

From Ltac2 Require Import Ltac2.

Require Import Util VarValStore Syntax Semantics Attacker Util Noninterference Tacs. 
Import Util.DecEq Util.List. 

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

Import VarValStore.Notations. 

(* Stepping tactics will not take any arguments.  *)
(* TODO:  *)
Ltac stp_corr_wf_gl :=
  lazymatch goal with
  |- context [ ⟨ corruptor ?atk ?ast ?st | is_trusted ⟩] => 
    let t := constr:(⟨ corruptor atk ast st | is_trusted ⟩) in
    have: t = ⟨ st | is_trusted ⟩=> [| ->]; [ 
    move: (corruptor_wf atk);  ⟨ evar_spec ⟩=> - [] + _; intros ->;done|]
  end.

Section test.
  Context `{!VarPrm,!ValPrm, !AdvLvlPrm, !AdvLeakPrm}.
  Generalizable All Variables.
  Goal `(forall P, P ⟨ corruptor (AtkStates := A) adv ast st  | is_trusted ⟩).
  Proof. move=> *. stp_corr_wf_gl. Abort.
End test.





Ltac2 stp_abstract_units_gl () :=
  repeat (
    let count :int ref := {contents := 0} in 
    repeat (
      ltac1:(let f := fresh in   set (f := _ : unit) at 1; move: f);
      count.(contents) := Int.add (count.(contents)) 1);
    do (count.(contents))  ltac1:(case)).
        

Ltac stp_destruct_units_gl :=
  ltac2:(stp_abstract_units_gl ()).
  (*assert_goal 1. The issue is that there needs to be some focusing done. all: things stress this out. TODO: How to fix?*)

Section test.
  Goal `(forall P (x : unit),  P tt x).
  Proof.  move=> ? x.  stp_destruct_units_gl. clear x.  Abort.
  Goal `(forall P (f : unit -> unit),  P (f tt)).
  Proof. move=> ? f.  stp_destruct_units_gl. clear f. Abort.
End test.


Section ts.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  (* Should this be inductive? *)
  Inductive CmdRestriction: Cmd -> Prop :=
    | nitr : forall comp, 
        Noninterfering (store_to_view is_trusted) comp (store_to_view is_trusted) ->
        CmdRestriction (assign comp).

  Definition ProgRestriction: Prog -> Prop :=
    Forall CmdRestriction.

  (* This name is stupid *)
  Definition AtkCmdRestriction '(mk_cstep _ c) : Prop :=
    if c isn't Some c then True else
    CmdRestriction c.

  Definition ContinuationRestriction: Continuation -> Prop :=
    Forall AtkCmdRestriction.

  (* TODO: Maybe show some safety lemma..
    If x sats continuation restruction and takes a step to x', then x' also satisfies that.
    This is true for all states, and whatnot
  *)

  (* 
    I think that constructor is okay to be part of finisher. 
    Don't make it part of forward reasoning
  *)
  Lemma pure_atk_wt : AtkCmdRestriction pure_atk. 
  Proof. constructor. Qed.

  Lemma pure_atklst_wt: forall n, 
    Forall AtkCmdRestriction (nlist  pure_atk n).
  Proof. 
    elim=> /=; auto using pure_atk_wt.
  Qed.

  Lemma restrict_rel: forall p,
    ProgRestriction p -> 
    (forall n, ContinuationRestriction (prog_zip p n)).
  Proof.
    rewrite/ContinuationRestriction/ProgRestriction. 
    elim=> [_ n|]; first (elim: n=> //= >; constructor; easy).
    move=> c l ih; ⟨ Forall_inv ⟩.
    move=> cr t; move: ih=> /(_ t) {t}=> cl n.
    case: n c l cr cl=> [> ? /(_ 0) |]; last constructor=> //. 
    rewrite !prog_zip_noatk /=; auto.
  Qed.

End ts.

Parameter vli : ValPrm. Existing Instance vli.
Parameter vri : VarPrm. Existing Instance vri.
Parameter lvli : AdvLvlPrm. Existing Instance lvli.
Parameter lki : AdvLeakPrm. Existing Instance lki.

Parameter myprog : Prog. Axiom myprog_wt : ProgRestriction myprog.

Definition AtkRealStates := unit.
Parameter atkreal : AdvStateMachine AtkRealStates.
 

(* TODO: Goes elsewhere *)
Notation only_atk_steps c := (map get_cmd (filter is_attacked c)) (only parsing).
Section idealatk.
  Record SimExtraStates := mk_sim_extra {
      sim_cont : list (option Cmd) ; 
  }.
   

  Record SimStates := mk_sim_state {real_sim : AtkRealStates ; extra: SimExtraStates}.


  Definition sim_init_state (inp: StoreView):  SimStates := 
    let: init_realatk := init_state atkreal inp in 
    let: init_realsubstps := init_substeps atkreal init_realatk in 
    let: init_cont := prog_zip myprog init_realsubstps in
    let: init_optprog := only_atk_steps init_cont in
    mk_sim_state init_realatk (mk_sim_extra init_optprog).

  Definition sim_learner (s : SimStates) (_: Store):  SimStates :=
    let: mk_sim_state real_st (mk_sim_extra cont) := s in 
    let: substeps := substeps atkreal real_st in
    let: real_st' := real_st in (* TODO: This should be fixed eventually *)
    mk_sim_state real_st' (mk_sim_extra ((nlist None substeps) ++ (tl cont))). 

  Obligation Tactic := idtac. (* TODO: Program cases or whatnot *)
  Program Definition atkideal : AdvStateMachine SimStates := {|
      init_state := sim_init_state ;
      learner := sim_learner;

      (* These  things are fixed. Things probably can be refactored better, but I don't care *)

      init_substeps st := init_substeps atkreal (real_sim st);
      corruptor _ := id; (* TODO: We need to show a stronger property, which we don't.. But which is obvious.. We need to say that simulator only does things at x or y*)
      leaker st := leaker atkreal (real_sim st);
      substeps st := substeps atkreal (real_sim st)
      |}.
  

  Next Obligation. easy. Qed.
  Next Obligation. 
    move=> [] /= arst ?.
    move: (learner_wf atkreal)=> /(_ arst).
    move: (store_to_view _) (learner _ _)=> > nirl.
    move=> s1 s2; move: nirl=> /(_ s1 s2) /[apply]. 
    dst_hyp_type SimExtraStates=>//=.
  Qed.
End idealatk.

Import Semantics.Notations.
Definition b1 := ⟦ myprog ☠︎︎ atkreal ⟧.
Definition b2 := ⟦ myprog ☠︎︎ atkideal ⟧.

Notation CfgR := (Cfg AtkRealStates).
Notation CfgI := (Cfg SimStates).

Record CombObj := {
     cont : Continuation; (* A single continuation is shared between everything *)
     real_st : Store; (* Store for the real system *)
     ideal_st : Store; (* Store for the ideal system *)
     (* sim_st: Store; (* This will  *) *)
     trace: ObservationTrace; (* Trace for everything *)
    }. 

Definition CombObjInv (c : CombObj): Prop :=
     ContinuationRestriction (cont c) /\
     ⟨ real_st c | is_trusted ⟩ = ⟨ ideal_st c | is_trusted ⟩.

Definition extract_r (comb : CombObj): CfgR :=
    (cont comb, real_st comb, tt , trace comb).

Definition extract_i (comb : CombObj): CfgI :=
    (cont comb, ideal_st comb, mk_sim_state tt (mk_sim_extra(only_atk_steps (cont comb))), trace comb).
(* Make a list of things which are happening *)

Definition comb_init (s_init : Store):  CombObj :=
    (* TODO: There should be attacker state also, which we'll do later  *)
    let: (cont, st, (mk_sim_state _ sim_extra), init_tr) := initial_cfg myprog atkideal s_init in 
    {|
     cont := cont ;
     real_st := st ;
     ideal_st := st ;
     trace := init_tr 
    |}.

Lemma comb_init_inv: forall s, CombObjInv (comb_init s).
Proof.
    rewrite/comb_init/initial_cfg/CombObjInv/=.
    auto using restrict_rel, myprog_wt.
Qed.

Lemma comb_init_extraction: forall s,
    extract_r (comb_init s) = initial_cfg myprog atkreal s /\
    extract_i (comb_init s) = initial_cfg myprog atkideal s.
Proof.
    move=> ?; rewrite /initial_cfg/extract_r/extract_i /=. 
    case: (init_state _ _)=> //. 
    split=> //. do ! congr (_,_).
    rewrite/sim_init_state.
    stp_destruct_units_gl.
    congr mk_sim_state.
    (*  Here, we are doing something  sus*)
Qed.

Definition comb_step (c: CombObj): CombObj :=
    let: 
        {| cont := cont; 
           real_st := real_st; 
           ideal_st := ideal_st; 
           trace := trace |} := c
    in
    let: (cont', real_st', ideal_st', leak') :=
      (* If the program is empty *)
      if cont isn't (atkcmd :: cont') then ([], real_st, ideal_st, None) else 

      (* If the program is not empty *)
      let: (real_st', _, extra_cont', leak') := atk_cmd_step atkreal atkcmd real_st tt in
      let: (ideal_st', _) := optcmd_step (get_cmd atkcmd) ideal_st in


      (extra_cont' ++ cont', real_st', ideal_st', leak')
    in
    {| cont := cont'; 
       real_st := real_st'; 
       ideal_st := ideal_st'; 
       trace := (⟨real_st'| is_trusted⟩, leak') :: trace |}.



(* TODO: This seems like a very very inefficient way to do this*)
Ltac stp_cnt_dst_gl :=
        match goal with
        |- context [match ?cnt with [] => _ | _ => _ end] => 
        let t := type of cnt in 
        unify t Continuation; (* I don't get this unify, etc. *)
        destruct cnt
        end.

Ltac stp_dst_atkcmd :=
    lazymatch goal with
    [ H : AtkCmdRestriction ?a |- _ ] => 
      let isatk := fresh in let cmd := fresh in 
      is_var a; destruct a as [isatk cmd];
      destruct isatk; destruct cmd;
      destruct H
    end.

Ltac stp_lst_app :=
  match goal with
  | |- _ ++ ?l = _ ++ ?l => congr (_ ++ _)
  | |- ?l ++ _ = ?l ++ _ => congr (_ ++ _)
  end.

Ltac stp_ni :=
    lazymatch goal with
    H : Noninterfering (store_to_view ?p) ?comp (store_to_view ?p) |-⟨ ?comp _ | is_trusted ⟩ =⟨ ?comp _ | is_trusted ⟩ => apply:H
    end.

(* TODO: Need to think about the right way to structure proofs and so on 
finisher backtracking proofs?
*)

(* TODO: Make this better. 
This should ideally take a tactic

*)


Ltac grind_step engine finisher := (engine || idtac); intros ; hnf; try finisher.

Ltac grind engine finisher :=  do ! [grind_step engine finisher].
    
Ltac engine := 
  (
  stp_Forall_app_gl ||
  stp_cnt_dst_gl ||
  stp_dst_atkcmd ||
  stp_corr_wf_gl ||
  stp_ni ||
  stp_destruct_units_gl ||
  stp_lst_app ||
  cnstrct_eq_gl || (* TODO: Naming convention *)
  apply/ pure_atklst_wt ||
  split ||
  unfold id in * ||
  ⟨⟨ Forall_inv ⟩⟩ ||
  rewrite filter_app ||
  rewrite map_app
  ).

(* TODO; This is actually quite sad *)
Ltac finisher := do ! progress(auto). (* (simpl + auto + done); fail does not work. Why? *)

Ltac mygrind := grind engine idtac.
Ltac mygrindstep := grind_step engine idtac.


Lemma comb_step_inv: forall c, 
                        CombObjInv c ->
                        CombObjInv (comb_step c).
Proof.
    case; rewrite /CombObjInv=> cnt >  /= [cr treq].
    mygrind=> /=.
    all: (mygrind)=> //=.
Qed.

Lemma nlist_filter_true : 
  forall n {A} (v: A) f,
    f v = true ->
    filter f (nlist v n) = nlist v n.
Proof.
  elim=> > ? //= => > /[dup] + ->=> *.
  congr (_::_);  auto.
Qed.

Lemma nlist_filter_false : 
  forall n {A} (v: A) f,
    f v = false ->
    filter f (nlist v n) = [].
Proof.
  elim=> > ? //= => > /[dup] + ->; auto.
Qed.
   

Lemma nlist_forallb_true: forall n {V} (tst : V -> bool) (v : V),
    tst v -> 
    forallb tst (nlist v n).
Proof.    elim=> * //=. apply/andP; auto. (* TODO: I don't know how this works *)Qed.

Lemma map_nlist: forall n {A B} (v: A) (f: A -> B), map f (nlist v n) = nlist (f v) n.
Proof.  elim=> * //=; congr (_ :: _); auto. Qed.

Section thm.
  Lemma comb_step_valid : forall c , 
      CombObjInv c ->
      extract_i (comb_step c) = step atkideal (extract_i c) /\
      extract_r (comb_step c) = step atkreal (extract_r c). 
  Proof.
    move=> [] > [cnt treq]; rewrite /= in cnt treq. (* TODO: Need to have this be good *)
    do !(mygrind; auto=> //=).
    all: (rewrite/extract_i/extract_r//=); do !(mygrind; auto=> //=).
    all: rewrite nlist_filter_true=> //; apply/map_nlist.
  Qed.

End thm.


Theorem comb_extract: 
    forall c, extract_trace (extract_i c) = extract_trace (extract_r c). 
Proof. case=> //. Qed.



Goal b1 = b2. 
Proof.
    rewrite/b1/b2/⟦ _ ☠︎︎  _⟧.
    apply/functional_extensionality=> s; apply/functional_extensionality=> n.
    set msr:= (multistep _ _ _); set msi := (multistep _ _ _).
    suff: exists c, CombObjInv c /\ msr = extract_r c  /\ msi = extract_i c;
      first (move=> [? [_ [-> ->]]]; rewrite comb_extract //).
    rewrite{}/msr{}/msi.

    elim: n=> [|> [c [cinv [e1 e2]]]].
    - exists (comb_init s) => /=.
      split; first apply/comb_init_inv.    
      move:(comb_init_extraction)=> /(_ s).
      intuition.

    - exists (comb_step c)=> /=. 
      split; first apply/comb_step_inv=> //.
      move: (comb_step_valid c cinv) e1 e2 => [-> ->] -> -> //.
Qed.
