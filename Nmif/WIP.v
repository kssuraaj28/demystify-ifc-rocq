(* Time to cook *)
From Stdlib Require Import ssreflect ssrbool List FunctionalExtensionality.
Import ListNotations.


(* This may be useful *)
From QuickChick Require Import Decidability.

Require Import Util VarValStore Syntax Semantics Attacker Util Noninterference Tacs. 
Import Util.Dec Util.List. 

(* An *_ssr tactic follows the ssr philosophy*)
Ltac Forall_inv_ssr :=  move=>/[dup] /(@Forall_inv _ _ _) + /(@Forall_inv_tail _ _ _).

Ltac evar_spec_ssr :=  
    let t := open_constr:(_) in 
    let f := fresh in 
    pose f := t=> /(_ f); subst f.

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
  Lemma restrict_rel: forall p,
    ProgRestriction p -> 
    (forall n, ContinuationRestriction (prog_zip p n)).
  Proof.
    rewrite/ContinuationRestriction/ProgRestriction. 
    elim=> [_ n|]; first by elim: n=> //= >; constructor; easy.
    move=> c l ih /ltac:(Forall_inv_ssr).
    move=> cr t; move: ih=> /(_ t) {t}=> cl n.
    case: n c l cr cl=> [> ? /(_ 0) |]; last by constructor. (* Can I make 0 an evar? *)
    by rewrite !prog_zip_noatk /=; auto.
  Qed.

End ts.

Parameter vli : ValPrm. Existing Instance vli.
Parameter vri : VarPrm. Existing Instance vri.
Parameter lvli : AdvLvlPrm. Existing Instance lvli.
Parameter lki : AdvLeakPrm. Existing Instance lki.


Definition AtkRealStates := unit.
Parameter atkreal : AdvStateMachine AtkRealStates.

Section idealatk.
   (*

    Okay, there are the following things to do:
    There must be

    - real store
    - ideal store
    - sim store

    Moreover, there will be invariants.
    ⟨ real_store | is_trusted  ⟩ = ⟨ ideal_store | is_trusted ⟩
    ⟨ real_store | is_public  ⟩ = ⟨ sim_store | is_public ⟩

    Moreover, different from viaduct, we will also have:

    - real continuation
    - ideal continuation
    - sim continuation

    The invariants should be:
    - When the PC is public trusted, all three should be equal
    - When the PC is secret trusted, real = ideal continuation. the sim continuation must be 'I don't know'
    - When the PC is untrusted,  ??. 

    The proof sketch maybe should look like this..

   * When the pc is untrusted, there should not be any changes to the real store
     trusted or ideal store trusted in any substep

   * When the pc is secret, there should not be any changes to the real store public.
    
     trusted or ideal store trusted in any substep


   *)
  Parameter SimExtraStates : Type.
  Parameter s_init : SimExtraStates.
  Record SimStates := mk_sim_state {real_sim : AtkRealStates ; extra: SimExtraStates}.
  Parameter f : SimStates -> SimExtraStates.
  (* TODO: Add more things here 
      Maybe add a counter? 
      Maybe add the program configuration? + Store? We can
      just add some whole store, 
      but maintain the invariant that 
  *)

  Obligation Tactic := idtac. (* TODO: Program cases or whatnot *)
  Program Definition atkideal : AdvStateMachine SimStates := {|
      init_state mem := mk_sim_state (init_state atkreal mem) s_init;
      init_substeps st := init_substeps atkreal (real_sim st);
      corruptor _ := id; (* TODO: We need to show a stronger property, which we don't.. But which is obvious.. We need to say that simulator only does things at x or y*)
      learner st mem := mk_sim_state (learner atkreal (real_sim st) mem) (f st);
      leaker st := leaker atkreal (real_sim st);
      substeps st := substeps atkreal (real_sim st)
      |}.

  Next Obligation. by easy. Qed.
  Next Obligation. 
    move=> [] /= arst ?.
    move: (learner_wf atkreal)=> /(_ arst).
    move: (store_to_view _) (learner _ _)=> > nirl.
    move=> s1 s2; move: nirl=> /(_ s1 s2) /[apply]. 
    by rewrite /id=> ->. 
  Qed.
End idealatk.

Import Semantics.Notations.
Parameter myprog : Prog. Axiom myprog_wt : ProgRestriction myprog.
Definition b1 := ⟦ myprog ☠︎︎ atkreal ⟧.
Definition b2 := ⟦ myprog ☠︎︎ atkideal ⟧.

(* 
Constructing a combined object.
I will use refinement types..
CombObj will contain the  data as well as the invariant.
There should be a function extracts CfgI and CfgR from it
There should be a stepping relation on this object also.
Finally, there should be 
Figuring out this single object approach would be a good task for the day..



*)

(* Can I construct a proof object with more state? 
Parameter Po : Type.
Parameter BisimRel : Po -> Type.
You need to lift step to Po..
*)

Notation CfgR := (Cfg AtkRealStates).
Notation CfgI := (Cfg SimStates).
Section bisim.

  Import VarValStore.Notations.

  Definition BisimRel (cr : CfgR) (ci: CfgI) : Prop :=
    let: (contr, storer, asr, trr) :=  cr in
    let: (conti, storei, (mk_sim_state asrsim _), tri) :=  ci in
    ContinuationRestriction contr /\  (* I don't like this*)
    (conti = contr) /\
    (asr = asrsim) /\
    ⟨ storer | is_trusted ⟩ = ⟨ storei | is_trusted ⟩ /\
    (trr = tri). 
  

  Import Tacs.SsrHack.
  Lemma bisim_extract: forall c1 c2,
                  BisimRel c1 c2 -> extract_trace c1 = extract_trace c2.
  Proof.
    move=> [[[? ?]?]?].
    move=> [[[? ?][? _]]?] /=. (* _ is s  *)
    by intuition.
  Qed.

  Lemma bisim_init: 
    forall s,
    BisimRel 
      (initial_cfg myprog atkreal  s)
      (initial_cfg myprog atkideal s).
  Proof.
    move=> s; split; first by apply/restrict_rel/myprog_wt.
    by repeat split=> //; repeat case: (init_state _ _).
  Qed.

  Lemma bisim_step: forall c1 c2,
                          BisimRel c1 c2 ->
                          BisimRel (step atkreal c1) (step atkideal c2).
  Proof.
    move=> [[[cont ? ]astr] ?] [[[? ?] [artrsim ?]]?].
    move=> [wt [-> [-> [trseq ->]]]] /=.
    case: cont wt=> [|atkcmd ? wt]; first by rewrite /= trseq //=.
    move rst: (atk_cmd_step atkreal _ _ _) => [[[sr []] contr ] lkr]. (* Note how I make tt. TODO *)
    move ist: (atk_cmd_step atkideal _ _ _) => [[[si [[] ?]] conti] lki].
    move: wt=>/ltac:(Forall_inv_ssr) wth wttl /=.
    clear- trseq rst ist wth wttl; set rsv := ⟨ sr | _ ⟩; set isv := ⟨ si | _⟩.
    suff: ([elaborate ContinuationRestriction contr /\ conti = contr /\  rsv = isv /\ lkr = lki])
      by intuition; try congruence; apply/Forall_app.
    rewrite {}/rsv {}/isv; move: atkcmd wth ist rst=> [isatk cmd]. 
    rewrite/AtkCmdRestriction=> [[]]; rewrite/Noninterfering; clear -trseq=> > ni.
    rewrite/atk_cmd_step ![corruptor atkideal _ _]/=.
    move cs1: (clean_cmd_step _ _)=> [>]; move cs2: (clean_cmd_step _ _)=> [>].
    case: isatk cs1 cs2; last 
      by move=> /= [<- <-] [<- <-] [<- <- _ <- <-] [<- <- <-]; (repeat split; try red; auto).
    move lrnrle:(learner atkreal _ _)=> lrnrl; move lrnide:(learner atkideal _ _) => [lrnid lrnidex].
    move subrle:(substeps atkreal _)=> subrl; move subide :(substeps atkideal _) => subid.
    rewrite /=/id in subrle lrnrle lrnide subide *; case: lrnide=> lrnide lrnidexe.
    case=> e; rewrite -{}e /=in lrnide *=> <-.
    case=> e; rewrite -{}e /=in lrnrle *=> <-.
    case=> <- e; rewrite {}e in subide lrnide *=> e; rewrite {}e in lrnidexe=> <- <-.
    case=> <- e; rewrite {}e in subrle lrnrle *=> <- <-.
    (have ->: subid = subrl by congruence); clear subide subrle.
    (have _: lrnrl = lrnid by case: lrnrl; case: lrnid); clear lrnide lrnrle lrnidexe. (* TODO When we say improve more than tt, we will get this ..*)
    repeat split; first by rewrite -/(prog_zip [] _); apply/restrict_rel.
    apply: ni; rewrite -{}trseq; clear.
    by move: (corruptor_wf atkreal); firstorder.
  Qed.
End bisim.

Goal b1 = b2 . Proof.
  apply: functional_extensionality=> s; apply: functional_extensionality=> n.
  rewrite /b1 /b2 !/(⟦_☠︎︎_⟧).
  set c1 := (initial_cfg _ _ _); set c2 := (initial_cfg _ _ _). (* Set second? *) 
  move e1: (multistep _ _ c1) => ms1; move e2: (multistep _ _ c2) => ms2. 
  apply/bisim_extract.
  elim: n ms1 ms2 e1 e2=> [> | > ? >] <- <- /=; first by apply/ bisim_init.
  by apply/bisim_step; auto. (* What the hell is this *)
Qed.


(* Combined Object...
This will contain:
- Continuation
- Real store
- Ideal store
- Trace
*)
Import VarValStore.Notations. 
Record CombObj := {
     cont : Continuation; (* A single continuation is shared between everything *)
     real_st : Store; (* Store for the real system *)
     ideal_st : Store; (* Store for the ideal system *)
     sim_extra: SimExtraStates;
     trace: ObservationTrace; (* Trace for everything *)
     cont_wf : ContinuationRestriction cont;
     tr_match : ⟨ real_st | is_trusted ⟩ = ⟨ ideal_st | is_trusted ⟩
    }. 

Definition extract_r (comb : CombObj): CfgR :=
    (cont comb, real_st comb, tt , trace comb).

Definition extract_i (comb : CombObj): CfgI :=
    (cont comb, ideal_st comb, mk_sim_state tt (sim_extra comb), trace comb).

(*
Cfg =
fun (H : VarPrm) (H0 : ValPrm) (H2 : AdvLeakPrm) (AtkStates : Type) =>
(Continuation * Store * AtkStates * ObservationTrace)%type
     : VarPrm -> ValPrm -> AdvLeakPrm -> Type -> Type

Arguments Cfg {H H0 H2} AtkStates%type_scope
*)
(* TODO: Take more things as input? *)
Section def.
    Obligation Tactic := try done. (* TODO: Program cases or whatnot *)
    Program Definition comb_init (s_init : Store):  CombObj :=
        (* TODO: There should be attacker state also, which we'll do later  *)
        let: (cont, st, (mk_sim_state _ sim_extra), init_tr) := initial_cfg myprog atkideal s_init in 
        {|
         cont := cont ;
         real_st := st ;
         ideal_st := st ;
         sim_extra := sim_extra ;
         trace := init_tr 
        |}.
    Next Obligation.
      move=> /= > [] -> *; clear.
      by auto using restrict_rel, myprog_wt.
    Qed.
End def.

Lemma comb_init_valid: forall s,
    extract_r (comb_init s) = initial_cfg myprog atkreal s /\
    extract_i (comb_init s) = initial_cfg myprog atkideal s.
Proof.
    move=> ?; rewrite /initial_cfg/extract_r/extract_i /=. 
    by case: (init_state _ _). (*  Here, we are doing something  sus*)
Qed.

Section def.
    Obligation Tactic := try done. (* TODO: Program cases or whatnot *)
(*
atk_cmd_step atkreal ?c ?s tt
     : Store * AtkRealStates * Continuation * option LeakVals
where
?c : [ |- AtkCmd]
?s : [ |- Store]
*)
    (* This is really how you should think about it.. 
       Maybe it is not a terrible idea to replicate things
    *)
    Program Definition comb_step (c: CombObj): CombObj :=
        let: 
            {| cont := cont; 
               real_st := real_st; 
               ideal_st := ideal_st; 
               sim_extra := sim_extra ; 
               trace := trace |} := c
        in
        if cont isn't (cmd :: cont') then c else  (* Is this correct? *)
        if cmd isn't (mk_cstep is_atk (assign comp)) then False_rect _ _ else (* Here, we throw an exception *)
        if is_atk is false then 
            {| 
               real_st := comp real_st; 
               ideal_st := comp ideal_st; 
               sim_extra := sim_extra;
               cont :=  cont';
               trace := ((⟨real_st |is_trusted ⟩,None)::trace)  (* You could also use ⟨ ideal_st | is_trusted ⟩ here! *)
            |}
         else  
            {| 
               real_st := comp (corruptor atkreal tt real_st);
               ideal_st := comp ideal_st; (* Does this even get corrupted? *)
               sim_extra := f (mk_sim_state tt sim_extra);
               cont :=  cont'; (* This is not correct.. *)
               trace := ((⟨real_st |is_trusted ⟩, Some (leaker atkreal tt))::trace)  (* You could also use ⟨ ideal_st | is_trusted ⟩ here! *)
            |}.
           
         (* Just handcode everything that will happen *)

        (* Maybe rewrite atk_cmd_step here? 
           The fact that I am rewriting makes me a litte uneasy..

        *)
        (* What should be done? We need to show that there is a single continuation 
        - real_st
        - ideal_st
        - sim_extra
        - trace
        Maybe the right thing to do is to redefine everything.. 
        When there is no attack..
        -- 
        *)
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
    Next Obligation. Admitted.
End def.


Axiom comb_step_valid : forall c , 
    extract_i (comb_step c) = step atkideal (extract_i c) /\
    extract_r (comb_step c) = step atkreal (extract_r c). 


Theorem comb_extract: 
    forall c, extract_trace (extract_i c) = extract_trace (extract_r c). 
Proof. by case. Qed.

Import Tacs.SsrHack.
Goal b1 = b2. 
Proof.
    rewrite/b1/b2/⟦ _ ☠︎︎  _⟧.
    apply/functional_extensionality=> s; apply/functional_extensionality=> n.
    set msr:= (multistep _ _ _); set msi := (multistep _ _ _).
    suff: exists c, msr = extract_r c  /\ msi = extract_i c by move=> [? [-> ->]]; rewrite comb_extract.
    subst msr msi;  elim: n=> [|> [c [*]]]; first by
        exists (comb_init s); move: (comb_init_valid s)=> [-> ->].
    exists (comb_step c); move: (comb_step_valid c)=> [-> ->].
    move ? : (step atkreal _)=> ?;  move ? : (step atkideal _)=> ? /=. (* Controlled simpl. Locking is actually sick *)
    by intuition; congruence.
Qed.
