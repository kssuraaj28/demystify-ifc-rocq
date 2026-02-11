From Stdlib Require Import List ssreflect.
(* ssreflect for gallina extensions *)
From QuickChick Require Import Decidability. 
(* QuickCheck decidable equality classes are so good *)

Import ListNotations.
(* I'm just going to bundle stuff for now. The context is getting quite large otherwise.
*)
Class VarPrm := {Vars : Type ; vars_deceq :: Dec_Eq Vars}. 
Class ValPrm := {Vals : Type}.

(* Changing this to () does make a difference! *)
Class AdvLvlParam `{!VarPrm} := { is_untrusted : Vars -> bool ; is_public : Vars -> bool }.


(* When you instantiate an adversary, you also give it memory *)
Class AdvMemParam := {AdvMem : Type}. (* Maybe specify initial value also.. *)

Class AdvLeakParam := {LeakVals : Type}.  (* The type of messages that the adversary leaks *)

Section advsnips.
  Context `{!ValPrm, !AdvMemParam, !AdvLeakParam}. 

  (* When you write to an adversary readable variable, the adversary can exfiltrate the value *)
  Definition AdvExfiltrator := Vals -> AdvMem -> (LeakVals * AdvMem).

  (* 
    When you read from  an adversary writable variable, the adversary can corrupt the value 
    The adversary can maul
  *)
  Definition AdvCorruptor := Vals -> AdvMem -> Vals. 
End advsnips.

Section syntax.
  (* I wonder whether all of this should be packaged into a single thing? I could do "SyntaxParams" *)
  Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.

  Inductive VarSrc := mk_vr_src (v: Vars) (adv : AdvCorruptor).
  Inductive VarDst := mk_vr_dest (v: Vars) (adv : AdvExfiltrator).


  (* 
    v1 ∘ v2. Some binary operation 
    If either variable is controlled by the adversary, then that strat will be applied.
    Another thing we could to is to have an alternative where the adversary gets to supply an alternative function.
    Here, when either variable is untrusted, the adversary function gets activated
  *)
  Inductive ValExp := mk_vl_exp (v1 v2: VarSrc) (comp : Vals -> Vals -> Vals).
  Inductive BoolExp :=  mk_bl_exp (v: VarSrc) (test : Vals -> bool).

  Section cmd.
    Notation Prog' Cmd := (list Cmd).
    Unset Elimination Schemes. Inductive Cmd :=
      | assign (d : VarDst) (exp : ValExp)
      | cond (cond_var: BoolExp) (b1 b2: Prog' Cmd)
      | while (cond_var: BoolExp) (body: Prog' Cmd).  Set Elimination Schemes.
    Definition Prog := Prog' Cmd.
  End cmd.

  Section cmd_ind.
    Variable P : Cmd -> Prop.
    Generalizable All Variables.

    Hypothesis assign : `(P (assign d exp)).

    Hypothesis cond : `(Forall P b1 ->
                        Forall P b2 ->
                        P (cond cond_var b1 b2)).

    Hypothesis while : `(Forall P body ->
                          P (while cond_var body)).

    Ltac done ::= auto.
    Ltac t appl :=  intros; apply appl; match goal with |- Forall P ?b => induction b end.

    (* I don't know whether I'm using the right ssreflect thing *)
    Fixpoint Cmd_ind : forall c, P c. Proof.
      case => c; by [t assign || t cond || t while].
    Qed.
  End cmd_ind.
  (* It is a little weird that a very syntactic  *_ind approach is used. *)
  Goal forall c : Cmd, c = c. elim => c; reflexivity. Qed. 
End syntax.

Section store.
  Context `{!VarPrm, !ValPrm}.

  Definition Store := Vars -> Vals.
  Definition get_from_store (st : Store) (v : Vars) : Vals := st v.
  Definition update_to_store (st : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if (v = v')? is true then vl else st v'.  (* The double colon in vars_deceq is needed here. *)
End store.

Section semantics.
  Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam, !AdvLvlParam}.

  (* What is 'state'? *)
  Inductive Cfg := mk_cfg (store : Store) (amem: AdvMem) (cont : Prog).

  (* Our definition is super lockstep. 
     If it works, I think it's good.
  *)
  Inductive Event :=
    | assignment (optupd: option (Vars * Vals)) (optlk : option LeakVals) (* We don't care about updates to untrusted variables *)
    | if_choice(choice : bool)
    | while_choice (choice : bool)
    | terminate.
  (* 
    You check whether the variable is controlled by the attacker. 
    If the variable is controlled by the attacker, then the adversary strat is active
    I'm making a very important choice here. 
    We can strengthen or weaken the adversary later here.
  *)

  Definition store_read_w_adv (st : Store) (vs : VarSrc) (amem : AdvMem) : Vals := 
    let: mk_vr_src v adv := vs in 
    let: orig_val := get_from_store st v in
    if (is_untrusted v) is false then orig_val else
    adv orig_val amem.

  Definition val_exp_eval (e : ValExp) (store : Store) (amem : AdvMem) : Vals :=
    let: mk_vl_exp vs1 vs2 comp := e in
    let: get_val := fun vs => store_read_w_adv store vs amem in 
    let: val1 := get_val vs1 in
    let: val2 := get_val vs2 in
    comp val1 val2.


  Definition bool_exp_eval (be : BoolExp) (store : Store) (amem : AdvMem) : bool :=
    let: mk_bl_exp vs test := be in
    let: val := store_read_w_adv store vs amem in 
    test val.


  Definition store_update_w_adv
          (s : Store) (vd : VarDst) (vl : Vals) (amem : AdvMem) : 
          Store * AdvMem * Event :=
    let: mk_vr_dest v adv := vd in 
    let: s' := update_to_store s v vl in
    let: (lk, amem') := (adv vl amem) in
    (* We leak only when the variable is public *)
    let: optlk := if (is_public v) is false then None else Some lk in 
    (* Only trusted updates are part of our trace *)
    let: optupd := if (is_untrusted v) is true then None else Some (v,vl) in
    (s',amem', assignment optupd optlk).



  (* Maybe this can be factored out.. *)
  Definition step (cfg : Cfg) : Cfg * Event:=
    let: mk_cfg store amem prog := cfg in
    if prog isn't (cmd :: prog') then (cfg, terminate) else  (* prog is skip *)

    match cmd with 
    | assign vd exp =>  
        let: cont := prog' in
        let: val := (val_exp_eval exp store amem) in
        let: (store', amem', event) := store_update_w_adv store vd val amem in
        (mk_cfg store' amem' prog', event)

    | cond exp b1 b2 =>
        let: test := (bool_exp_eval exp store amem) in
        let: branch := if test is true then b1 else b2 in
        let: cont := (branch ++ prog') in
        let: cfg := mk_cfg store amem cont in
        (cfg, if_choice test)

    | while exp while_bdy  =>  
       let: test := (bool_exp_eval exp store amem) in
       let: cont := if test is false then prog' else (while_bdy ++ prog) in
       let: cfg := mk_cfg store amem cont in
       (cfg, while_choice test)
    end.


(* 
  What is the correct next step?
  - Define what NMIF is. 
  - I need to define what an observation is..
    -- initial and final state? Then I need to talk about nontermination and all that bs
    -- Writes to trusted channels? What about reads then?
  - Maybe I skirt things about observations, and show the stongest proof lemma I can show..
    -- This will be my strat.
  - First, I would have to put restriction on adversary (cannot maul) -- This will be the definition of what it means for a system to satisfy nmif.
  - Then, I will have to incorporate IFC on it.
*)
End semantics.
