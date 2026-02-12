From Stdlib Require Import (*Arith*) List ssreflect.
From QuickChick Require Import Decidability. 
(* QuickCheck decidable equality classes are so good *)
(* ssreflect for gallina extensions *)
(* Arith for iter_nat *)

Import ListNotations.
(* I'm just going to bundle stuff for now. The context is getting quite large otherwise.
*)
Class VarPrm := {Vars : Type ; vars_deceq :: Dec_Eq Vars}. 
Class ValPrm := {Vals : Type}.

(* Changing this to () does make a difference! *)
Class AdvLvlParam `{!VarPrm} := { is_untrusted : Vars -> bool ; is_public : Vars -> bool }.


(* When you instantiate an adversary, you also give it memory *)
Class AdvMemParam := {AdvMem : Type; adv_init : AdvMem}.

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



Section var_atk.
  Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.
  
  Inductive AtkVarSrc := mk_vr_src (v: Vars) (adv : AdvCorruptor).
  Definition erase_var_src '(mk_vr_src v _) := v. (* I don't even think that this is an ssreflect extension *)

  Inductive AtkVarDst := mk_vr_dest (v: Vars) (adv : AdvExfiltrator).
  Definition erase_var_dst '(mk_vr_dest v _) := v.
End var_atk.

(* 
   This should be a helper defined somewhere else. 
   There should be a string accessor
*)
Class _SrcVarTC := SrcVar : Type. 
Class _DstVarTC := DstVar : Type.

Section meta_syntax.
  (* I wonder whether all of this should be packaged into a single thing? I could do "SyntaxParams" *)
  Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.

  Context `(!_SrcVarTC, !_DstVarTC).


  (* 
    v1 ∘ v2. Some binary operation 
  *)
  Inductive ValExpMeta := mk_vl_exp (v1 v2: SrcVar) (comp : Vals -> Vals -> Vals).
  Inductive BoolExpMeta :=  mk_bl_exp (v: SrcVar) (test : Vals -> bool).

  Section cmd.
    Notation ProgMeta' CmdMeta := (list CmdMeta).

    Unset Elimination Schemes. Inductive CmdMeta :=
      | assign (d : DstVar) (exp : ValExpMeta)
      | cond (cond_var: BoolExpMeta) (b1 b2: ProgMeta' CmdMeta)
      | while (cond_var: BoolExpMeta) (body: ProgMeta' CmdMeta).  Set Elimination Schemes.

    Definition ProgMeta := ProgMeta' CmdMeta.
  End cmd.

  Section cmd_ind.
    Variable P : CmdMeta -> Prop.
    Generalizable All Variables.

    Hypothesis assign : `(P (assign d exp)).

    Hypothesis cond : `(Forall P b1 ->
                        Forall P b2 ->
                        P (cond cond_var b1 b2)).

    Hypothesis while : `(Forall P body ->
                          P (while cond_var body)).

    Ltac t appl :=  intros; apply appl; match goal with |- Forall P ?b => elim: b; auto end.

    (* I don't know whether I'm using the right ssreflect thing *)
    Fixpoint CmdMeta_ind : forall c, P c. Proof.
      case => c; (t assign || t cond || t while).
    Qed.

  End cmd_ind.
  (* It is a little weird that a very syntactic  *_ind approach is used. *)
  Goal forall c : CmdMeta, c = c. elim => c; reflexivity. Qed. 
End meta_syntax.

Section syntax.
  Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.

  (* I don't like this _. 
    There are a few options, none of which I found fully good
    - refine
    - notations
  *)
  Ltac constr_valexp := exact (ValExpMeta _). 
  Ltac constr_boolexp := exact (BoolExpMeta _).
  Ltac constr_cmd := exact (CmdMeta _ _).
  Ltac constr_prog := let t := eval unfold ProgMeta in (ProgMeta _ _) in exact t.

  Section clean.
    Hint Extern 0 _SrcVarTC => exact Vars : typeclass_instances.
    Hint Extern 0 _DstVarTC => exact Vars : typeclass_instances.

    Definition CleanValExp := ltac:(constr_valexp).
    Definition CleanBoolExp := ltac:(constr_boolexp).
    Definition CleanCmd := ltac:(constr_cmd).
    Definition CleanProg := ltac:(constr_prog).
  End clean.

  Section atk.
    Hint Extern 0 _SrcVarTC => exact AtkVarSrc : typeclass_instances.
    Hint Extern 0 _DstVarTC => exact AtkVarDst : typeclass_instances.

    Definition AtkValExp := ltac:(constr_valexp).
    Definition AtkBoolExp := ltac:(constr_boolexp).
    Definition AtkCmd := ltac:(constr_cmd).
    Definition AtkProg := ltac:(constr_prog).
  End atk.

End syntax.

Section syntax_erase.
  Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.

  Definition erase_val_exp (exp : AtkValExp) : CleanValExp :=
    let: (mk_vl_exp v1 v2 comp) := exp in (* Weird pattern matching.. *)
    mk_vl_exp _ (erase_var_src v1) (erase_var_src v2) comp.

  Definition erase_bool_exp (exp : AtkBoolExp) : CleanBoolExp :=
    let: (mk_bl_exp v test) := exp in 
    mk_bl_exp _ (erase_var_src v) test.


  (* If map is opaque, I think that this would fail. *)
  (* The termination checker cannot handle mutual recursion. Weird.*)
  Notation erase_prog' p erase_cmd  := (map erase_cmd p).

  Fixpoint erase_cmd (a_cmd : AtkCmd) : CleanCmd :=
    match a_cmd with
    | assign v exp => assign _ _ (erase_var_dst v) (erase_val_exp exp)
    | cond test b1 b2 =>  cond _ _ (erase_bool_exp test) (erase_prog' b1 erase_cmd ) (erase_prog' b1 erase_cmd)
    | while test p => while _ _ (erase_bool_exp test) (erase_prog' p erase_cmd)
    end.
  
  Definition erase_prog p := erase_prog' p erase_cmd.
End syntax_erase.


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
    | assignment (optupd: option (Vars * Vals)) (optlk : option LeakVals) 
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

  (* Maybe define this with iter nat *)
  Fixpoint multi_step (cfg : Cfg) (n : nat) : Cfg * Event := 
    if n isn't S n' then step cfg else 
    let: (cfg, _) := multi_step cfg n' in
    step cfg.

  Print multi_step.

  (* 
    What does behavior of program mean? 
  *)
  Parameter Behavior : Type.
  Parameter prog_behavior : Behavior -> Type.
  (* 
  Definition Behavior := Store -> nat -> Event.
  (* I think that it is possible to use iter_nat to make this so much simpler *)
  (* 
    TODO: I feel like this says nothing about the initial state.  
    Perhaps that is okay?
    I feel like the right way to have solved this would have been
    Parameter Behavior and parameter prog_behavior..

    This is wrong anyway. We're letting the environment choose all input values.
    The adversary needs a way to learn what the inputs are.
    - There are a few other ways to get this done, I think...
 *)
  Definition prog_behavior (p : Prog) : Behavior := 
    fun store_init step_cnt =>
      let: init_cfg := mk_cfg store_init adv_init p in
      let: multi_step := 
        fix multi_step cfg n {struct n} :=
            if n isn't S n' then step cfg else 
            let: (cfg, _) := multi_step cfg n' in
            step cfg
      in 
      let: (_, ret) := multi_step init_cfg step_cnt in
      ret.

 *)
End semantics.
(* Now, you need to  *)
