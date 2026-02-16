From Stdlib Require Import (*Arith*) List String ssreflect.
From QuickChick Require Import Decidability. 
(* QuickCheck decidable equality classes are so good *)
(* ssreflect for gallina extensions *)
(* Arith for iter_nat *)

(* I'm just going to bundle stuff for now. The context is getting quite large otherwise.
*)
Class VarPrm := {Vars : Type ; vars_deceq :: Dec_Eq Vars}. 
Class ValPrm := {Vals : Type}.
(* 
   This should be a helper defined somewhere else. 
   There should be a string accessor
*)
Class CfgVar (T : Type) (id : string) := cfg_val : T.
Arguments cfg_val : clear implicits. Arguments cfg_val {_} id {_}.
(* Print Implicit cfg_val. *)


Module MetaSyntax.
  Section meta_syntax.
    (* I wonder whether all of this should be packaged into a single thing? I could do "SyntaxParams" *)
    Context `{!VarPrm, !ValPrm}.

    (* If I make this implicit it becomes a little hard to debug *)
    Context `(!CfgVar Type "src", !CfgVar Type "dst").

  (* TODO: I have no idea how this works/ why. I think this is because of some eauto thing.
     To be more specific, I don't know why cfg_val does not infer the right thing. *)
    Notation SrcVar := (cfg_val "src"). 
    Notation DstVar := (cfg_val "dst").

    (* v1 ∘ v2. Some binary operation *)
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

  Ltac constr_valexp := exact (ValExpMeta _). 
  Ltac constr_boolexp := exact (BoolExpMeta _).
  Ltac constr_cmd := exact (CmdMeta _ _).
  Ltac constr_prog := let t := eval unfold ProgMeta in (ProgMeta _ _) in exact t.

  (* Here, we give helper functions to transform syntax *)
  Section syntax_transform.
    Context `{!VarPrm, !ValPrm}.

    Context `(!CfgVar Type "src1", !CfgVar Type "dst1").
    Context `(!CfgVar Type "src2", !CfgVar Type "dst2").

    (* I don't know why I had to do @ *)
    Let SrcVar1 : CfgVar Type "src" := (@cfg_val Type "src1" _). 
    Let DstVar1 : CfgVar Type "dst" := (@cfg_val Type "dst1" _). 
    Let SrcVar2 : CfgVar Type "src" := (@cfg_val Type "src2" _). 
    Let DstVar2 : CfgVar Type "dst" := (@cfg_val Type "dst2" _). 
    Ltac erase_let cons :=
      let t := constr:(ltac:(cons)) in 
      let t := eval cbv delta [SrcVar1 DstVar1 SrcVar2 DstVar2] in t in
      exact t.

    (* We need to force typeclass resolution *)
    Existing Instance SrcVar1. Existing Instance DstVar1.
    Let ValExp1 := ltac:(erase_let constr_valexp).
    Let BoolExp1 := ltac:(erase_let constr_boolexp).
    Let Cmd1 := ltac:(erase_let constr_cmd).
    Let Prog1 := ltac:(erase_let constr_prog).
    Remove Hints DstVar1 SrcVar1 : typeclass_instances.   (* TODO: Add HL *)


    Existing Instance SrcVar2. Existing Instance DstVar2.
    Let ValExp2 := ltac:(erase_let constr_valexp).
    Let BoolExp2 := ltac:(erase_let constr_boolexp).
    Let Cmd2 := ltac:(erase_let constr_cmd).
    Let Prog2 := ltac:(erase_let constr_prog).
    Remove Hints DstVar2 SrcVar2 : typeclass_instances.   (* TODO: Add HL *)

    Ltac erase_let cons ::=
      let t := eval cbv delta [
        SrcVar1 DstVar1 ValExp1 BoolExp1 Cmd1 Prog1
        SrcVar2 DstVar2 ValExp2 BoolExp2 Cmd2 Prog2
        ] in cons in
      exact t.

    (* Ideally, we would define all of these above.
      I don't like that these take in parameters?
    *)
    Definition SrcTrans := (
      ltac:(erase_let SrcVar1) -> 
      ltac:(erase_let SrcVar2)).

    Definition DstTrans := (
      ltac:(erase_let DstVar1) -> 
      ltac:(erase_let DstVar2)).

    Context `(!CfgVar SrcTrans "src_trans", !CfgVar DstTrans "dst_trans").

    Notation src_trans := (cfg_val "src_trans"). Check ltac:(exact src_trans).
    Notation dst_trans := (cfg_val "dst_trans"). Check ltac:(exact dst_trans).

    Definition val_exp_trans (exp : ltac:(erase_let ValExp1)) : ltac:(erase_let ValExp2) :=
      let: (mk_vl_exp v1 v2 comp) := exp in (* Weird pattern matching.. *)
      mk_vl_exp _ (src_trans v1) (src_trans v2) comp.

    Definition bool_exp_trans (exp : ltac:(erase_let BoolExp1)) : ltac:(erase_let BoolExp2) :=
      let: (mk_bl_exp v test) := exp in 
      mk_bl_exp _ (src_trans v) test.

    (* If map is opaque, I think that this would fail. *)
    (* The termination checker cannot handle mutual recursion. Weird.*)
    Notation prog_trans' p cmd_trans  := (map cmd_trans p).

    Fixpoint cmd_trans (a_cmd : ltac:(erase_let Cmd1)) : ltac:(erase_let Cmd2) :=
      match a_cmd with
      | assign v exp => assign _ _ (dst_trans v) (val_exp_trans exp)
      | cond test b1 b2 =>  cond _ _ (bool_exp_trans test) (prog_trans' b1 cmd_trans ) (prog_trans' b1 cmd_trans)
      | while test p => while _ _ (bool_exp_trans test) (prog_trans' p cmd_trans)
      end.
    Definition prog_trans p := prog_trans' p cmd_trans.
  End syntax_transform.

  Arguments SrcTrans {_} {_}.
  Arguments DstTrans {_} {_}.

  (* This can be refactored *)
  Ltac constr_val_exp_trans := exact (val_exp_trans _ _ _).
  Ltac constr_bool_exp_trans := exact (bool_exp_trans _ _ _).
  Ltac constr_cmd_trans := exact (cmd_trans _ _ _ _ _ _).
  Ltac constr_prog_trans := exact (prog_trans _ _ _ _ _ _).

  Section test.
    Context `{!VarPrm, !ValPrm}.
    Context `(!CfgVar Type "src1", !CfgVar Type "dst1").
    Context `(!CfgVar Type "src2", !CfgVar Type "dst2").
    Context `(!CfgVar SrcTrans "src_trans").
    Context `(!CfgVar DstTrans "dst_trans").
    Check ltac:(constr_val_exp_trans).
    Check ltac:(constr_bool_exp_trans).
    Check ltac:(constr_cmd_trans).
    Check ltac:(constr_prog_trans).
  End test.

End MetaSyntax.

Module CleanSyntax.
  Import MetaSyntax.
  Section clean_syntax.
    Context `{!VarPrm, !ValPrm}.
    Instance VarSrc : CfgVar Type "src" := Vars.
    Instance VarDst : CfgVar Type "dst" := Vars.


    Definition ValExp := ltac:(constr_valexp).
    Definition BoolExp := ltac:(constr_boolexp).
    Definition Cmd := ltac:(constr_cmd).
    Definition Prog := ltac:(constr_prog).
    (* Eval hnf in CleanProg. *)
    (* Eval red  in CleanProg.  *)
  End clean_syntax.
End CleanSyntax.

Module AtkSyntax.
  (* The type of messages that the adversary leaks *)
  Class AdvLeakParam := {LeakVals : Type}. 

  (* When you instantiate an adversary, you also give it memory *)
  Class AdvMemParam := {AdvMem : Type; adv_init : AdvMem}.

  Import MetaSyntax.
  Section atksyntax.
    Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.

    (* When you write to an adversary readable variable, the adversary can exfiltrate the value *)
    Definition AdvExfiltrator := Vals -> AdvMem -> (LeakVals * AdvMem).

    (* When you read from  an adversary writable variable, the adversary can maul *)
    Definition AdvCorruptor := Vals -> AdvMem -> Vals. 

    Instance VarSrc : CfgVar Type "src" := (Vars * AdvCorruptor)%type.
    Instance VarDst : CfgVar Type "dst" := (Vars * AdvExfiltrator)%type.

    Definition ValExp := ltac:(constr_valexp).
    Definition BoolExp := ltac:(constr_boolexp).
    Definition Cmd := ltac:(constr_cmd).
    Definition Prog := ltac:(constr_prog).
  End atksyntax.
  
  Section syntax_erase.
    Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.

    Hint Extern 0 (CfgVar Type "src1") => exact VarSrc : typeclass_instances.
    Hint Extern 0 (CfgVar Type "dst1") => exact VarDst : typeclass_instances.

    Hint Extern 0 (CfgVar Type "src2") => exact CleanSyntax.VarSrc : typeclass_instances.
    Hint Extern 0 (CfgVar Type "dst2") => exact CleanSyntax.VarDst : typeclass_instances.

    Instance erase_var_src : CfgVar SrcTrans "src_trans" :=
      fun vs => let: (v, _) := vs in v.

    Instance erase_var_dst : CfgVar DstTrans "dst_trans" :=
      fun vd => let: (v, _) := vd in v.

    Definition erase_val_exp := ltac:(constr_val_exp_trans).
    Definition erase_bool_exp := ltac:(constr_bool_exp_trans).
    Definition erase_cmd := ltac:(constr_cmd_trans).
    Definition erase_prog := ltac:(constr_prog_trans).
  End syntax_erase.
End AtkSyntax.


Section store.
  Context `{!VarPrm, !ValPrm}.

  Definition Store := Vars -> Vals.
  Definition get_from_store (st : Store) (v : Vars) : Vals := st v.
  Definition update_to_store (st : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if (v = v')? is true then vl else st v'.  (* The double colon in vars_deceq is needed here. *)
End store.

(* We only give semantics to attacked programs *)
Class AdvLvlParam `{!VarPrm} := {is_untrusted : Vars -> bool ; is_public : Vars -> bool }.
Section semantics.
  Import MetaSyntax.
  Import AtkSyntax.
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
    let: (v, adv) := vs in 
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
    let: (v, adv) := vd in 
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


  (* 
    What does behavior of program mean? 
  *)
  Parameter Behavior : Type.
  Parameter prog_behavior : Prog -> Behavior.
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
(* Define NMIF? *)

Section nmif.
  Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam, !AdvLvlParam}.

  (* I will do magic trick now. After this you should be convinced.  *)
  Definition CorruptorNMIFOkay (ac:  AdvCorruptor) : Prop :=
    forall mem v1 v2, 
      ac v1 mem = ac v2 mem.

  Parameter AtkNMIFOkay:  AtkProg -> Prop.
  Definition SatsNMIF (p : CleanProg) : Prop :=
    forall rap, exists iap, erase_prog rap = p /\ erase_prog iap = p -> 
    AtkNMIFOkay iap /\
    prog_behavior iap = prog_behavior rap.

End nmif.
(* It should be a predicate on clean programs *)

