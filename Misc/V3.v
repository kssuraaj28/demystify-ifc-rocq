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
    Context `{!CfgVar Type "src", !CfgVar Type "dst"}.

  (* TODO: I have no idea how this works/ why. I think this is because of some eauto thing.
     To be more specific, I don't know why cfg_val does not infer the right thing. *)
    (* TODO: SrcVar needn't be notation anymore. Check *)
    Definition SrcVarMeta := (cfg_val "src").
    Definition DstVarMeta := (cfg_val "dst").

    (* v1 ∘ v2. Some binary operation *)
    Inductive ValExpMeta := mk_vl_exp (v1 v2: SrcVarMeta) (comp : Vals -> Vals -> Vals).
    Inductive BoolExpMeta :=  mk_bl_exp (v: SrcVarMeta) (test : Vals -> bool).

    Section cmd.
      Notation ProgMeta' CmdMeta := (list CmdMeta).

      Unset Elimination Schemes. Inductive CmdMeta :=
        | assign (d : DstVarMeta) (exp : ValExpMeta)
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

  Section syntax_pred.
    Context `{!VarPrm, !ValPrm}.
    (* Maybe I should be more uniform. I do use this a lot.. *)
    Context `{!CfgVar Type "src", !CfgVar Type "dst"}. 
    Context `{!CfgVar (SrcVarMeta -> Prop) "srcpred", !CfgVar (DstVarMeta -> Prop) "dstpred"}. 

    (* TODO: Make this ltac *)
    Notation SrcPred := (cfg_val "srcpred"). Check ltac:(exact SrcPred).
    Notation DstPred := (cfg_val "dstpred"). Check ltac:(exact DstPred).

    Definition ValExpPred (exp: ValExpMeta): Prop :=
      let: mk_vl_exp vs1 vs2 _ := exp in
      SrcPred vs1 /\ SrcPred vs2.

    Definition BoolExpPred (exp: BoolExpMeta):  Prop :=
      let: mk_bl_exp vs test := exp in
      SrcPred vs.

    Notation ProgPred' CmdPred prog :=  
      (fold_left (fun rest cmd => rest /\ CmdPred cmd) prog True).

    Fixpoint CmdPred (cmd: CmdMeta) : Prop :=
      match cmd with
      | assign vd exp => DstPred vd /\ ValExpPred exp
      | cond exp b1 b2 => 
          BoolExpPred exp /\ 
          ProgPred' CmdPred b1 /\
          ProgPred' CmdPred b2
      | while exp while_bdy  => 
          BoolExpPred exp /\ 
          ProgPred' CmdPred while_bdy
      end.

    Definition ProgPred prog := ProgPred' CmdPred prog.
  End syntax_pred.

  (* Here, we give helper functions to transform syntax *)
  Section syntax_transform.
    Context `{!VarPrm, !ValPrm}.

    Context `{!CfgVar Type "src1", !CfgVar Type "dst1"}.
    Context `{!CfgVar Type "src2", !CfgVar Type "dst2"}.

    (* I don't know why I had to do @. TODO *)
    Let SrcVar1 : CfgVar Type "src" := (@cfg_val Type "src1" _). 
    Let DstVar1 : CfgVar Type "dst" := (@cfg_val Type "dst1" _). 
    Let SrcVar2 : CfgVar Type "src" := (@cfg_val Type "src2" _). 
    Let DstVar2 : CfgVar Type "dst" := (@cfg_val Type "dst2" _). 

    Ltac unfold_clean cons :=
      let t := constr:(cons) in 
      let t := eval cbv delta [SrcVar1 DstVar1 SrcVar2 DstVar2 cfg_val] in t in
      let t := eval hnf in t in (* TODO: Is this needed? *)
      exact t.

    (* We need to force typeclass resolution *)
    Existing Instance SrcVar1. Existing Instance DstVar1.
    Let ValExp1 := ltac:(unfold_clean ValExpMeta).
    Let BoolExp1 := ltac:(unfold_clean BoolExpMeta).
    Let Cmd1 := ltac:(unfold_clean CmdMeta).
    Let Prog1 := ltac:(unfold_clean ProgMeta).
    Remove Hints DstVar1 SrcVar1 : typeclass_instances.   (* TODO: Add HL *)


    Existing Instance SrcVar2. Existing Instance DstVar2.
    Let ValExp2 := ltac:(unfold_clean ValExpMeta).
    Let BoolExp2 := ltac:(unfold_clean BoolExpMeta).
    Let Cmd2 := ltac:(unfold_clean CmdMeta).
    Let Prog2 := ltac:(unfold_clean ProgMeta).
    Remove Hints DstVar2 SrcVar2 : typeclass_instances.   (* TODO: Add HL *)

    Ltac unfold_clean cons ::=
      let t := eval cbv delta [
        SrcVar1 DstVar1 ValExp1 BoolExp1 Cmd1 Prog1
        SrcVar2 DstVar2 ValExp2 BoolExp2 Cmd2 Prog2
        cfg_val
        ] in cons in
      exact t.

    (* Ideally, we would define all of these above.
      I don't like that these take in parameters?
    *)
    Definition SrcTrans := (
      ltac:(unfold_clean SrcVar1) -> 
      ltac:(unfold_clean SrcVar2)).

    Definition DstTrans := (
      ltac:(unfold_clean DstVar1) -> 
      ltac:(unfold_clean DstVar2)).

    Context `{!CfgVar SrcTrans "src_trans", !CfgVar DstTrans "dst_trans"}.

    Ltac src_trans := 
      let t := constr:(cfg_val "src_trans") in
      let t := eval hnf in t in
      exact t.

    Ltac dst_trans := 
      let t := constr:(cfg_val "dst_trans") in
      let t := eval hnf in t in
      exact t.

    Definition val_exp_trans (exp : ltac:(unfold_clean ValExp1)) : ltac:(unfold_clean ValExp2) :=
      let: (mk_vl_exp v1 v2 comp) := exp in 
      mk_vl_exp (ltac:(src_trans) v1) (ltac:(src_trans) v2) comp.

    Definition bool_exp_trans (exp : ltac:(unfold_clean BoolExp1)) : ltac:(unfold_clean BoolExp2) :=
      let: (mk_bl_exp v test) := exp in 
      mk_bl_exp (ltac:(src_trans) v) test.

    (* If map is opaque, I think that this would fail. *)
    (* The termination checker cannot handle mutual recursion. Weird.*)
    Notation prog_trans' p cmd_trans  := (map cmd_trans p).

    Fixpoint cmd_trans (a_cmd : ltac:(unfold_clean Cmd1)) : ltac:(unfold_clean Cmd2) :=
      match a_cmd with
      | assign v exp => assign (ltac:(dst_trans) v) (val_exp_trans exp)
      | cond test b1 b2 =>  cond (bool_exp_trans test) (prog_trans' b1 cmd_trans ) (prog_trans' b1 cmd_trans)
      | while test p => while (bool_exp_trans test) (prog_trans' p cmd_trans)
      end.
    Definition prog_trans p := prog_trans' p cmd_trans.
  End syntax_transform.

End MetaSyntax.

Module CleanSyntax.
  Import MetaSyntax.
  Section clean_syntax.
    Context `{!VarPrm, !ValPrm}.
    Instance VarSrc : CfgVar Type "src" := Vars.
    Instance VarDst : CfgVar Type "dst" := Vars.


    Set Printing Implicit.
    Definition ValExp := Eval hnf in ValExpMeta.
    Definition BoolExp := Eval hnf in BoolExpMeta.
    Definition Cmd := Eval hnf in CmdMeta.
    Definition Prog := Eval hnf in ProgMeta.
  End clean_syntax.
End CleanSyntax.

Module AtkSyntax.
  (* The type of messages that the adversary leaks *)
  Class AdvLeakParam := {LeakVals : Type}. 

  (* When you instantiate an adversary, you also give it memory *)
  Class AdvMemParam := {AdvMem : Type; adv_init : AdvMem}.

  Import MetaSyntax.
  Section atksyntax.
    Context `{!VarPrm, !ValPrm, !AdvLeakParam, !AdvMemParam}.

    (* When you write to an adversary readable variable, the adversary can exfiltrate the value *)
    Definition AdvExfiltrator := Vals -> AdvMem -> (LeakVals * AdvMem).

    (* When you read from  an adversary writable variable, the adversary can maul *)
    Definition AdvCorruptor := Vals -> AdvMem -> Vals. 

    Instance VarSrc : CfgVar Type "src" := (Vars * AdvCorruptor)%type.
    Instance VarDst : CfgVar Type "dst" := (Vars * AdvExfiltrator)%type.

    Definition ValExp := Eval hnf in ValExpMeta.
    Definition BoolExp := Eval hnf in BoolExpMeta.
    Definition Cmd := Eval hnf in CmdMeta.
    Definition Prog := Eval hnf in ProgMeta.
  End atksyntax.

  Section syntax_erase.
    Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam}.

    Hint Extern 0 (CfgVar Type "src1") => exact AtkSyntax.VarSrc : typeclass_instances.
    Hint Extern 0 (CfgVar Type "dst1") => exact AtkSyntax.VarDst : typeclass_instances.

    Hint Extern 0 (CfgVar Type "src2") => exact CleanSyntax.VarSrc : typeclass_instances.
    Hint Extern 0 (CfgVar Type "dst2") => exact CleanSyntax.VarDst : typeclass_instances.

    Instance erase_var_src : CfgVar SrcTrans "src_trans" :=
      fun vs => let: (v, _) := vs in v.

    Instance erase_var_dst : CfgVar DstTrans "dst_trans" :=
      fun vd => let: (v, _) := vd in v.

    (* TODO: Refactor and think *)
    Definition erase_val_exp := Eval hnf in val_exp_trans.
    Definition erase_bool_exp := Eval hnf in bool_exp_trans.
    Definition erase_cmd := Eval hnf in cmd_trans.
    Definition erase_prog := Eval hnf in prog_trans.
  End syntax_erase.

  Section atk_pred.
    Context `{!VarPrm, !ValPrm, !AdvLeakParam, !AdvMemParam}.

    Existing Instance VarSrc. Check ltac:(exact VarSrc).
    Existing Instance VarDst. Check ltac:(exact VarSrc). 

    Variable CorruptorPred : AdvCorruptor -> Prop.
    Variable ExfiltratorPred : AdvExfiltrator -> Prop.

    Instance VarSrcPred : CfgVar (SrcVarMeta -> Prop) "srcpred" :=
      fun vs => let (_, cor) := vs in CorruptorPred cor.

    Instance VarDstPred : CfgVar (DstVarMeta -> Prop) "dstpred" :=
      fun vd => let (_, exf) := vd in ExfiltratorPred exf.

    Definition CorruptorRestricted := Eval hnf in ProgPred.
  End atk_pred.
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


Section sim_security.
  (* You need a type and an interpretation as an AdvCorruptor *)
  (* You need a type and an interpretation as an AdvInfiltrator *)
  (* You could also have a predicate on AdvCorruptors.. *)
  Import AtkSyntax (AdvMemParam, AdvLeakParam, AdvCorruptor, AdvExfiltrator, erase_prog).
  Notation CleanProg := CleanSyntax.Prog.
  Notation AtkProg := AtkSyntax.Prog.

  Context `{!VarPrm, !ValPrm, !AdvLeakParam}.

  (* What went up must come down *)
  Variable CorruptorPred : forall {memprm: AdvMemParam},  AdvCorruptor -> Prop.
  Variable ExfiltratorPred : forall {memprm: AdvMemParam}, AdvExfiltrator -> Prop.

  (* 
     This is what we want.. 
     This is a little bit stupid..
  *)
  Definition AtkProgPred {memprm: AdvMemParam} :=
    AtkSyntax.CorruptorRestricted CorruptorPred ExfiltratorPred.

  Definition atk_sim_sec (p : CleanProg) := 
    forall (rm: AdvMemParam) (rp : AtkProg),  erase_prog rp = p ->
    exists (im: AdvMemParam) (ip : AtkProg),  erase_prog ip = p /\
    AtkProgPred ip /\
    prog_behavior rp = prog_behavior ip.
End sim_security.

(* The idea is that you give two predicates, *)
(* Define NMIF? *)

Module NMIF.
  Section nmif_syntax.
    Import MetaSyntax AtkSyntax. (* This should not be imported TODO *)
    Context `{!VarPrm, !ValPrm, !AdvMemParam, !AdvLeakParam, !AdvLvlParam}.
    Fail.
    Definition NonmaulingCorruptor := AtkSyntax.AdvMem -> Vals. 

    Instance VarSrc : CfgVar Type "src" := (Vars * NonmaulingCorruptor)%type.
    Instance VarDst : CfgVar Type "dst" := AtkSyntax.VarDst.

    Definition ValExp := Eval hnf in ValExpMeta.
    Definition BoolExp := Eval hnf in BoolExpMeta.
    Eval red in BoolExp.
      ltac:(constr_boolexp).
    Definition Cmd := ltac:(constr_cmd).
    Definition Prog := ltac:(constr_prog).
  End nmif_syntax.

  Section nmif_to_atk.
    Import MetaSyntax.
    Context `{!VarPrm, !ValPrm, !AtkSyntax.AdvMemParam, !AtkSyntax.AdvLeakParam}.

    Hint Extern 0 (CfgVar Type "src1") => exact NMIF.VarSrc : typeclass_instances.
    Hint Extern 0 (CfgVar Type "dst1") => exact NMIF.VarDst : typeclass_instances.

    Hint Extern 0 (CfgVar Type "src2") => exact AtkSyntax.VarSrc : typeclass_instances.
    Hint Extern 0 (CfgVar Type "dst2") => exact AtkSyntax.VarDst : typeclass_instances.

    (* I hope this is correct *)
    Instance interpret_var_src : CfgVar SrcTrans "src_trans" :=
      fun vs => let: (v, c) := vs in (v, fun _ i => c i). 

    Instance interpret_var_dst : CfgVar DstTrans "dst_trans" :=
      fun vd => vd.

    Definition interpret_val_exp := ltac:(constr_val_exp_trans).
    Definition interpret_bool_exp := ltac:(constr_bool_exp_trans).
    Definition interpret_cmd := ltac:(constr_cmd_trans).
    Definition interpret_prog := ltac:(constr_prog_trans). (* I wonder whether I can make this a coercion easily *)
  End nmif_to_atk.
End NMIF.



(* 
  The goal here is to define a predicate on Clean programs. 
*)
