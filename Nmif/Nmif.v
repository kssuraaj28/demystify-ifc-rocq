From Stdlib Require Import (*Arith*) List String ssreflect ssrbool.
From QuickChick Require Import Decidability. 
From Ltac2 Require Import Ltac2. Set Default Proof Mode "Classic".
(* QuickCheck decidable equality classes are so good *)
(* ssreflect for gallina extensions *)
(* Arith for iter_nat *)
(* ssrbool for boolean predicates *)

Ltac2 goals l :=
  let name_goal x := ltac1:(x |- refine ?[x]) (Ltac1.of_ident x) in
  Control.dispatch (List.map (fun x () => name_goal x) l).

Class VarPrm := {Vars : Type ; vars_deceq :: Dec_Eq Vars}. 
Class ValPrm := {Vals : Type}.

(* This can be used in more places. TODO *)
Ltac hnf_clean def :=
    let t := def in
    let t := eval red in t in 
    let t := eval hnf in t in 
    exact t.


Module MetaSyntax.
  Class SrcDstVarPrm := {SrcVarMeta : Type ; DstVarMeta : Type}.

  (* TODO: There needs to be a good eval thing *)
  Section meta_syntax.
    Context `{!VarPrm, !ValPrm}.

    Context `{!SrcDstVarPrm}.

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
        case => c; by [t assign | t cond | t while].
      Qed.

    End cmd_ind.

    (* It is a little weird that a very syntactic  *_ind approach is used. *)
    Goal forall c : CmdMeta, c = c. Proof. elim; reflexivity. Qed. 
  End meta_syntax.

  Class SrcDstPredPrm `{!SrcDstVarPrm}
    := {SrcPred : (SrcVarMeta -> Prop); DstPred : (DstVarMeta -> Prop)}.

  Section syntax_pred.
    Context `{!VarPrm, !ValPrm}.

    Context `{!SrcDstVarPrm,!SrcDstPredPrm}.

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

  (* Bundling is a little bit sad. *)
  Class SynTransPrm := {
    Lang1: SrcDstVarPrm; 
    Lang2: SrcDstVarPrm;
    src_trans: @SrcVarMeta Lang1 -> @SrcVarMeta Lang2;
    dst_trans: @DstVarMeta Lang1 -> @DstVarMeta Lang2
  }.

  Section syntax_transform.
    Context `{!VarPrm, !ValPrm}.
    Context `{!SynTransPrm}.


    (* This should be refactored out. TODO *)
    Ltac clean cons := 
      let t := cons in
      let t := eval hnf in t in
      let t := eval unfold Lang1, Lang2, src_trans, dst_trans in t in
      let t := eval hnf in t in
      exact t.

    (* Don't double colon!! *)
    Fail Check ltac:(exact(_ : SrcDstVarPrm)). 

    Existing Instance Lang1. Check ltac:(exact(_ : SrcDstVarPrm)). 
      Let ValExp1 := ltac:(clean ValExpMeta).
      Let BoolExp1 := ltac:(clean BoolExpMeta).
      Let Cmd1 := ltac:(clean CmdMeta).
      Let Prog1 := ltac:(clean ProgMeta).
    Remove Hints Lang1: typeclass_instances. Fail Check ltac:(exact(_ : SrcDstVarPrm)). 


    Existing Instance Lang2. Check ltac:(exact(_ : SrcDstVarPrm)). 
      Let ValExp2 := ltac:(clean ValExpMeta).
      Let BoolExp2 := ltac:(clean BoolExpMeta).
      Let Cmd2 := ltac:(clean CmdMeta).
      Let Prog2 := ltac:(clean ProgMeta).
    Remove Hints Lang2: typeclass_instances. Fail Check ltac:(exact(_ : SrcDstVarPrm)). 

    (* I think that this can be abstracted out? *)
    Ltac unfold_clean cons :=
      let t := cons in 
      let t := eval hnf in t in
      let t := eval unfold
        ValExp1,BoolExp1,Cmd1,Prog1,
        ValExp2,BoolExp2,Cmd2,Prog2,
        Lang1, Lang2, src_trans, dst_trans
        in t in
      let t := eval hnf in t in
      exact t.

    Definition val_exp_trans (exp : ltac:(unfold_clean ValExp1)) : ltac:(unfold_clean ValExp2) :=
      ltac:(unfold_clean( 
      let: (mk_vl_exp v1 v2 comp) := exp in 
      mk_vl_exp (src_trans v1) (src_trans v2) comp
      )).

    Definition bool_exp_trans (exp : ltac:(unfold_clean BoolExp1)) : ltac:(unfold_clean BoolExp2) :=
      ltac:(unfold_clean( 
      let: (mk_bl_exp v test) := exp in 
      mk_bl_exp (src_trans v) test
      )).

    (* If map is opaque, I think that this would fail. *)
    (* The termination checker cannot handle mutual recursion. Weird.*)
    Notation prog_trans' p cmd_trans  := (map cmd_trans p).

    Fixpoint cmd_trans (a_cmd : ltac:(unfold_clean Cmd1)) : ltac:(unfold_clean Cmd2) :=
      ltac:(unfold_clean(
      match a_cmd with
      | assign v exp => assign (dst_trans v) (val_exp_trans exp)
      | cond test b1 b2 =>  cond (bool_exp_trans test) (prog_trans' b1 cmd_trans ) (prog_trans' b1 cmd_trans)
      | while test p => while (bool_exp_trans test) (prog_trans' p cmd_trans)
      end)).
    Definition prog_trans p := ltac:(unfold_clean (prog_trans' p cmd_trans)).
  End syntax_transform.

End MetaSyntax. 

Module CleanSyntax.
  Import MetaSyntax.
  Section clean_syntax.
    Context `{!VarPrm, !ValPrm}.

    Definition VarSrc := Vars.
    Definition VarDst := Vars.

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := VarSrc; DstVarMeta := VarDst|}) : typeclass_instances.

    Definition ValExp := ValExpMeta.
    Definition BoolExp := BoolExpMeta.
    Definition Cmd := CmdMeta.
    Definition Prog := ProgMeta.
  End clean_syntax.
End CleanSyntax.

Section store.
  Context `{!VarPrm, !ValPrm}.

  Definition Store := Vars -> Vals.
  Definition get_from_store (st : Store) (v : Vars) : Vals := st v.
  Definition update_to_store (st : Store) (v : Vars) (vl : Vals) : Store := 
    fun v' => if (v = v')? is true then vl else st v'.  (* The double colon in vars_deceq is needed here. *)

  Definition StoreView (p : pred Vars) := {v: Vars | p v} -> Vals.

  (* Maybe we can make this a coercion? *)
  Definition construct_view (s : Store) {p} : StoreView p :=
      fun vp =>
        let: exist x _ := vp in 
        s x.
End store.

Module AtkSyntax.
  (* The type of messages that the adversary leaks.
  I made this a operational typeclass for some reason... *)
  Module Prms.
    Class AdvLeakPrm := LeakVals : Type. 


    (* We also need to specify what variables the adversary has access to*)
    Class AdvLvlPrm  `{!VarPrm} := {
      is_untrusted : pred Vars ; 
      is_public : pred Vars
    }.

    (* 
      When you instantiate an adversary, you also give it memory.
      The adversary gets to access the public view of the store and initialize memory
      TODO: Eventually, we should also let it corrupt memory.
      Should we let the adversary leak a value initially? 
    *)

    Class AdvDevicePrm  `{!VarPrm, !ValPrm, !AdvLvlPrm} := { 
        AdvMem : Type; 
        adv_mem_init : StoreView is_public -> AdvMem;
        adv_maul_init : {v: Vars | is_untrusted v} -> Vals -> Vals 
        (* 
          I guess that there are other things that can be done:
          - StoreView is_untrusted -> StoreView is_untrusted
          Here, you can maul in a slightly weirder way
        *)
      }.
  End Prms.

  Import Prms.
  Import MetaSyntax.

  Section atksyntax.
    Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm, !AdvDevicePrm}.

    (* When you write to an adversary readable variable, the adversary can exfiltrate the value *)
    Definition AdvExfiltrator := Vals -> AdvMem -> (LeakVals * AdvMem).

    (* When you read from  an adversary writable variable, the adversary can maul *)
    Definition AdvCorruptor := Vals -> AdvMem -> Vals. 

    (* 
       Maybe think about other ways? I use computation here.. 
       Maybe the equations plugin helps..
    *)
    Notation SrcAttachment v :=
      (if (is_untrusted v) is true then AdvCorruptor else unit).

    Notation DstAttachment v :=
      (if (is_public v) is true then AdvExfiltrator else unit).

    (* 
      In order to construct these vars, you may have to do dependent pattern matching. 
      I don't know how much it will bite us.
      The other way to do it is +
    *)
    Definition VarSrc := {v : Vars & SrcAttachment v}.  
    Definition VarDst := {v : Vars & DstAttachment v}.  

    Hint Extern 0 SrcDstVarPrm => 
      (exact {|SrcVarMeta := VarSrc; DstVarMeta := VarDst|}) : typeclass_instances.

    Definition ValExp := ValExpMeta.
    Definition BoolExp := BoolExpMeta.
    Definition Cmd := CmdMeta.
    Definition Prog := ProgMeta.
  End atksyntax.

  Section syntax_erase.
    Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm, !AdvDevicePrm}.

    Notation AtkSrc := AtkSyntax.VarSrc.
    Notation AtkDst := AtkSyntax.VarDst.

    Notation CleanSrc := CleanSyntax.VarSrc.
    Notation CleanDst := CleanSyntax.VarDst.

    Import SigTNotations.
    Definition erase_var_src (vs : AtkSrc) : CleanSrc := 
      let: (v; _) := vs in v.
    Definition erase_var_dst (vd : AtkDst) : CleanDst := 
      let: (v; _) := vd in v.

    Notation L1 := 
      {|SrcVarMeta := AtkSrc; DstVarMeta := AtkDst |}.
    Check ltac:(exact L1).

    Notation L2 := 
      {|SrcVarMeta := CleanSrc; DstVarMeta := CleanDst |}.
    Check ltac:(exact L2).

    Hint Extern 0 SynTransPrm => (exact {|
      Lang1 := L1;
      Lang2 := L2;
      src_trans := erase_var_src;
      dst_trans := erase_var_dst;
    |}) : typeclass_instances.
    Check ltac:(exact(_ : SynTransPrm)).

    Definition erase_val_exp := Eval red in val_exp_trans.
    Definition erase_bool_exp := Eval red in bool_exp_trans.
    Definition erase_cmd := Eval red in cmd_trans.
    Definition erase_prog := Eval red in prog_trans.
  End syntax_erase.
End AtkSyntax.


Section semantics.
  Import MetaSyntax AtkSyntax.Prms.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm, !AdvDevicePrm}.
  Notation AtkProg := AtkSyntax.Prog.
  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.
  Notation AtkValExp := AtkSyntax.ValExp.
  Notation AtkBoolExp := AtkSyntax.BoolExp.

  (* What is 'state'? *)
  Inductive Cfg := mk_cfg (store : Store) (amem: AdvMem) (cont : AtkProg).

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

  (* 
    For dependent pattern matching, there seem to be the following appraoches:
    - Painfully write using gallina 
    - Use proof mode.
      - Normal? 
      - ssreflect? `Show Proof` is disgusting
    - Use equations plugin
  I use normal because ssreflect is too magical.
  Also, I have eqn:E and stuff, which I don't know how to do using ssreflect
  case E: X might be okay. However, ssreflect tactics seem to have trouble with typeclasses..
  Another thing I don't like is destruct doing a let definition

  With normal, I don't like how destruct makes a new let definition.
  Perhaps the right way to solve this is targeted cbv zeta, which is not possible also
  I think that nonmagical coq tactics are the way to go..

  Maybe use destruct along with move?
  *)
  Section def.
    Let def (st : Store) (vs : AtkVarSrc) (amem : AdvMem) : Vals. Proof.
      destruct vs as [v adv].
      pose (orig_val := get_from_store st v). (* What does () make?  *)
      destruct (is_untrusted v); ltac2:(goals [@UNTR; @TR]).
      [UNTR]: { exact (adv orig_val amem). }
      [TR]: { exact (orig_val). }
    Defined.

    Definition store_read_w_adv := ltac:(hnf_clean def).
  End def.

  Definition val_exp_eval (e : AtkValExp) (store : Store) (amem : AdvMem) : Vals :=
    let: mk_vl_exp vs1 vs2 comp := e in
    let: get_val := fun vs => store_read_w_adv store vs amem in 
    let: val1 := get_val vs1 in
    let: val2 := get_val vs2 in
    comp val1 val2.

  Definition bool_exp_eval (be : AtkBoolExp) (store : Store) (amem : AdvMem) : bool :=
    let: mk_bl_exp vs test := be in
    let: val := store_read_w_adv store vs amem in 
    test val.

  (* Maybe using the equations plugin is the right way to handle this.. *)
  Section def.
    Let def (s : Store) (vd : AtkVarDst) (vl : Vals) (amem : AdvMem) : 
          Store * AdvMem * Event. Proof.
      destruct vd as [v exf].
      pose (s' := update_to_store s v vl).
      pose (optupd := if (is_untrusted v) is true then None else Some (v,vl)). (* Here () makes a difference TODO *)
      destruct (is_public v); ltac2:(goals [@PUB; @SEC]).
      [PUB]: {
        destruct (exf vl amem) as [lk amem'].
        exact (s', amem', assignment optupd (Some lk)).
        }
      [SEC]: {
        exact (s', amem, assignment optupd None).
        }
    Defined.
  Definition store_update_w_adv := ltac:(hnf_clean def).
  End def.

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

  Import ListNotations.
  Notation NeList A := (A * list A)%type.

  Fixpoint multi_step (n : nat) (cfg: Cfg) : NeList (Cfg * Event) :=
    match n with 
    | 0 => (step cfg, [])
    | S n' =>
        let: ((cfg', ev'), lst') := multi_step n' cfg in
        (step cfg', (cfg', ev') :: lst') (* This naming is a little stupid *)
    end.

  Definition Behavior := Store -> nat -> list Event.

  Section def.
    Let def (s : Store) : Store. Proof.
      intro v.
      pose (orig_val := s v).
      destruct (is_untrusted v) eqn: VEq; ltac2:(goals [@UNTR; @TR]).
      [UNTR]: { apply adv_maul_init; [esplit; exact VEq | exact orig_val]. }
      [TR]: { exact (orig_val). }
    Defined.
    Definition init_source_maul := ltac:(hnf_clean def).
  End def.

  (* These names are absolutely disgusting. TODO *)
  Definition prog_behavior (p : AtkProg) : Behavior := 
    fun store_init step_cnt =>
      let: init_adv := adv_mem_init (construct_view store_init) in
      let: init_store := init_source_maul store_init in
      let: init_cfg := mk_cfg store_init init_adv p in
      let: ((_, ev), lst) := multi_step step_cnt init_cfg in
      ev :: map snd lst.

End semantics.
Notation "⟦ p ⟧" := (prog_behavior p).

Section sim_security.
  (* You need a type and an interpretation as an AdvCorruptor *)
  (* You need a type and an interpretation as an AdvInfiltrator *)
  (* You could also have a predicate on AdvCorruptors.. *)
  Import MetaSyntax.
  Import AtkSyntax.Prms.
  Import AtkSyntax (AdvCorruptor, AdvExfiltrator, erase_prog).
  Notation CleanProg := CleanSyntax.Prog.
  Notation AtkProg := AtkSyntax.Prog.
  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.


  Context `{!VarPrm, !ValPrm, !AdvLeakPrm, !AdvLvlPrm}.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.
  Check ltac:(exact SrcDstVarPrm).

  (* What went up must come down *)
  Variable IdealCorruptor : forall `{!AdvDevicePrm},  AdvCorruptor -> Prop.
  Variable IdealExfiltrator : forall `{!AdvDevicePrm}, AdvExfiltrator -> Prop.

  Section lift.
    Context `{!AdvDevicePrm}.

    (* I don't use exact: in def. *)
    Section def.
      Let def (vs : AtkVarSrc) : Prop. Proof.
        move: vs => [v].
        case: (is_untrusted v) => [corr | _].
        - exact (IdealCorruptor corr).
        - exact (True).
      Defined.

      Definition IdealSrcVar := 
        ltac:(
          let t := def in
          let t := eval hnf in t in 
          let t := eval cbv zeta in t in
          exact t).
    End def.

    Section def.
      Let def (vd : AtkVarDst) : Prop. Proof.
        move: vd => [v].
        case: (is_public v) => [exf | _].
        - exact (IdealExfiltrator exf).
        - exact (True).
      Defined.

    Definition IdealDstVar := ltac:(
      let t := def in 
      let t := eval hnf in t in
      let t := eval cbv zeta in t in
      exact t).
    End def.

    Hint Extern 0 SrcDstPredPrm => exact ({|
        SrcPred := IdealSrcVar;
        DstPred := IdealDstVar;
    |}) : typeclass_instances.

    (* This namespacing thing is stupid. TODO *)
    Definition IdealProg := MetaSyntax.ProgPred.
  End lift.

  Let ExpAtkProg (m: AdvDevicePrm) : Type := AtkProg.

  Definition atk_sim_sec (p : CleanProg) := Eval unfold ExpAtkProg in
    forall rad (rp : ExpAtkProg rad),  erase_prog rp = p ->
    exists iad (ip : ExpAtkProg iad),  erase_prog ip = p /\
    IdealProg ip /\
    ⟦ rp ⟧ = ⟦ ip ⟧.
End sim_security.

Section nmif.
  Import MetaSyntax AtkSyntax.Prms.
  Import AtkSyntax (AdvCorruptor, AdvExfiltrator).
  Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

  Definition NmifCorruptor `{!AdvDevicePrm} (corr : AdvCorruptor) : Prop := 
    forall mem v1 v2, corr v1 mem = corr v2 mem.

  (* TODO: What happens when you make the variable thing have explicit param? 
  I think that there should be no change? *)
  Definition NmifSecurity := atk_sim_sec (fun _ => NmifCorruptor) (fun _ _ => True).
End nmif.

Section ni.
  Import MetaSyntax AtkSyntax.Prms.
  Import AtkSyntax (AdvCorruptor, AdvExfiltrator).
  Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

  (* Noop *)
  Definition NICorruptor `{!AdvDevicePrm} (corr : AdvCorruptor) : Prop := 
    forall mem v, corr v mem = v.

  Definition NIExfiltrator `{!AdvDevicePrm} (exf : AdvExfiltrator) : Prop :=
    forall v1 v2 amem,
      exf v1 amem = exf v2 amem.

  (* TODO: What happens when you make the variable thing have explicit param? 
  I think that there should be no change? *)
  Definition NISecurity := atk_sim_sec (fun _ => NICorruptor) (fun _ => NIExfiltrator).
End ni.

Section rd.
  Import MetaSyntax AtkSyntax.Prms.
  Import AtkSyntax (AdvCorruptor, AdvExfiltrator).
  Context `{!VarPrm, !ValPrm,!AdvLeakPrm, !AdvLvlPrm}.

  Notation AtkVarSrc := AtkSyntax.VarSrc.
  Notation AtkVarDst := AtkSyntax.VarDst.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := AtkVarSrc; DstVarMeta := AtkVarDst|}) : typeclass_instances.

  (* Passive *)
  Definition RDCorruptor `{!AdvDevicePrm} (corr : AdvCorruptor) : Prop := 
    forall mem v, corr v mem = v.

  (* TODO: What happens when you make the variable thing have explicit param? 
  I think that there should be no change? *)
  Definition RDSecurity := atk_sim_sec (fun _ => RDCorruptor) (fun _ _ => True).
End rd.

(* To define program behavior, 
   we can just define mem_init, 
   So, this can initialize adversary memory, 
   and maybe leak something to the adversary initially as well.
   The order should be leak then corrupt.
   We can then think about
   

   Another thing to keep in mind is that we might want to
   count the number of while iterations.


*)
