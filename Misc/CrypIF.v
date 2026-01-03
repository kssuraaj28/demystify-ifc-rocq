(* Here, the point is to show how the crypto view and the information flow view are equal, if you have nmif 
Let us start with a very simple program. Then we try to see how
*)

From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.

Import ListNotations.

Inductive Vars := st | pt | pu.
Definition var_eq_dec : forall (v v' : Vars), {v = v'} + {v <> v'}. Proof. decide equality. Defined.

Definition Value := nat.
Definition State :=  Vars -> Value.


Record ComputeData := { code : State -> Value ; cmp_lbl : Vars }. (* TODO: Maybe `code` should be a Coercion too *)


Definition WellFormedCompute (c : ComputeData) : Prop :=
  let (code, lbl) := c in 
  match lbl with 
  | pt => forall s s', 
      s pt = s' pt -> (* I should probably just use NI, which means I need to define this correctly *)
      code s = code s'

  | st => forall s s', 
      s pt = s' pt -> (* st can depend on pt and st *)
      s st = s' st ->
      code s = code s' 

  | pu => forall s s',
      s pt = s' pt ->  (* pu can depend on pu and pt *)
      s pu = s' pu ->
      code s = code s' 
  end. (* I could refactor. Or I could use NI. Or I could use lattice flow. For now, I don't care *)


Section test.
  (* This should go somewhere else *)
  Ltac print_goal :=
    match goal with
    | |- ?G => idtac "Current Goal is:" G
    end.

  (* Can I automatcially generate counterexamples? *)
  Ltac counterexample s1 s2:=
      repeat (
        intuition; 
        match goal with
        | [ H : WellFormedCompute _ |- _ ] => specialize (H s1 s2) 
        | [|- _] => discriminate
        end).

  Section pt_good.
    Let c :=  {| code := fun s => s pt; cmp_lbl := pt |}.
    Goal WellFormedCompute c. 
    Proof. 
      congruence.
    Qed.
  End pt_good.

  Section pt_bad.
    Let c :=  {| code := fun s => s pt + s st; cmp_lbl := pt |}.
    Goal ~ WellFormedCompute c. 
    Proof. 
      counterexample 
      (fun x => match x with st => 1 | _ => 0 end) 
      (fun x => match x with st => 2 | _ => 0 end).
    Qed.
  End pt_bad.

  Section st_good.
    Let c :=  {| code := fun s => s st + s pt; cmp_lbl := st |}.
    Goal WellFormedCompute c. 
    Proof. 
      congruence.
    Qed.
  End st_good.

  Section st_bad.
    Let c :=  {| code := fun s => s pu + s st; cmp_lbl := pt |}.
    Goal ~ WellFormedCompute c. 
    Proof. 
      counterexample 
      (fun x => match x with pu => 1 | _ => 0 end) (* TODO: What happens when you tacvalue  ltac: *)
      (fun x => match x with pu => 2 | _ => 0 end).
    Qed.
  End st_bad.

  Section pu_good.
    Let c :=  {| code := fun s => s pt * s pu + 102; cmp_lbl := pu |}.
    Goal WellFormedCompute c. 
    Proof. 
      congruence.
    Qed.
  End pu_good.

  Section pu_bad.
    Let c :=  {| code := fun s => s st + s pt; cmp_lbl := pu |}.
    Goal ~ WellFormedCompute c. 
    Proof. 
      counterexample 
      (fun x => match x with st => 1 | _ => 0 end) 
      (fun x => match x with st => 2 | _ => 0 end).
    Qed.
  End pu_bad.

End test.
(* I hope that the refinement types gods don't come for me *)
Definition Compute := {x : ComputeData | WellFormedCompute x}.  (* TODO: Can I coerce  *)
Definition compute_data (c: Compute) : ComputeData := proj1_sig c.
Coercion compute_data : Compute >-> ComputeData.


Record CmdData := {dest : Vars; comp : Compute}. 



Definition cmd_sem (c: CmdData) (s: State) : State := 
  fun var => 
    let (dest, comp) := c in (* TODO: What did I just do? *)
    let new_val := code comp s in (* There is some Coercion happening *)
    let old_val := s var in 
    if var_eq_dec var dest then 
      new_val
    else
      old_val.

(* There are illegal commands also.. *)
Inductive CmdKind := ni | endorse | declassify | illegal.

Definition cmd_kind (cmd : CmdData) : CmdKind :=
  let src_lvl := cmp_lbl (proj1_sig (comp cmd)) in
  let dest_lvl := dest cmd in
  match src_lvl, dest_lvl with 
  | pt, _ | st, st | pu, pu  => ni
  | pu, pt => endorse
  | st, pt => declassify
  | _, _ => illegal (* st pu and pu st *)
  end.

Definition Cmd := { c : CmdData | cmd_kind c <> illegal }. (* Dependent gods please save me *)
Definition cmd_to_data (c : Cmd) : CmdData := proj1_sig  c.
Coercion cmd_to_data : Cmd >-> CmdData.

Notation "v ← c" := ((exist _ {| dest := v ; comp := exist _ c _ |} _) : Cmd) (at level 20).
Check _ ← _ : Cmd.
(* This : Cmd helps force coercion. Otherwise, what we have below will not work*)
Check cmd_sem (_ ← _) _. 

Section test.
  Variable admit : forall {T}, T.
  Let s : State :=
    fun v => match v with
             | st => 67
             | pt => 3
             | pu => 58
             end.

  Let c : ComputeData :=
    {| code := fun s => s st + s pt + s pu ; cmp_lbl :=  admit |}. (* Actually, this Compute is illegal lmao *)

  Let s' : State. Proof. unshelve refine (cmd_sem (pu ← c) s); abstract exact admit. Defined. 
  (* Is there a shortcut for this?  Program fixpoint, for example?*)

  Goal s' pu = (s pu + s pt + s st). reflexivity. Qed.
  Goal s' pt = (s pt). reflexivity. Qed.
  Goal s' st = (s st). reflexivity. Qed.
End test.

Definition LeakVal := list Value.

Class AtkMemParam := { AtkState : Type ; init_val : AtkState }.

(* TODO: Perhaps wise to refactor the domain correctly? *)
Record AtkSnip {amem : AtkMemParam} := {
  pu_trans : AtkState  -> Value (* pt *) -> Value (* pu *) -> Value (* pu *)  ;
  mem_trans : AtkState -> Value (* pt *) -> Value (* pu *) -> AtkState ;
  leak : AtkState -> Value (* pt *) -> Value (* pu *) -> LeakVal ;
}.

Notation "☠︎︎ ⟨ pu | mem | lk ⟩" := 
    {|pu_trans := pu ; mem_trans := mem ; leak := lk|}.


Section comb.
  Context {amem : AtkMemParam}.
  Definition CombState : Type := State * AtkState.
End comb.

Section atksnip_sem.
  Context {amem : AtkMemParam}.

  Variables (a: AtkSnip) (cfg : CombState).

  Definition atksnip_sem : CombState * LeakVal :=
    let (s, s_atk) := cfg in
    let pu_v := pu_trans a s_atk (s pt) (s pu) in
    let s_atk' := mem_trans a s_atk (s pt) (s pu) in
    let leak := leak a s_atk (s pt) (s pu) in
    let s' := fun v => 
                if var_eq_dec v pu then (* You could probably refactor this.. *)
                  pu_v
                else
                  s v in
    let cfg' := (s', s_atk') in
    (cfg', leak).
End atksnip_sem.

Section test.
  Let s : State :=
    fun v => match v with
             | st => 67
             | pt => 3
             | pu => 58
             end.

  Section zero.
    Let amem : AtkMemParam := {| AtkState := unit ; init_val := tt |}.  Existing Instance amem.
    Let zero_atk : AtkSnip := ☠︎︎ ⟨ fun _ _ _ => 0 | fun x _ _ => x | fun m pt pu => [pt ; pu ; pu ; pt] ⟩.
    
    Let res := atksnip_sem zero_atk (s, tt). (* Can I not do copattern? *)

    Let cfg := fst res.
    Let leak := snd res.

    Let s_out := fst cfg.
    Let atk_mem := snd cfg.

    Goal s_out pu = 0. cbv. reflexivity. Qed.
    Goal s_out pt = s pt. cbv. reflexivity. Qed.
    Goal s_out st = s st. cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
    Goal atk_mem = tt. cbv. reflexivity. Qed. 
    Goal leak = [3; 58; 58; 3]. cbv. reflexivity. Qed.
  End zero.

  Section sum.
    Let amem : AtkMemParam := {| AtkState := nat ; init_val := 67 |}.  Existing Instance amem.
    Let sum_atk : AtkSnip := ☠︎︎ ⟨ fun m x y => m + x + y | fun x _ _ => x + 1 | fun m pt pu => [m ; pt ; pu] ⟩.

    Let res := atksnip_sem sum_atk (s, 42). (* Can I not do copattern? *)

    Let cfg := fst res.
    Let leak := snd res.

    Let s_out := fst cfg.
    Let atk_mem := snd cfg.


    Goal s_out pu = (42 + 3 + 58). cbv. reflexivity. Qed.
    Goal s_out pt = s pt. cbv. reflexivity. Qed.
    Goal s_out st = s st. cbv. reflexivity. Qed. 
    Goal atk_mem = (42 + 1). cbv. reflexivity. Qed. 
    Goal leak = [42; 3; 58]. cbv. reflexivity. Qed.
  End sum.
End test.

(* I think that this notion of computation is a monad *)
Inductive Combined {amem : AtkMemParam} : Type := 
  | cmd (c : Cmd) 
  | atk (a: AtkSnip).

Coercion cmd : Cmd >-> Combined. (* uniform inheritance condition? TODO *)
Coercion atk : AtkSnip >-> Combined.
(* 
TODO: Can I make this work? with Cmd + AtkSnip?
Coercion inl : Cmd >-> Combined.
 *)

Section comb.
  Context {amem : AtkMemParam}.
  Variables (c : Combined) (cfg : CombState).

  Definition combined_sem : CombState * LeakVal :=
    match c with 
    | cmd c => 
        let (st, ast) := cfg in
        ((cmd_sem c st , ast), [])
    | atk a => atksnip_sem a cfg
    end.
End comb.


Section prog.
  Context {amem : AtkMemParam}.
  Definition AtkProg := list Combined.

  (* This is not structured correctly, I think *)
  Fixpoint prog_sem (p : AtkProg) : (CombState * LeakVal) -> (CombState * LeakVal) :=
    match p with
    | [] => fun x => x
    | c :: p' => fun x => 
        let (cst, lk) := x in
        let (cst', lk_extra) := prog_sem p' (combined_sem c cst) in
        (cst', lk ++ lk_extra)
    end.

  Section prog_behavior.
    Variables (p : AtkProg) (st_inp : Value). 

    Let inp_state := fun v => if var_eq_dec v st then st_inp else 0.
    Let inp_atk_state := init_val.
    Notation inp_cfg := ((inp_state, inp_atk_state), []). (* This does not type check otherwise. *)
    Let out := prog_sem p inp_cfg.
    Let out_cfg := fst out.
    Let out_lk := snd out.
    Let out_pt := ((fst out_cfg) pt).
    Let out_st := ((fst out_cfg) st).


  (* This init_val is kind of garbage *)
    Definition prog_behavior : (Value * Value * LeakVal)  (* ST x PT *) := 
      (out_st, out_pt, out_lk).

  End prog_behavior.
End prog.

Section test.
  Variable admit : forall {T}, T.
  Let s : State :=
    fun v => match v with
             | st => 67
             |pt => 3
             | pu => 58
             end.

  Let c := {| code :=  fun s => s st + s pt + s pu ; cmp_lbl := admit |} . (* TODO: I didn't like writing this at all *)

  (* TODO: Forcing this, and not being able to infer seems a little bit sad *)
  Check ((pu ← _) : Cmd) : Combined. (* How can I print Coercions? *)
(*
pu ← _ : Combined
     : Combined
*)
  Set Printing Coercions.
  Check (pu ← _) : Combined. 
(*
cmd (pu ← ?comp) : Combined
     : Combined
*)
  Unset Printing Coercions.
  Check (pu ← _) : Combined. 
(*
pu ← ?comp : Combined
     : Combined
*)

  Context {amem : AtkMemParam}.
  
  Let p : AtkProg. Proof.
    unshelve refine (
    [
     (pu ← c) : Combined;  (* TODO: Is it possible to not keep writing this nonsense *)
     (st ← c) : Combined; 
     (pt ← c) : Combined
    ]). 
    all:(abstract exact admit).
    Defined.


  Compute prog_behavior p 10.
End test.

(* Can I make this recursive? *)
Ltac dominate_example := abstract (repeat ( congruence || 
                                  discriminate ||  
                                  cbv; intros; match goal with [ H : _ = _ |- _ ] =>  rewrite H; clear H end)).
(* The next step will be to write an example *)
Module  IntEx.
  (* 
    I wish I could have syntax that is a little better. 
    TODO: Notation?
    TODO: Should I force programs to alternate? Let me not. 
  *)
  Section run_ex.
    Context {amem : AtkMemParam}.
    Definition real_atkprg : AtkProg. Proof. unshelve refine ([ (* TODO: Why do I have to do this unshelve? *) 
      (* Moreover, refine is a tactic that takes in incomplete gallina terms. Can I build a custom tactic that does that? *)

         ☠︎︎ ⟨fun _ _ _ => 10 | fun s _ _ => s | fun s _ _ => [4 ] ⟩
         :Combined; (* ☠︎︎ sets pu to 10 *)

         (pt ← {| code := fun _ => 10 ; cmp_lbl := pt |})
         :Combined; (* pt ← 10 *)

         ☠︎︎ ⟨fun _ pt pu => pt + pu | fun s _ _ => s | fun s _ _ => [5] ⟩
         :Combined; (* ☠︎︎ sets pu to 10 *)

         (pu ← {| code := fun s => s pt + 5 ; cmp_lbl := pt |})
         :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨ (fun _ pt pu => pu)  | fun s _ _ => s | fun s _ _ => [6] ⟩               
         :Combined; (* ☠︎︎ does nothing *)

         (pt ← {| code := fun s => s pu ; cmp_lbl := pu |})
         :Combined; (* pt ← pu  !!ENDORSE!! *) (* I don't like the fact that there is not endorse happening *)

         ☠︎︎ ⟨  (fun _ _ _ => 10)| fun s _ _ => s | fun s _ _ => [9] ⟩                  
         :Combined; (* Adversary sets pu to 10 *)

         (pt ← {| code := fun s => s pt + 1 ; cmp_lbl := pt |})
         :Combined  (* pt ← pt + 1 *)
      ]). 
      all:(dominate_example).
    Defined.
    (* TODO: Am I using my other  coercions? *)


    Compute prog_behavior real_atkprg. (* See how there is no dependent type nonsense here at all! *)
  (*
  = fun st_inp : Value => (st_inp, 16, [4; 5; 6; 9])
       : Value -> Value * Value * LeakVal
  *)

    Definition ideal_atkprg1 : AtkProg. Proof. unshelve refine( [
         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => [4; 5; 6; 9]⟩             
         :Combined; (* ☠︎︎ leaks everything first *)

         (pt ← {| code := fun _ => 10 ; cmp_lbl := pt |})
         :Combined; (* pt ← 10 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => []⟩                       
         :Combined; (* ☠︎︎ noop *)

         (pu ← {| code := fun s => s pt + 5 ; cmp_lbl := pt |})
         :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨fun _ _ pu => 15 | fun s _ _ => s | fun _ _ _ => []⟩                       
         :Combined; (* ☠︎︎ endorses 15, a value. There is no compute, or anything *)

         (pt ← {| code := fun s => s pu ; cmp_lbl := pu |})
         :Combined; (* pt ← pu  !!ENDORSE!! *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => []⟩                       
         :Combined; (* ☠︎︎ noop 10 *)

         (pt ← {| code := fun s => s pt + 1 ; cmp_lbl := pt |})
         :Combined  (* pt ← pt + 1 *)
         ]). 
         all:(dominate_example).
     Defined.
    Compute  prog_behavior ideal_atkprg1.

    (* This is what we want to do *)
    Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg1. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
    Proof.
      cbv. reflexivity.
    Qed.

    
    Definition my_nat : nat := 5.

    Definition my_prf : True := I. (* True is a type that has one element called I *)

    Definition ideal_atkprg2 : AtkProg. Proof. unshelve refine ([
         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => [4; 5; 6; 9]⟩             
             :Combined; (* ☠︎︎ leaks everything first *)

         (pt ← {| code := fun _ => 10 ; cmp_lbl := pt |})
         :Combined; (* pt ← 10 *)

         (pu ← {| code := fun s => s pt + 5 ; cmp_lbl := pt |})
         :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨fun _ _ pu => 15 | fun s _ _ => s | fun _ _ _ => []⟩                       
             :Combined; (* ☠︎︎ endorses 15, a value. There is no compute, or anything *)

         (pt ← {| code := fun s => s pu ; cmp_lbl := pu |})
         :Combined; (* pt ← pu  !!ENDORSE!! *) (* I would prefer if the endorses were marked *)

         (pt ← {| code := fun s => s pt + 1 ; cmp_lbl := pt |})
         :Combined  (* pt ← pt + 1 *)

         ]); abstract (congruence || discriminate).
     Defined.

    Compute  prog_behavior ideal_atkprg2.
  (*
  = fun st_inp : Value => (st_inp, 16, [4; 5; 6; 9])
       : Value -> Value * Value * LeakVal
  *)

    Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg2. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
    Proof.
      cbv. reflexivity.
    Qed.

    Definition ideal_atkprg3 : AtkProg. Proof. unshelve refine ([

         (pt ← {| code := fun _ => 10 ; cmp_lbl := pt |})
         :Combined; (* pt ← 10 *)

         (pu ← {| code := fun s => s pt + 5 ; cmp_lbl := pt |})
         :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨fun _ _ pu => 15 | fun s _ _ => s | fun _ _ _ => []⟩                       
             :Combined; (* ☠︎︎ endorses 15, a value. There is no compute, or anything *)

         (pt ← {| code := fun s => s pu ; cmp_lbl := pu |})
         :Combined; (* pt ← pu  !!ENDORSE!! *) (* I would prefer if the endorses were marked *)

         (pt ← {| code := fun s => s pt + 1 ; cmp_lbl := pt |})
         :Combined;  (* pt ← pt + 1 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => [4; 5; 6; 9]⟩             
             :Combined (* ☠︎︎ leaks everything at the end *)

         ]); abstract (congruence || discriminate).
     Defined.

    Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg3. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
    Proof.
      cbv. reflexivity.
    Qed.
  End run_ex.
End IntEx.

Module NIex. Section ctx.
    Let amem : AtkMemParam := {| AtkState := unit ; init_val := tt |}.  Existing Instance amem.
    Definition real_atkprg : AtkProg. Proof. unshelve refine ([
       ☠︎︎ ⟨fun s pt pu => 10 | fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩
       :Combined;  

       (pt ← {| code := fun _ => 10 ; cmp_lbl := pt |})
       :Combined; 

       ☠︎︎ ⟨fun s pt pu => pt + 5 + pu| fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩
       :Combined;

       (st ← {| code := fun s => (s st + s pt) * 29 ; cmp_lbl := st |})
       :Combined;

       ☠︎︎ ⟨fun s pt pu => pt + 5 + pu| fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩
       :Combined;

       (pu ← {|  code := fun s => s pu * s pt ;  cmp_lbl := pu |})
       :Combined; 

       ☠︎︎ ⟨fun s pt pu => pt + 5 + pu| fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩   
       :Combined
      ]); abstract (congruence || discriminate). 
    Defined.

    Print real_atkprg.
    Eval compute in prog_behavior real_atkprg.

    (* TODO: I would like to have a way to not*)
    Definition ideal_atkprg : AtkProg. Proof. unshelve refine ( [

         (pt ← {| code := fun _ => 10 ; cmp_lbl := pt |})
         :Combined; 

         (st ← {| code := fun s => (s st + s pt) * 29 ; cmp_lbl := st |})
         :Combined;

         (pu ← {|  code := fun s => s pu * s pt ;  cmp_lbl := pu |})
         :Combined; (* pt ← 10 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ _ _ => [0; 0; 10; 10; 10; 25; 10; 400] ⟩             
             :Combined
      ]); abstract ( congruence || discriminate).
   Defined.

     (* Notice how the ideal attacker just comes in at the end to leak the values.
        If we defined equivalence where pu values also matter, 
        then we should let the ideal attacker set those also, which compilcates the ideal world a little bit

     *)
    Eval compute in prog_behavior ideal_atkprg.
    Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
    Proof.
      cbv. reflexivity.
    Qed.

End ctx. End NIex.

Set Printing Implicit.
Check NIex.real_atkprg.
Unset Printing Implicit.

(* TODO: An example with declassification *)
Module Declass. 
  Section real. (* Can I use the same section for real and ideal? *)
    Let amem : AtkMemParam := {| AtkState := unit ; init_val := tt |}.  Existing Instance amem.

    Definition real_atkprg : AtkProg. Proof. unshelve refine ([
         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (st ← {| code := fun s => if s st then 0 else 1 ; cmp_lbl := st |})
           :Combined;  (* check if st is 0 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (pt ← {| code := fun s => s st ; cmp_lbl := st |})
           :Combined;  (* DECLASSIFICATION!! *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (pt ← {| code := fun s => 0 ; cmp_lbl := pt |})
           :Combined;  (* Some other random code *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (st ← {| code := fun s => 1 - s st ; cmp_lbl := st |})
           :Combined ; (* Some other random code *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined 
      ]). 
      all:(dominate_example).
   Defined.

  End real.
  Eval compute in prog_behavior real_atkprg.

  Section ideal. (* Can I use the same section for real and ideal? *)
    Let amem : AtkMemParam := {| AtkState := nat ; init_val := 0 |}.  Existing Instance amem.

    Definition ideal_atkprg : AtkProg. Proof. unshelve refine ([
         (st ← {| code := fun s => if s st then 0 else 1 ; cmp_lbl := st |})
           :Combined;  (* check if st is 0 *)

         (pt ← {| code := fun s => s st ; cmp_lbl := st |})
           :Combined;  (* DECLASSIFICATION!! *)

         (* Note how these we have attacker right after the declassification point, and reads the declassified value *)
         (* Unfortunately, the present model is not good enough to force this. This is a 'trust me bro'*)
         ☠︎︎ ⟨fun _ _ pu => pu | fun _ pt _ => pt | fun _ pt pu => [] ⟩ 
             :Combined ;

         (pt ← {| code := fun s => 0 ; cmp_lbl := pt |})
           :Combined;  (* Some other random code *)

         (st ← {| code := fun s => 1 - s st ; cmp_lbl := st |})
           :Combined ; (* Some other random code *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun s _ _ => [0 ; 0 ; 0; 0; s ; 0 ; 0 ; 0 ;0 ;0] ⟩ (*TODO: Why can't I use  if s ... here?  *)
             :Combined 
      ]). 
      all:(dominate_example).
     Defined.

  End ideal.
  Goal prog_behavior ideal_atkprg = prog_behavior real_atkprg. Proof.
    simpl.
    reflexivity.
  Qed.
End Declass.

Module Both.

  Section real.
    Let amem : AtkMemParam := {| AtkState := unit ; init_val := tt |}.  Existing Instance amem.

    Definition real_atkprg : AtkProg. Proof. unshelve refine ([
         ☠︎︎ ⟨fun _ _ _ => 1 | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ; (* Attacker sets pu to 1*)

         (pt ← {| code := fun s => s pu ; cmp_lbl := pu |}) 
           :Combined;  (* ENDORSEMENT! *)

         ☠︎︎ ⟨fun _ pt pu =>  pu + pt | fun _ _ _ => tt | fun _ _ _ => [3 ; 1] ⟩             
             :Combined ; (* Attacker does random crap *)

         (pt ← {| code := fun s => s pt * s st ; cmp_lbl := st |}) (* Reverse this later *)
           :Combined ; (* DECLASSIFICATION! *)

         ☠︎︎ ⟨fun _ _ _ => 1 | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined  (* Attacker does random crap *)
      ]); dominate_example.
    Defined.

  End real.
  Compute prog_behavior real_atkprg.

  Section ideal.
    Let amem : AtkMemParam := {| AtkState := nat ; init_val := 0 |}.  Existing Instance amem.

    Definition ideal_atkprg : AtkProg. Proof. unshelve refine ([
         ☠︎︎ ⟨fun _ _ _ => 1 | fun s _ _ => s | fun _ _ _ => [] ⟩
             :Combined ; (* Setting the endorsement *)
 
         (pt ← {| code := fun s => s pu ; cmp_lbl := pu |}) 
           :Combined;  (* ENDORSEMENT! *)


         (pt ← {| code := fun s => s pt * s st ; cmp_lbl := st |}) (* Reverse this later *)
           :Combined ; (* DECLASSIFICATION! *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ pt _ => pt | fun _ _ _ => [] ⟩
           :Combined ; (* Learning the declassification *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun s _ _ => [0 ; 0 ; 3; 1 ; s ; 2] ⟩
           :Combined  (* Simulating the real learnt information *)
      ]);  dominate_example.
           Defined.
  End ideal.

  Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg.
  Proof.
    cbv.
    reflexivity.
  Qed.

End Both.

(* The proof compiler *)
(* This takes in an input which is an attacked program, and returns an attacked program as well *)

Section proof_compiler.
  (* I don't care about things for now *)
  Let amem : AtkMemParam := {| AtkState := unit ; init_val := tt |}.  Existing Instance amem.

  (* This should really go somewhere else *)
  Ltac name_gl name := refine ?[name]. (* for convenience *)

  #[local] Set Printing Goal Names. (* Test Printing Goal Names at the end of section will return false *)

  Definition cmd_simulate (c : Cmd) (old_pt : Value) (old_pu : Value) : Value(* new_pt*) * Value (* new_pu) *). Proof.
     destruct c as [cmd ?]. (* Don't use _ instead of ? *)
     destruct (cmd_kind cmd); [name_gl NI | name_gl END | name_gl DECL | name_gl ILL]. 

    [ILL]: { abstract contradiction. } (* We don't care about these *)

    (* TODO: Is there a way I can select multiple goals? Something like [NI], [END]*)
    [END]: { exact (123, 59). } (* This is a temp fix*)

    [DECL]: { exact (69, 30). } (* This is a temp fix*)

    [NI]: {
      (* you can also use as *) (* I use compute_data coercion here *)
       pose (code := code (comp cmd)). 

       (* 
         The interface the program gives you is a function.
         Unfortunately, This means that you'll have to construct a state with some useless values
         We could also syntactically force functions to look a certain way
         Then things could be pairs, where there will be an 'effective function'.
         I'm not entirely sure what the right way to proceed is
       *)
       pose (dummy_newst := (fun var =>  match var with pu => old_pu | pt => old_pu | st => 69 end) : State). 

       destruct (dest cmd); [name_gl ST | name_gl PT | name_gl PU].

       [ST]: {  exact (old_pt,old_pu). } (* If the assignment is to ST *)
       [PT]: {  
         pose (new_pt := code dummy_newst).
         exact (new_pt, old_pu).
        }
       [PU]: { 
        (* I wonder if I could incrementally build this using an evar *)
        (* 
         assert State as new_state; [destruct 1; [name_gl ST | name_gl PT | name_gl PU] |].
        I just get new_state : State. This seems okay, but there seems to me an Implicit generalization
         *)
          
        pose (new_pu := code dummy_newst).
        exact (old_pt, new_pu).
      }
    }
  Defined.

  Definition atksnip_sim (atk : AtkSnip) (existing_pt : Value) (existing_pu : Value) : 
            (Value (* pu *) *  LeakVal). Proof.
     destruct atk as [pu_trans _ leak].
     pose (new_pu := pu_trans tt existing_pt existing_pu). (* TODO: tt is stupid *)
     pose (leaked := leak tt existing_pt existing_pu). 
     exact (new_pu, leaked).
    Defined.

  Record Accumulator : Type := { partial_prog : AtkProg ; pt_sim : Value; pu_sim : Value ; partial_leak : LeakVal }. (* TODO Let or definition? *)
  (* I think that these sims should eventually be Value -> Value, because they might depend on runtime secrets *) 
  (* 'Last declassified secret' should probably be what the memory should be*)

  Fixpoint proof_compiler_loop (inp_ap : AtkProg): Accumulator -> Accumulator. Proof.
    destruct inp_ap as [| cmdatk inp_ap']; [name_gl EMPTY | name_gl NONEMPTY].

    [EMPTY]: {  exact (fun x => x). } (* Just return the accumulator *)

    [NONEMPTY]: { 
       intros [partial_prog pt_sim_old pu_sim_old partial_leak]. (* How do I use assertions? *)
       unshelve evar (final_state : Accumulator); [| exact (proof_compiler_loop inp_ap' final_state)]. 

       destruct cmdatk as [cmd | atk]; [name_gl CMD | name_gl ATK].

       [CMD]: {
         destruct (cmd_simulate cmd pt_sim_old pu_sim_old) as [pt_sim_new pu_sim_new].
         repeat split; [ name_gl PROG | name_gl PT | name_gl PU | name_gl LEAK].

         [PROG]: { exact (partial_prog ++ [ cmd : Combined ]). } (* Trusted code gets compiled as such *)
         [LEAK]: { exact (partial_leak). } (* No need to simulate any leaks when you have this *)
         [PT]: { exact (pt_sim_new). } (* No need to simulate any leaks when you have this *)
         [PU]: { exact (pu_sim_new). }
        }

       [ATK]: {
         destruct (atksnip_sim atk pt_sim_old pu_sim_old) as [pu_sim_new extra_leak].
         pose (partial_leak_new := partial_leak ++ extra_leak).

         repeat split; [name_gl PROG | name_gl PT | name_gl PU | name_gl LEAK].

         [PROG]: { exact partial_prog. } (* The attack gets erased. However, when we start thinking about downgrades, this should not be the case *)
         [LEAK]: { exact partial_leak_new.  }
         [PU]: { exact pu_sim_new.  }
         [PT]: { exact pt_sim_old. }
        }
     }
    Guarded.
  Defined.

  Definition proof_compiler (inp_ap : AtkProg) : AtkProg. Proof.
    (* TODO: Are pt, pu_sim actually set to 0? *)
    pose (initial_acc := {| partial_prog := []; pt_sim := 0 ; pu_sim := 0; partial_leak := []|}).
    destruct (proof_compiler_loop inp_ap initial_acc) as [prefinal_prog  _  _ final_leak].
    pose (final_snip := (☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ _ _ => final_leak ⟩): Combined).
    exact (prefinal_prog ++ [final_snip]).
  Defined.

  Print NIex.real_atkprg.
  Goal False.
  pose (proof_compiler NIex.real_atkprg). (* So, there is an error *)
  red in a.
  clear a.
  pose (proof_compiler_loop NIex.real_atkprg). (* So, there is an error *)
  simpl in a.
  Abort.

  (* 
          (((partial_leak ++ [0; pu_sim]) ++ [0; 10]) ++ [0; 15]) ++
          [0; 1340]
 *)

  Compute prog_behavior (NIex.real_atkprg). (* So, there is an error *)
(*
      [0; 0; 10; 10; 10; 25; 10; 400])
*)
  Compute prog_behavior (proof_compiler NIex.real_atkprg). (* So, there is an error *)
(*
      [0; 0; 0; 10; 0; 15; 0; 1340])
*)
End proof_compiler.


(* TODO: Check NI examples. Then see if I can prove that  *)




  Goal forall p, prog_behavior p = prog_behavior (proof_compiler p). Proof.
    reflexivity. 
  Qed.



(*  

There are so many directions it looks like I can take.
- I can make the attackers do exactly one thing. Then, to simulate simulataneous model, we do one by one
- I could do this in both the real and ideal situations
*)
