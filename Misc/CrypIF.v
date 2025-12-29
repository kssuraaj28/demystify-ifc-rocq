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


Record ComputeData := { code : State -> Value ; cmp_lbl : Vars }. 
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
Definition Compute := {x : ComputeData | WellFormedCompute x}. 


Record Cmd := {dest : Vars; comp : Compute}.
Notation "v ← c" := {| dest := v ; comp := c |} (at level 20).

Inductive CmdKind := ni | endorse | declassify.

Definition cmd_kind (cmd : Cmd) : CmdKind :=
  let dest_lvl := dest cmd in
  let src_lvl := cmp_lbl (proj1_sig (comp cmd)) in
  match dest_lvl, src_lvl with 
  | _, _ => ni
  end.

  let (dest, compute) := c in 
  let (compute, _) := compute in  (* I wish I could do this copattern thing *)
  ni.


Definition cmd_sem (c: Cmd) (s: State) : State := 
  fun var => 
    let (dest, comp) := c in (* TODO: What did I just do? *)
    let new_val := comp s in 
    let old_val := s var in 
    if var_eq_dec var dest then 
      new_val
    else
      old_val.

Section test.
  Let s : State :=
    fun v => match v with
             | st => 67
             | pt => 3
             | pu => 58
             end.

  Let c : Compute :=
    fun s => s st + s pt + s pu.


  Let s' := cmd_sem (pu ← c) s. 
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
  Let s : State :=
    fun v => match v with
             | st => 67
             |pt => 3
             | pu => 58
             end.

  Let c : Compute :=
    fun s => s st + s pt + s pu.

  (* TODO: Forcing this, and not being able to infer seems a little bit sad *)
  Check (pu ← _) : Combined. (* How can I print Coercions? *)
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
  
  Let p : AtkProg := 
    [
     (pu ← c) : Combined;  (* TODO: Is it possible to not keep writing this nonsense *)
     (st ← c) : Combined; 
     (pt ← c) : Combined
    ].

  Compute prog_behavior p 10.
End test.

(* The next step will be to write an example *)
Module  IntEx.
  (* 
    I wish I could have syntax that is a little better. 
    TODO: Notation?
    TODO: Should I force programs to alternate? Let me not. 
  *)
  Section run_ex.
    Context {amem : AtkMemParam}.
    Definition real_atkprg : AtkProg := [
         ☠︎︎ ⟨fun _ _ _ => 10 | fun s _ _ => s | fun s _ _ => [4 ] ⟩                    :Combined; (* ☠︎︎ sets pu to 10 *)

         (pt ← fun _ => 10)                                                           :Combined; (* pt ← 10 *)

         ☠︎︎ ⟨fun _ pt pu => pt + pu | fun s _ _ => s | fun s _ _ => [5] ⟩              :Combined; (* ☠︎︎ sets pu to 10 *)

         (pu ← fun s => s pt + 5)                                                     :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨ (fun _ pt pu => pu)  | fun s _ _ => s | fun s _ _ => [6] ⟩               :Combined; (* ☠︎︎ does nothing *)

         (pt ← (fun s => s pu))                                                       :Combined; (* pt ← pu  !!ENDORSE!! *)

         ☠︎︎ ⟨  (fun _ _ _ => 10)| fun s _ _ => s | fun s _ _ => [9] ⟩                  :Combined; (* Adversary sets pu to 10 *)

         (pt ← (fun s => s pt + 1))                                                   :Combined  (* pt ← pt + 1 *)
      ].

    Compute prog_behavior real_atkprg.
  (*
  = fun st_inp : Value => (st_inp, 16, [4; 5; 6; 9])
       : Value -> Value * Value * LeakVal
  *)

    Definition ideal_atkprg1 : AtkProg := [
         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => [4; 5; 6; 9]⟩             :Combined; (* ☠︎︎ leaks everything first *)

         (pt ← fun _ => 10)                                                            :Combined; (* pt ← 10 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => []⟩                       :Combined; (* ☠︎︎ noop *)

         (pu ← fun s => s pt + 5)                                                      :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨fun _ _ pu => 15 | fun s _ _ => s | fun _ _ _ => []⟩                       :Combined; (* ☠︎︎ endorses 15, a value. There is no compute, or anything *)

         (pt ← (fun s => s pu))                                                        :Combined; (* pt ← pu  !!ENDORSE!! *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => []⟩                       :Combined; (* ☠︎︎ noop 10 *)

         (pt ← (fun s => s pt + 1))                                                    :Combined  (* pt ← pt + 1 *)
         ].
    Compute  prog_behavior ideal_atkprg1.

    (* This is what we want to do *)
    Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg1. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
    Proof.
      cbv. reflexivity.
    Qed.

    Definition ideal_atkprg2 : AtkProg := [
         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => [4; 5; 6; 9]⟩             :Combined; (* ☠︎︎ leaks everything first *)

         (pt ← fun _ => 10)                                                            :Combined; (* pt ← 10 *)
         (pu ← fun s => s pt + 5)                                                      :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨fun _ _ pu => 15 | fun s _ _ => s | fun _ _ _ => []⟩                       :Combined; (* ☠︎︎ endorses 15, a value. There is no compute, or anything *)

         (pt ← (fun s => s pu))                                                        :Combined; (* pt ← pu  !!ENDORSE!! *)
         (pt ← (fun s => s pt + 1))                                                    :Combined  (* pt ← pt + 1 *)
         ].

    Compute  prog_behavior ideal_atkprg2.
  (*
  = fun st_inp : Value => (st_inp, 16, [4; 5; 6; 9])
       : Value -> Value * Value * LeakVal
  *)

    Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg2. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
    Proof.
      cbv. reflexivity.
    Qed.


    Definition ideal_atkprg3 : AtkProg := [

         (pt ← fun _ => 10)                                                            :Combined; (* pt ← 10 *)
         (pu ← fun s => s pt + 5)                                                      :Combined; (* pu ← pt + 5 *)

         ☠︎︎ ⟨fun _ _ pu => 15 | fun s _ _ => s | fun _ _ _ => []⟩                       :Combined; (* ☠︎︎ endorses 15, a value. There is no compute, or anything *)

         (pt ← (fun s => s pu))                                                        :Combined; (* pt ← pu  !!ENDORSE!! *)
         (pt ← (fun s => s pt + 1))                                                    :Combined; (* pt ← pt + 1 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun _ _ _ => [4; 5; 6; 9]⟩             :Combined  (* ☠︎︎ leaks everything last  *)
         ].

    Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg3. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
    Proof.
      cbv. reflexivity.
    Qed.
End run_ex.
End IntEx.

Module NIex. Section ctx.
    Let amem : AtkMemParam := {| AtkState := unit ; init_val := tt |}.  Existing Instance amem.
    Definition real_atkprg : AtkProg := [

        ☠︎︎ ⟨fun s pt pu => 10 | fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩            :Combined;  

         (pt ← fun _ => 10)                                                            :Combined; 

         ☠︎︎ ⟨fun s pt pu => pt + 5 + pu| fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩   :Combined;

         (st ← fun s => (s st + s pt) * 29)                                            :Combined;

         ☠︎︎ ⟨fun s pt pu => pt + 5 + pu| fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩   :Combined;

         (pu ← fun s => s pu * s pt)                                                   :Combined; (* pt ← 10 *)

         ☠︎︎ ⟨fun s pt pu => pt + 5 + pu| fun _ _ _ => tt | fun s pt pu => [pt ; pu] ⟩   :Combined
      ].

    Eval compute in prog_behavior real_atkprg.

    (* TODO: I would like to have a way to not*)
    Definition ideal_atkprg : AtkProg := [

         (pt ← fun _ => 10)                                                                                 :Combined; 

         (st ← fun s => (s st + s pt) * 29)                                                                 :Combined;

         (pu ← fun s => s pu * s pt)                                                                        :Combined; (* pt ← 10 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ _ _ => [0; 0; 10; 10; 10; 25; 10; 400] ⟩             :Combined
      ].

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

    Definition real_atkprg : AtkProg := [
         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (st ← fun s => if s st then 0 else 1)
           :Combined;  (* check if st is 0 *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (pt ← fun s => s st )
           :Combined;  (* DECLASSIFICATION!! *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (pt ← fun s => 0)
           :Combined;  (* Some other random code *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ;

         (st ← fun s => 1 - s st)
           :Combined ; (* Some other random code *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined 
      ].
  End real.
  Eval compute in prog_behavior real_atkprg.

  Section ideal. (* Can I use the same section for real and ideal? *)
    Let amem : AtkMemParam := {| AtkState := nat ; init_val := 0 |}.  Existing Instance amem.

    Definition ideal_atkprg : AtkProg := [
         (st ← fun s => if s st then 0 else 1)
           :Combined;  (* check if st is 0 *)

         (pt ← fun s => s st )
           :Combined;  (* DECLASSIFICATION!! *)

         (* Note how these we have attacker right after the declassification point, and reads the declassified value *)
         (* Unfortunately, the present model is not good enough to force this. This is a 'trust me bro'*)
         ☠︎︎ ⟨fun _ _ pu => pu | fun _ pt _ => pt | fun _ pt pu => [] ⟩ 
             :Combined ;

         (pt ← fun s => 0)
           :Combined;  (* Some other random code *)

         (st ← fun s => 1 - s st)
           :Combined ; (* Some other random code *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun s _ _ => [0 ; 0 ; 0; 0; s ; 0 ; 0 ; 0 ;0 ;0] ⟩ (*TODO: Why can't I use  if s ... here?  *)
             :Combined 
      ].
  End ideal.
  Goal prog_behavior ideal_atkprg = prog_behavior real_atkprg. Proof.
    simpl.
    reflexivity.
  Qed.
End Declass.

Module Both.

  Section real.
    Let amem : AtkMemParam := {| AtkState := unit ; init_val := tt |}.  Existing Instance amem.

    Definition real_atkprg : AtkProg := [
         ☠︎︎ ⟨fun _ _ _ => 1 | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined ; (* Attacker sets pu to 1*)

         (pt ← fun s => s pu) 
           :Combined;  (* ENDORSEMENT! *)

         ☠︎︎ ⟨fun _ pt pu =>  pu + pt | fun _ _ _ => tt | fun _ _ _ => [3 ; 1] ⟩             
             :Combined ; (* Attacker does random crap *)

         (pt ← fun s => s pt * s st ) (* Reverse this later *)
           :Combined ; (* DECLASSIFICATION! *)

         ☠︎︎ ⟨fun _ _ _ => 1 | fun _ _ _ => tt | fun _ pt pu => [pt ; pu] ⟩             
             :Combined  (* Attacker does random crap *)
      ].
  End real.
  Compute prog_behavior real_atkprg.

  Section ideal.
    Let amem : AtkMemParam := {| AtkState := nat ; init_val := 0 |}.  Existing Instance amem.

    Definition ideal_atkprg : AtkProg := [
         ☠︎︎ ⟨fun _ _ _ => 1 | fun s _ _ => s | fun _ _ _ => [] ⟩
             :Combined ; (* Setting the endorsement *)
 
         (pt ← fun s => s pu) 
           :Combined;  (* ENDORSEMENT! *)

         (pt ← fun s => s pt * s st ) (* Reverse this later *)
           :Combined ; (* DECLASSIFICATION! *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun _ pt _ => pt | fun _ _ _ => [] ⟩
           :Combined ; (* Learning the declassification *)

         ☠︎︎ ⟨fun _ _ pu => pu | fun s _ _ => s | fun s _ _ => [0 ; 0 ; 3; 1 ; s ; 2] ⟩
           :Combined  (* Simulating the real learnt information *)
      ].
  End ideal.

  Goal prog_behavior real_atkprg = prog_behavior ideal_atkprg.
  Proof.
    cbv.
    reflexivity.
  Qed.

End Both.

(* Now, what should my proof compiler target be? 

There are so many directions it looks like I can take.
- I can make the attackers do exactly one thing. Then, to simulate simulataneous model, we do one by one
- I could do this in both the real and ideal situations
- In order to give the proof compiler, I have to think about writing down declassify and endorse.
  Can I write the compiler assuming this? (I feel like I might have to pass in 0 or something somewhere...) 

*)
