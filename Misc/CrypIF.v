(* Here, the point is to show how the crypto view and the information flow view are equal, if you have nmif 
Let us start with a very simple program. Then we try to see how
*)

From Stdlib Require Import List.
From Stdlib Require Import Logic.FunctionalExtensionality.

Inductive Vars := st | pt | pu.
Definition var_eq_dec : forall (v v' : Vars), {v = v'} + {v <> v'}. Proof. decide equality. Defined.

Definition Value := nat.
Definition State :=  Vars -> Value.


(* TODO: Define the prediates *)
Definition Compute := State -> Value.

(* TODO: Just define confidentiality equivalence for now.. *)

Record Cmd := {dest : Vars; comp : Compute}.
Notation "v ← c" := {| dest := v ; comp := c |} (at level 20).

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

Class AtkMemParam := { AtkState : Type ; init_val : AtkState }.

Record AtkSnip {amem : AtkMemParam} := {
  pu_trans : AtkState  -> Value (* pt *) -> Value (* pu *) -> Value (* pu *)  ;
  mem_trans : AtkState -> Value (* pt *) -> Value (* pu *) -> AtkState 
}.

Notation "☠︎︎ ⟨ pu | mem ⟩" := {|pu_trans := pu ; mem_trans := mem |}.

Section atksnip_sem.
  Context {amem : AtkMemParam}.
  Definition CombState : Type := State * AtkState.
  Variables (a: AtkSnip) (cfg : CombState).


  Definition atksnip_sem : CombState :=
    let (s, s_atk) := cfg in
    let pu_v := pu_trans a s_atk (s pt) (s pu) in
    let s_atk' := mem_trans a s_atk (s pt) (s pu) in
    let s' := fun v => 
                if var_eq_dec v pu then (* You could probably refactor this.. *)
                  pu_v
                else
                  s v in
    (s', s_atk').

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
    Let zero_atk : AtkSnip := ☠︎︎ ⟨ fun _ _ _ => 0 | fun x _ _ => x⟩.

    
    Let res := atksnip_sem zero_atk s tt. (* Can I not do copattern? *)
    Let s' := fst res.
    Let atk' := snd res.
    Goal s' pu = 0. cbv. reflexivity. Qed.
    Goal s' pt = s pt. cbv. reflexivity. Qed.
    Goal s' st = s st. cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
    Goal atk' = tt. cbv. reflexivity. Qed. 
  End zero.

  Section sum.
    Let amem : AtkMemParam := {| AtkState := nat ; init_val := 67 |}.  Existing Instance amem.
    Let sum_atk : AtkSnip := ☠︎︎ ⟨ fun m x y => m + x + y | fun x _ _ => x + 1⟩.

    Let res := atksnip_sem sum_atk s 42. (* Can I not do copattern? *)
    Let s' := fst res. Let atk' := snd res.

    Goal s' pu = (42 + 3 + 58). cbv. reflexivity. Qed.
    Goal s' pt = s pt. cbv. reflexivity. Qed.
    Goal s' st = s st. cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
    Goal atk' = (42 + 1). cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
  End sum.
End test.

Inductive Combined {amem : AtkMemParam} : Type := 
  | cmd (c : Cmd) 
  | atk (a: AtkSnip).

Coercion cmd : Cmd >-> Combined.
Coercion atk : AtkSnip >-> Combined.
(* 
TODO: Can I make this work? with Cmd + AtkSnip?
Coercion inl : Cmd >-> Combined.
 *)


Section comb.
  Context {amem : AtkMemParam}.
  Variables (c : Combined) (cfg : CombState).

  Check (
    let (st, ast) := cfg in
      match c with 
        | cmd c => (st , ast)
        | atk a => (st , ast)
        end) : CombState.


  Definition combined_sem : CombState.
Proof. (* I wonder how things might look if I used case instead TODO *)
  destruct c.
  - refine (cmd_sem _ _ _).
  - exact (atksnip_sem a s).
Defined.
  

Definition AtkProg := list Combined.
Import ListNotations.

(* I wonder if I could do (s : State) *)
Fixpoint prog_sem (p : AtkProg) : State -> State :=
  match p with
  | [] => 
      fun inp_state => inp_state
  | c :: p' => 
      fun inp_state => 
        prog_sem p' (combined_sem c inp_state)
  end.


Definition prog_behavior (p : AtkProg) (st_inp : Value) : (Value * Value)  (* ST x PT *) :=
  let inp_state := fun v => if var_eq_dec v st then st_inp else 0 in 
  let end_state := prog_sem p inp_state in
  (end_state st, end_state pt).


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

  Let p : AtkProg := 
    [
     (pu ← c) : Combined;  (* TODO: Is it possible to not keep writing this nonsense *)
     (st ← c) : Combined; 
     (pt ← c) : Combined
    ].

  Let s' := prog_sem p s.
  Compute s' pu.
  Compute s' pt.
  Compute s' st.

  Compute prog_behavior p 10.
End test.

(* The next step will be to write an example *)

(* 
  I wish I could have syntax that is a little better. 
  TODO: Notation?
  TODO: Should I force programs to alternate? Let me not. 
*)
Definition running_example : AtkProg := [
     ☠︎︎ ⟨fun _ _ => 10  ⟩        :Combined; (* ☠︎︎ sets pu to 10 *)
     (pt ← fun _ => 10)         :Combined; (* pt ← 10 *)
     ☠︎︎ ⟨fun pt pu => pt + pu  ⟩ :Combined; (* ☠︎︎ sets pu to 10 *)
     (pu ← fun s => s pt + 5)   :Combined; (* pu ← pt + 5 *)
     ☠︎︎ ⟨ (fun _ pu => pu)  ⟩    :Combined; (* ☠︎︎ does nothing *)
     (pt ← (fun s => s pu))     :Combined; (* pt ← pu  !!ENDORSE!! *)
     ☠︎︎ ⟨  (fun _ _ => 10)⟩      :Combined; (* Adversary sets pu to 10 *)
     (pt ← (fun s => s pt + 1)) :Combined  (* pt ← pt + 1 *)
  ].

Set Printing Coercions.
Print running_example.
Unset Printing Coercions.

Definition sim : AtkProg := [
     ☠︎︎⟨ (fun _ pu => pu) ⟩       :Combined; (* ☠︎︎ noop *)
     (pt ← fun _ => 10)          :Combined; (* pt ← 10 *)
     ☠︎︎⟨(fun _ pu => pu) ⟩        :Combined; (* ☠︎︎ noop *)
     (pu ← fun s => s pt + 5)    :Combined; (* pu ← pt + 5 *)
     ☠︎︎⟨(fun _ _ => 15) ⟩         :Combined; (* ☠︎︎ ENDORSE plan value *)
     (pt ← (fun s => s pu))      :Combined; (* pt ← pu  !!ENDORSE!! *)
     ☠︎︎⟨(fun _ pu => pu) ⟩        :Combined; (* ☠︎︎ noop *)
     (pt ← (fun s => s pt + 1))  :Combined  (* pt ← pt + 1 *)
  ].

Definition beh_real := prog_behavior running_example.
Definition beh_ideal := prog_behavior sim.

(* This is what we want to do *)
Goal beh_real = beh_ideal. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
Proof.
  reflexivity.
Qed.
