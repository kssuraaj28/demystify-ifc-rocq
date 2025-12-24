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

Record AtkSnip (*(AtkMem : Type)*) := {
  pu_trans : Value -> Value -> Value (*  *)
  }.

Notation "☠︎︎ ⟨ f ⟩" := {|pu_trans := f|}.


Section atksnip_sem.
  Variables (a: AtkSnip) (s : State).

  Definition atksnip_sem : State:=
    let pu_v := pu_trans a (s pt) (s pu) in
    fun v => 
      if var_eq_dec v pu then (* You could probably refactor this.. *)
        pu_v
      else
        s v.
End atksnip_sem.


Section test.
  Let s : State :=
    fun v => match v with
             | st => 67
             | pt => 3
             | pu => 58
             end.

  Section zero.
    Let zero_atk : AtkSnip := ☠︎︎ ⟨ fun _ _ => 0⟩.

    Let s' := atksnip_sem zero_atk s.
    Goal s' pu = 0. cbv. reflexivity. Qed.
    Goal s' pt = s pt. cbv. reflexivity. Qed.
    Goal s' st = s st. cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
  End zero.

  Section sum.
    Let sum_atk : AtkSnip := ☠︎︎ ⟨ fun x y => x + y ⟩.

    Let s' := atksnip_sem sum_atk s.
    Goal s' pu = s pt + s pu. cbv. reflexivity. Qed.
    Goal s' pt = s pt. cbv. reflexivity. Qed.
    Goal s' st = s st. cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
  End sum.
End test.

Inductive Combined : Type := 
  | cmd (c : Cmd) 
  | atk (a: AtkSnip).

Coercion cmd : Cmd >-> Combined.
Coercion atk : AtkSnip >-> Combined.
(* 
TODO: Can I make this work? with Cmd + AtkSnip?
Coercion inl : Cmd >-> Combined.
 *)


Definition combined_sem (c : Combined) (s : State) : State. Proof. (* I wonder how things might look if I used case instead TODO *)
  destruct c.
  - exact (cmd_sem c s).
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
     ☠︎︎ ⟨fun _ _ => 10  ⟩        : Combined; (* ☠︎︎ sets pu to 10 *)
     (pt ← fun _ => 10)         : Combined; (* pt ← 10 *)
     ☠︎︎ ⟨fun pt pu => pt + pu  ⟩ : Combined; (* ☠︎︎ sets pu to 10 *)
     (pu ← fun s => s pt + 5)   : Combined; (* pu ← pt + 5 *)
     ☠︎︎ ⟨ (fun _ pu => pu)  ⟩    : Combined; (* ☠︎︎ does nothing *)
     (pt ← (fun s => s pu))     : Combined; (* pt ← pu  !!ENDORSE!! *)
     ☠︎︎ ⟨  (fun _ _ => 10)⟩      : Combined; (* Adversary sets pu to 10 *)
     (pt ← (fun s => s pt + 1)) : Combined  (* pt ← pt + 1 *)
  ].

Definition sim : AtkProg := [
     ☠︎︎⟨ (fun _ pu => pu) ⟩       :Combined ;  (* ☠︎︎ noop *)
     (pt ← fun _ => 10)          :Combined ;  (* pt ← 10 *)
     ☠︎︎⟨(fun _ pu => pu) ⟩        :Combined ;  (* ☠︎︎ noop *)
     (pu ← fun s => s pt + 5)    :Combined ;  (* pu ← pt + 5 *)
     ☠︎︎⟨(fun _ _ => 15) ⟩         :Combined ;  (* ☠︎︎ ENDORSE plan value *)
     (pt ← (fun s => s pu))      :Combined ;  (* pt ← pu  !!ENDORSE!! *)
     ☠︎︎⟨(fun _ pu => pu) ⟩        :Combined ;  (* ☠︎︎ noop *)
     (pt ← (fun s => s pt + 1))  :Combined    (* pt ← pt + 1 *)
  ].

Definition beh_real := prog_behavior running_example.
Definition beh_ideal := prog_behavior sim.

(* This is what we want to do *)
Goal beh_real = beh_ideal. (* This is what we want to do *) (* We don't even use functional_extensionaltiy here! *)
Proof.
  reflexivity.
Qed.
