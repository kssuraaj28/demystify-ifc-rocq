(* Here, the point is to show how the crypto view and the information flow view are equal, if you have nmif 
Let us start with a very simple program. Then we try to see how
*)

From Stdlib Require Import List.

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
    match c with dest ← cmp => 
      let new_val := cmp s in 
      let old_val := s var in 
      if var_eq_dec var dest then 
        new_val
      else
        old_val
    end.

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
  Compute s' pu.
  Compute s' pt.
  Compute s' st.
End test.

Definition AtkSnip := Value -> Value -> Value. (* pt -> pu -> pu *)
Section atksnip_sem.
  Variables (a: AtkSnip) (s : State).

  Definition atksnip_sem : State:=
    let pu_v := a (s pt) (s pu) in
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
    Let zero_atk : AtkSnip := fun _ _ => 0.

    Let s' := atksnip_sem zero_atk s.
    Goal s' pu = 0. cbv. reflexivity. Qed.
    Goal s' pt = s pt. cbv. reflexivity. Qed.
    Goal s' st = s st. cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
  End zero.

  Section sum.
    Let sum_atk : AtkSnip := fun x y => x + y.

    Let s' := atksnip_sem sum_atk s.
    Goal s' pu = s pt + s pu. cbv. reflexivity. Qed.
    Goal s' pt = s pt. cbv. reflexivity. Qed.
    Goal s' st = s st. cbv. reflexivity. Qed. (* We could have theorem that says this for all atk *)
  End sum.
End test.

Definition Combined : Type := (Cmd + AtkSnip).
Definition combined_sem (c : Combined) (s : State) : State. Proof. (* I wonder how things might look if I used case instead *)
  destruct c.
  - exact (cmd_sem c s).
  - exact (atksnip_sem a s).
Defined.
  

Definition Prog := list Combined.
Import ListNotations.

Fixpoint prog_sem (p : Prog) : State -> State :=
  match p with
  | [] => 
      fun inp_state => inp_state
  | c :: p' => 
      fun inp_state => 
        prog_sem p' (combined_sem c inp_state)
  end.

Section test.
  Let s : State :=
    fun v => match v with
             | st => 67
             |pt => 3
             | pu => 58
             end.

  Let c : Compute :=
    fun s => s st + s pt + s pu.

  Let p : Prog := 
    [
    inl (pu ← c); 
    inl (st ← c); 
    inl (pt ← c)
    ].

  Let s' := prog_sem p s.
  Compute s' pu.
  Compute s' pt.
  Compute s' st.
End test.
