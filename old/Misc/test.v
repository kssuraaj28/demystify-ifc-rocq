From Stdlib Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Print Options.

Locate "=".

Lemma add_comm : forall n m, n + m = m + n.
Proof.
Proof Mode "Classic".
elim=> [|n IHn] m.          (* Induction on n: base case and inductive step *)
- simpl. 
- 
  by rewrite addn0.         (* Base case (0 + m = m + 0) solved by lemma addn0 *)
by rewrite /= IHn addnS.    (* Step: simplify, use IH, and apply successor lemma *)
Qed.

Goal (eq 1 1).


Lemma add_comm (a b : nat) : a + b = b + a.
Proof.
  elim => //= [| n IHn]. (* Induction on 'a', skipping base case with //=, then handling successor case *)
  move=> m. (* Move 'm' (b in the original goal) into the context *)
  rewrite IHn. (* Rewrite using the inductive hypothesis (n + m = m + n) *)
  reflexivity. (* Show 0 + m = m + 0 *)
Qed.
Goal False.
  Proof Mode "Classic".
  move 3.
  idtac "h".
  
