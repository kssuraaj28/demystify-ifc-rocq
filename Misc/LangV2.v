(* This is a different version of the language. 
Now, we have a more message passing style communication with the adversary..

I think that extending this to more control flow might be useful.

*)


(* 
I'll just start with 2 point lattice for now..

Then, I should only worry about the variables that I write to..
*)

Inductive Lbl := secret | public.

(* TODO: Should this be {Vars?}
Another thing: Should I make this Dec
Which existing library has this?
*)

Class VarPrm (Vars : Type) := { 
  var_lbl : Vars -> Lbl
  }.

Class ValPrm (Vals : Type).

Section cmd.
  Set Mangle Names. (* TODO: Remove this. *)
  Generalizable Variables Vars Vals.  Fail Check Vars.
  Context `{VarPrm Vars} `{ValPrm Vals}. Check Vars.

  Record Cmd := {src : Vars; dest : Vars; compute : Vals -> Vals}.
  Definition Program := list Cmd. 
End cmd.


(* Define what an attacker is. *)
(* Then we define what state is. *)

(* 
   Should the value of the program counter be sent to the attacker at every step? 
   Sure, why not....
   Then `if (secret) { p <- 0  } { p <- 0  }`. will be considered to violate noninterference.
   This is a slightly difference notion of security, where we actually model adversary corruption
*)

(* Attacker. *)

