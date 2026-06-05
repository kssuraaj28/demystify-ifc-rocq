From Stdlib Require List ssreflect ssrfun ssrbool.
Import List ListNotations ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section preds.
  Import Util.DecEq Util.DecEq.Notations.

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Definition extract_controlled_endorse (c: Cmd) : option (Vars * Vars) :=
    match c with
    | assign (endorse from to) =>
      if (var_lbl from =? pulbl) && (var_lbl to =? ptlbl) is false then None else
      Some (from, to)
    | _ => None
    end.

  Definition extract_controlled_declassify (c: Cmd) : option (Vars * Vars) :=
    match c with
    | assign (declassify from to) =>
      if (var_lbl from =? stlbl) && (var_lbl to =? ptlbl) is false then None else
      Some (from, to)
    | _ => None
    end.

  Lemma extr_endorse_eq c from to :
    extract_controlled_endorse c = Some (from, to) ->
    c = assign (endorse from to) /\ var_lbl from = pulbl /\ var_lbl to = ptlbl.
  Proof. 
    case: c=> // - [] // >.
    rewrite/extract_controlled_endorse.
    case e1: (_ =? _); [apply dec_eq_true in e1| apply dec_eq_false in e1]=> //.
    case e2: (_ =? _); [apply dec_eq_true in e2| apply dec_eq_false in e2]=> //= - [<- <-] //.
  Qed.

  Lemma extr_decl_eq c from to :
    extract_controlled_declassify c = Some (from, to) ->
    c = assign (declassify from to) /\ var_lbl from = stlbl /\ var_lbl to = ptlbl.
  Proof. 
    case: c=> // - [] // >.
    rewrite/extract_controlled_declassify.
    case e1: (_ =? _); [apply dec_eq_true in e1| apply dec_eq_false in e1]=> //.
    case e2: (_ =? _); [apply dec_eq_true in e2| apply dec_eq_false in e2]=> //= - [<- <-] //.
  Qed.

  Lemma extr_endorse_opt oc from to:
    oapp extract_controlled_endorse None oc = Some (from, to) ->
    oc = Some (assign (endorse from to))
      /\ var_lbl from = pulbl /\ var_lbl to = ptlbl.
  Proof.
    case: oc=> //= c /extr_endorse_eq [-> ?]; by [].
  Qed.

  Lemma extr_decl_opt oc from to:
    oapp extract_controlled_declassify None oc = Some (from, to) ->
    oc = Some (assign (declassify from to))
      /\ var_lbl from = stlbl /\ var_lbl to = ptlbl.
  Proof.
    case: oc=> //= c /extr_decl_eq [-> ?]; by [].
  Qed.

  Fact extract_endorse_decl from to :
    extract_controlled_endorse (assign (declassify from to)) = None.
  Proof. done. Qed.

  Fact extract_decl_endorse from to :
    extract_controlled_declassify (assign (endorse from to)) = None.
  Proof. done. Qed.
End preds.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> extract_endorse_decl) "extract_endorse_decl" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> extract_decl_endorse) "extract_decl_endorse" old.

Ltac2 this_cookbook () := this_cookbook_ ().
