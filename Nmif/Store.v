From Stdlib Require ssreflect ssrbool. 
Import ssreflect ssrbool.

Require Util VarVal.
Import VarVal Util.Notations.

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
