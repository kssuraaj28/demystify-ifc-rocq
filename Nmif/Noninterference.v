From Stdlib Require ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore.
Import VarValStore.

Section ni.
  Context {I Iv O Ov: Type}.
  Notation CompType := (I -> O).
  (* You can think of *v as equivalence class *)
  Notation InpView := (I -> Iv).
  Notation OutView := (O -> Ov).


  Definition Noninterfering (comp : CompType) (iview : InpView) (oview : OutView): Prop :=
    forall i1 i2,
      iview i1 = iview i2 ->
      oview (comp i1) = oview (comp i2).
End ni.

(* TODO: Examples and tests.. *)
