Section ni.
  Context {I Iv O Ov: Type}.
  Notation Comp := (I -> O).
  Notation Iview := (I -> Iv).
  Notation Oview := (O -> Ov).

  Definition Noninterfering (iv: Iview) (comp: Comp) (ov: Oview) := 
    forall i1 i2,
      iv i1 = iv i2 ->
      ov (comp i1) = ov (comp i2).
End ni.
