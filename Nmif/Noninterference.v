From Stdlib Require ssreflect ssrbool.
Import ssreflect ssrbool.

Require VarValStore.
Import VarValStore.

Section ni.
  Import VarValStore.Notations.
  Context `{!VarPrm, !ValPrm}.

  (* Is this the right definition? I don't even know *)
  Definition Noninterfering (p: pred Vars) (comp : Store -> Store) :=
    forall s1 s2,
    ⟨ s1 | p ⟩ = ⟨ s2 | p⟩ ->
    ⟨ comp s1 | p ⟩ = ⟨ comp s2 | p⟩.
      
End ni.
