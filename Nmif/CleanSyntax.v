Require Import VarVal MetaSyntax.

Section clean_syntax.
  Context `{!VarPrm, !ValPrm}.

  Definition VarSrc := Vars.
  Definition VarDst := Vars.

  Hint Extern 0 SrcDstVarPrm => 
    (exact {|SrcVarMeta := VarSrc; DstVarMeta := VarDst|}) : typeclass_instances.

  Definition ValExp := ValExpMeta.
  Definition BoolExp := BoolExpMeta.
  Definition Cmd := CmdMeta.
End clean_syntax.
