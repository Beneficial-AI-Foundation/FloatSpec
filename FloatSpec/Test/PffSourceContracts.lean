import FloatSpec.src.Pff.Pff

/-!
# Pff source-contract regression surface

These declarations deliberately mention the public names, not their
`*_internal` implementation lemmas. They keep the restored Coq-facing
surface in the test dependency graph and make accidental removal or renaming
fail `FloatSpecTests`.
-/

#check FnormalPrecision
#check NormalAndSubNormalNotEq
#check ClosestErrorBoundNormal
#check RoundLeGeneral
#check delta_inf
#check MKnuth2
#check s2Le

example (b : Fbound_skel) (t : Nat) (pGe : 4 ≤ t) :
    ((t : Int) - (Nat.div2 t : Int)) +
        ((t : Int) - (Nat.div2 t : Int)) ≤ (t : Int) + 1 :=
  s2Le b t pGe
