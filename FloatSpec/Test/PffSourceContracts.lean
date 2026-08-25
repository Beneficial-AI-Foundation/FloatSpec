import FloatSpec.src.Pff.Pff

open Std.Do

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

/-- A concrete application of the restored source-facing contract.  This
guards the public theorem's Hoare wrapper as well as its binder order. -/
example :
    |(2 : Real) - _root_.F2R (beta := 2)
        (⟨2, 0⟩ : FloatSpec.Core.Defs.FlocqFloat 2)| ≤
      |_root_.F2R (beta := 2)
        (⟨2, 0⟩ : FloatSpec.Core.Defs.FlocqFloat 2)| *
        ((1 / 2 : Real) * (2 : Real) ^ (1 - (2 : Int))) := by
  simpa only [wp, PostCond.noThrow, pure, ClosestErrorBoundNormal_check,
    Id.run, ULift.up_down] using
      (ClosestErrorBoundNormal
        ({ dExp := 0, vNum := 4 } : Fbound_skel)
        2 2 (2 : Real)
        (⟨2, 0⟩ : FloatSpec.Core.Defs.FlocqFloat 2)
        ⟨by norm_num,
         by norm_num,
         by norm_num [Zpower_nat],
         by
           constructor
           · norm_num [Fbounded]
           · intro g _hg
             norm_num [_root_.F2R],
         by
           norm_num [Fnormal, Fnormalize, Fbounded, Fdigit, Fshift,
             FloatSpec.Core.Digits.Zdigits]⟩)
