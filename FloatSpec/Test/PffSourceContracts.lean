import FloatSpec.src.Pff.Pff
import FloatSpec.src.Pff.Pff2Flocq
import FloatSpec.src.Pff.Pff2FlocqAux
import FloatSpec.src.Calc.Plus
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Round
import FloatSpec.src.Prop.Relative

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
#check dExpPrim
#check NormalbPrim
#check Dekker2_aux
#check Dekker2
#check RoundLeNormal
#check dp_dq_le
#check abeLeab
#check ErrorBoundedIplus
#check MDekkerAux1
#check Dekker1_FTS
#check Dekker3
#check MDekker
#check Dekker_FTS
#check Fulp_le_twice_r_round
#check zPos
#check uhPos
#check FmaErr_aux1
#check FmaErr_aux2
#check errorBoundedPlusLe
#check LeExpRound
#check LeExpRound2
#check errorBoundedPlusAbs
#check errorBoundedPlus
#check Fma_FTS
#check MKnuth
#check MKnuth1
#check MKnuth3
#check MKnuth4
#check MKnuth5
#check MKnuth6
#check MKnuth7
#check Knuth
#check errorBoundedMultClosest_aux
#check errorBoundedMultClosest
#check plusExact1
#check plusExact2Aux
#check plusExact2
#check LeExp1
#check plusExactExp
#check AddExpGe1Underf
#check AddExpGe1Underf2
#check plusExactR0
#check ExactSum_Near
#check xLe2y_aux1
#check xLe2y_aux2
#check xLe2y
#check Subexact
#check gatCorrect
#check Expbe1
#check be2MuchSmaller
#check gaCorrect
#check tBounded_aux
#check tBounded
#check ErrFmaApprox_1_aux
#check ErrFmaApprox_1
#check LeExp2
#check LeExp3
#check LeExp
#check vLe_aux
#check vLe
#check tLe
#check wLe
#check ErrFmaApprox_2_aux
#check ErrFmaApprox_2
#check ErrFmaApprox
#check delta_inf
#check MKnuth2
#check s2Le
#check CompatibleP
#check MonotoneP
#check MinOrMaxP
#check RoundedModeP
#check ProjectorP
#check RoundedProjector
#check RoundedModeProjectorIdem
#check RoundedModeBounded
#check RoundedModeProjectorIdemEq
#check MinOrMaxRep
#check RoundedModeRep
#check FloatSpec.Calc.Plus.Fplus_core_correct
#check FloatSpec.Calc.Plus.Fplus_correct

/-! Every declaration named by the FLoCq alignment repair checklist remains
available under its source-facing name.  Payload helpers are intentionally not
checked here. -/

#check FloatSpec.Core.Float_prop.F2R_lt_bpow
#check FloatSpec.Core.Ulp.pred_le
#check FloatSpec.Core.Ulp.succ_le
#check FloatSpec.Core.Ulp.pred_le_inv
#check FloatSpec.Core.Ulp.succ_le_inv
#check FloatSpec.Core.Ulp.pred_lt
#check FloatSpec.Core.Ulp.succ_lt
#check FloatSpec.Calc.Div.Fdiv_core_correct
#check relative_error_lt_conversion
#check relative_error_le_conversion
#check relative_error_le_conversion_inv
#check relative_error_le_conversion_round_inv
#check relative_error
#check relative_error_ex
#check relative_error_F2R_emin
#check relative_error_F2R_emin_ex
#check relative_error_round
#check relative_error_round_F2R_emin
#check relative_error_FLX
#check relative_error_FLX_ex
#check relative_error_FLX_round
#check relative_error_FLT
#check relative_error_FLT_F2R_emin
#check relative_error_FLT_F2R_emin_ex
#check relative_error_FLT_ex
#check RleBoundRoundl
#check RleBoundRoundr
#check FNoddEq
#check FNevenEq
#check ClosestMinEq
#check ClosestMaxEq
#check RleMinR0
#check RleMaxR0
#check RleRoundedR0
#check RleRoundedLessR0
#check div2IsBetweenPos
#check div2IsBetween
#check RND_Min_canonic
#check RND_Max_canonic
#check RND_Min_correct
#check RND_Max_correct
#check MinCompatible
#check MaxCompatible
#check ClosestCompatible
#check EvenClosestCompatible
#check ClosestMinOrMax
#check ClosestMonotone
#check EvenClosestMinOrMax
#check EvenClosestMonotone
#check ClosestZero
#check ClosestIdem
#check ClosestZero1
#check ClosestExp
#check ClosestErrorExpStrict
#check MinEx
#check MaxEx
#check MinRoundedModeP
#check MaxRoundedModeP
#check ClosestTotal
#check ClosestRoundedModeP
#check RoundAbsMonotoner
#check RoundAbsMonotonel
#check RoundedModeMult
#check RoundedModeMultLess
#check plusExpMin
#check plusExpUpperBound
#check plusExpBound
#check minusRoundRep
#check multExpUpperBound
#check errorBoundedMultPos
#check errorBoundedMultNeg
#check RoundedModeUlp
#check RoundedModeErrorExpStrict
#check errorBoundedMultExpPos
#check errorBoundedMultExp
#check MSBroundLSB
#check mBFadic_correct1
#check mBFadic_correct3
#check mBFadic_correct4
#check FboundedFzero
#check FnormalNotZero
#check FsubnormalFexp
#check FsubnormalUnique
#check FsubnormalLt
#check FcanonicLeastExp
#check MaxFloat
#check maxMax
#check maxMax1
#check FexpGeUnderf
#check pGeUnderf
#check qGeUnderf
#check maxFbounded
#check FmaErr_aux
#check FmaErr
#check Veltkamp_Even
#check Veltkamp
#check Veltkamp_tail
#check Dekker
#check ErrFmaAppr_correct
#check Axpy
#check ErrFMA_correct
#check ErrFMA_correct_simpl
#check discri1
#check discri2
#check discri3
#check discri4
#check discri5
#check discri6
#check discri7
#check discri8
#check discri9
#check discri10
#check discri11
#check discri12
#check discri13
#check discri14
#check discri15
#check «cases»
#check discri16
#check discri
#check discri_correct_test
#check discri_fp_test
#check ClosestErrorBound
#check FmultRadixInv
#check EvenClosestUniqueP
#check EvenClosestMonotone2
#check AddExpGeUnderf
#check AddExpGeUnderf2
#check RoundedModeMultAbs
#check RND_Closest_canonic
#check RND_Closest_correct
#check RND_EvenClosest_canonic
#check EvenClosestTotal
#check EvenClosestRoundedModeP
#check FloatSpec.Core.Generic_fmt.generic_round_generic
#check FloatSpec.Core.Generic_fmt.monotone_exp_not_FTZ
#check FloatSpec.Calc.Round.truncate_aux_comp
#check FloatSpec.Calc.Round.truncate_0
#check FloatSpec.Calc.Round.generic_format_truncate
#check FloatSpec.Calc.Round.truncate_correct_format
#check FloatSpec.Calc.Round.truncate_correct_partial'
#check FloatSpec.Calc.Round.truncate_correct_partial
#check FloatSpec.Calc.Round.truncate_correct'
#check FloatSpec.Calc.Round.truncate_correct
#check pff_format_is_format
#check round_NE_is_pff_round_b32
#check round_NE_is_pff_round_b64

example {beta : Int} [ValidRadix beta] (b : Fbound_skel) (radix : Int) :
    CompatibleP (beta:=beta) b (isMin (beta:=beta) b radix) :=
  MinCompatible b radix

example {beta : Int} [ValidRadix beta] (b : Fbound_skel) (radix : Int) :
    CompatibleP (beta:=beta) b (isMax (beta:=beta) b radix) :=
  MaxCompatible b radix

example (beta : Int) [ValidRadix beta] (b : Fbound) (p : Int)
    (hpBound : pGivesBound beta b p) (hprec : precisionNotZero p)
    (f : PffFloat beta) (hf : PFbounded b f) :
    generic_format beta (FLT_exp (-b.dExp) p) (pff_to_R_aux beta f) :=
  pff_format_is_format beta b p hpBound hprec f hf

example (b : Fbound_skel) (t : Nat) (pGe : 4 ≤ t) :
    ((t : Int) - (Nat.div2 t : Int)) +
        ((t : Int) - (Nat.div2 t : Int)) ≤ (t : Int) + 1 :=
  s2Le b t pGe

/-- Coq's positive `Npos (P_of_succ_nat ...)` contributes one even at the
small public edge cases; this distinguishes `plusExp` from truncated `t - 1`. -/
example : (plusExp ({ dExp := 0, vNum := 2 } : Fbound_skel) 1).dExp = 1 := by
  rfl

/-- Coq `up` is a strict ceiling.  At the integral input one it selects two,
not one. -/
example : boundR (beta:=2) 2 (1 : ℝ) = boundNat (beta:=2) 2 2 := by
  norm_num [boundR]

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
