import FloatSpec.src.Pff.Pff
import FloatSpec.src.Pff.Pff2Flocq
import FloatSpec.src.Pff.Pff2FlocqAux
import FloatSpec.src.Pff.SourceFacade
import FloatSpec.src.Calc.Plus
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Round
import FloatSpec.src.Prop.Relative
import FloatSpec.src.Prop.Double_rounding
import FloatSpec.src.Prop.Round_odd
import FloatSpec.src.Prop.Div_sqrt_error
import FloatSpec.src.Prop.Plus_error
import FloatSpec.src.Prop.Mult_error

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

/-! Prop source-contract regression groups. -/

-- Raw rounding functions remain source-visible; `Mode` is only a helper API.
#check round_round_mult
#check round_round_mult_FLX
#check round_round_mult_FLT
#check round_round_mult_FTZ

-- Coq-erased section payloads stay internal.
#check generic_format_fexpe_fexp
#check d_eq
#check u_eq
#check d_ge_0
#check mag_d
#check Fexp_d
#check format_bpow_x
#check format_bpow_d
#check d_le_m
#check m_le_u
#check mag_m
#check mag_m_0
#check u'_eq
#check m_eq
#check m_eq_0
#check fexp_m_eq_0
#check DN_odd_d_aux
#check UP_odd_d_aux

-- Source statements without proof-only `Valid_exp` payloads.
#check round_repr_same_exp
#check generic_format_plus_prec
#check sqrt_error_N_FLX_aux1
#check mult_bpow_exact_FLX
#check mult_bpow_exact_FLT
#check mult_bpow_pos_exact_FLT
#check round_round_mult_aux
#check mag_plus_separated
#check round_round_plus_aux0_aux_aux
#check round_round_plus_aux0_aux
#check round_round_plus_aux0
#check round_round_minus_aux0_aux
#check round_round_minus_aux0
#check round_round_plus_radix_ge_3_aux0
#check round_round_minus_radix_ge_3_aux0

-- Coq's explicit `1 < prec` premises remain on the public sqrt family.
#check sqrt_error_N_FLX_aux2
#check sqrt_error_N_FLX_aux3
#check sqrt_error_N_FLX
#check sqrt_error_N_FLX_ex
#check sqrt_error_N_FLX_round_ex
#check sqrt_error_N_FLT_ex
#check sqrt_error_N_FLT_round_ex
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

/-! T42 Calc/Core source-contract regressions. -/

-- Coq positive digits count positions from zero.
example : FloatSpec.Core.Digits.digits2_Pnat 1 = 0 := by
  norm_num [FloatSpec.Core.Digits.digits2_Pnat,
    FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload]

-- The source helper compares its signed parameter, not its absolute value.
example : FloatSpec.Core.Digits.Zdigits_aux 2 (-1) 5 0 1 = 5 := by
  rfl

-- The public digit count still supplies the positive magnitude on negatives.
example : FloatSpec.Core.Digits.Zdigits 2 (-1) = 1 := by
  rfl

-- Coq exports the inverse-base equality and its nonzero premise.
example : ((2 : Real)⁻¹) ^ (3 : Int) = ((2 : Real) ^ (3 : Int))⁻¹ :=
  powerRZ_inv 2 3 (by norm_num)

-- Coq `Z.sqrtrem` totalizes a negative input to `(0,0)`.
example : FloatSpec.Calc.Sqrt.Fsqrt_core 2 (-1) 0 0 =
    (0, FloatSpec.Calc.Bracket.Location.loc_Exact) := by
  rfl

-- Coq `Zpower` totalizes a negative scaling exponent to zero.
example : FloatSpec.Calc.Sqrt.Fsqrt_core 2 1 0 1 =
    (0, FloatSpec.Calc.Bracket.Location.loc_Exact) := by
  decide

-- The source-facing Pff definition remains callable at an unrestricted radix.
example : FloatSpec.Pff.Source.boundR 1 0 =
    FloatSpec.Pff.Source.float.mk 1 1 := by
  norm_num [FloatSpec.Pff.Source.boundR, FloatSpec.Pff.Source.boundNat,
    _root_.digit]
  decide

example : FloatSpec.Pff.Source.boundR 1 0 =
    FloatSpec.Pff.Source.boundR 1 (-0) :=
  FloatSpec.Pff.Source.boundRrOpp 1 0

-- Signed division uses the shared Coq `Z.div_eucl` semantics.
example : FloatSpec.Core.Zaux.Z_div_eucl 5 (-3) = (-2, -1) := by
  decide

#check FloatSpec.Calc.Div.Fdiv_core
#check FloatSpec.Calc.Div.Fdiv_correct
#check FloatSpec.Core.Digits.Zdigits_aux
#check powerRZ_inv
#check FloatSpec.Core.Digits.ZOmod_plus_pow_digit
#check FloatSpec.Core.Digits.ZOdiv_plus_pow_digit
#check FloatSpec.Core.FLT.FLT_format
#check FloatSpec.Core.FLX.FLX_format
#check FloatSpec.Core.FLX.FLXN_format
#check FloatSpec.Core.Float_prop.F2R_lt
#check FloatSpec.Core.Generic_fmt.round_NA_pt
#check FloatSpec.Core.Generic_fmt.round_N0_pt
#check FloatSpec.Core.RoundNE.DN_UP_parity_pos_prop
#check FloatSpec.Core.RoundNE.round_NE_pt_pos
#check FloatSpec.Core.Ulp.round_N_ge_ge_midp
#check FloatSpec.Core.Ulp.round_N_le_le_midp
#check @relative_error_FLX_aux
#check @relative_error_FLT_aux
#check @FloatSpec.Pff.Source.FtoR
#check @FloatSpec.Pff.Source.UniqueP
#check @FloatSpec.Pff.Source.MonotoneP
#check @FloatSpec.Pff.Source.MinExList
#check @Zpower_nat_less

example : (0 : Int) ≤ 0 - FLX_exp 0 0 :=
  relative_error_FLX_aux 0 0

example : (0 : Int) ≤ 0 - FLT_exp 0 0 0 :=
  relative_error_FLT_aux 0 0 0 (by norm_num)

example : pos_length ⟨0⟩ = 0 := by decide
example : pos_length ⟨1⟩ = 1 := by decide
example : pos_length ⟨2⟩ = 1 := by decide
example : digitAux 2 5 1 ⟨0⟩ = 0 := by decide
example : digitAux 2 5 1 ⟨1⟩ = 1 := by decide

example : 0 < (2 : Int) ^ (0 : Nat) := by
  simpa only [wp, PostCond.noThrow, pure, Zpower_nat_less_check,
    Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply,
    SPred.down_pure_nil] using Zpower_nat_less 2 0 (by norm_num)

example : FloatSpec.Pff.Source.UniqueP 1
    (fun _ p => p = ⟨1, 0⟩) := by
  simp [FloatSpec.Pff.Source.UniqueP]

example : FloatSpec.Pff.Source.MonotoneP 0
    (fun _ p => p = ⟨0, 0⟩) := by
  intro _ _ p q _ hp hq
  subst p
  subst q
  exact le_rfl

example : FloatSpec.Pff.Source.FtoR 0 ⟨1, 1⟩ = 0 := by
  norm_num [FloatSpec.Pff.Source.FtoR]

example := FloatSpec.Pff.Source.MinExList 1 0 []

/-- A concrete application of the restored source-facing contract.  This
guards the public theorem's Hoare wrapper as well as its binder order. -/
example :
    |(2 : Real) - _root_.F2R (beta := 2)
        (⟨2, 0⟩ : FloatSpec.Core.Defs.FlocqFloat 2)| ≤
      |_root_.F2R (beta := 2)
        (⟨2, 0⟩ : FloatSpec.Core.Defs.FlocqFloat 2)| *
        ((1 / 2 : Real) * (2 : Real) ^ (1 - (2 : Int))) := by
  have h := ClosestErrorBoundNormal
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
             FloatSpec.Core.Digits.Zdigits]⟩
  simp only [wp, PostCond.noThrow, pure, ClosestErrorBoundNormal_check,
    Id.run, ULift.up_down, PredTrans.pure, PredTrans.apply,
    SPred.down_pure_nil] at h
  convert h using 1 <;> norm_num
