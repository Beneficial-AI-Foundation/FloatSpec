import FloatSpec.src.IEEE754.Binary

/-!
# Source-faithful rounding-mode boundary

`BinarySingleNaN.v` exposes a five-constructor `mode` datatype and a
`round_mode` interpretation.  FloatSpec's integrated IEEE layer uses the
idiomatic `RoundingMode` names instead.  This facade preserves the exact Coq
surface and proves that it is only a renaming, not a second rounding model.
-/

namespace FloatSpec.IEEE754.BinarySingleNaN.Source

/-- Coq `BinarySingleNaN.mode`, with the source constructor names and order. -/
inductive mode where
  | mode_NE
  | mode_ZR
  | mode_DN
  | mode_UP
  | mode_NA
deriving DecidableEq, Repr

/-- Embed the source-facing mode into FloatSpec's integrated IEEE API. -/
def mode.toRoundingMode : mode → RoundingMode
  | mode.mode_NE => RoundingMode.RNE
  | mode.mode_ZR => RoundingMode.RTZ
  | mode.mode_DN => RoundingMode.RTN
  | mode.mode_UP => RoundingMode.RTP
  | mode.mode_NA => RoundingMode.RNA

/-- Recover the exact source-facing constructor from the integrated API. -/
def mode.ofRoundingMode : RoundingMode → mode
  | RoundingMode.RNE => mode.mode_NE
  | RoundingMode.RTZ => mode.mode_ZR
  | RoundingMode.RTN => mode.mode_DN
  | RoundingMode.RTP => mode.mode_UP
  | RoundingMode.RNA => mode.mode_NA

@[simp] theorem mode.ofRoundingMode_toRoundingMode (m : mode) :
    mode.ofRoundingMode m.toRoundingMode = m := by
  cases m <;> rfl

@[simp] theorem mode.toRoundingMode_ofRoundingMode (m : RoundingMode) :
    (mode.ofRoundingMode m).toRoundingMode = m := by
  cases m <;> rfl

/-- Coq `BinarySingleNaN.round_mode`.

The five branches are definitionally the same functions as the integrated
`rnd_of_mode`; spelling them through that implementation prevents the source
facade and the reusable API from drifting apart.
-/
noncomputable def round_mode (m : mode) : Real → Int :=
  rnd_of_mode m.toRoundingMode

@[simp] theorem round_mode_eq_rnd_of_mode (m : mode) :
    round_mode m = rnd_of_mode m.toRoundingMode := by
  rfl

noncomputable instance valid_round_mode (m : mode) :
    FloatSpec.Core.Generic_fmt.Valid_rnd (round_mode m) := by
  unfold round_mode
  infer_instance

end FloatSpec.IEEE754.BinarySingleNaN.Source
