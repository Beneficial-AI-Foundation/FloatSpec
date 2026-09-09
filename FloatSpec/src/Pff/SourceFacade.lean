import FloatSpec.src.Pff.Pff

/-!
# Source-faithful Pff boundary

The legacy `Pff.v` development predates FLoCq's radix-indexed Core float.  Its
exported `float` record is therefore independent of a radix, and operations
such as `FtoR`, `digit`, and `Fnormalize` take an unrestricted integer radix.

The main translated Pff implementation is integrated with FloatSpec's
radix-indexed Core representation.  This module provides the exact external
Pff data model and explicit bridges at the boundary, instead of silently
adding `[ValidRadix beta]` to source declarations that do not export it.
-/

namespace FloatSpec.Pff.Source

/-- Coq `Pff.float`: an unindexed pair of integer mantissa and exponent. -/
structure float where
  Fnum : Int
  Fexp : Int
deriving DecidableEq, Repr

/-- Forget the Core radix index. -/
def float.ofCore {beta : Int} [ValidRadix beta]
    (x : FloatSpec.Core.Defs.FlocqFloat beta) : float :=
  ⟨x.Fnum, x.Fexp⟩

/-- Refine a source Pff float into the Core carrier at a valid radix. -/
def float.toCore (beta : Int) [ValidRadix beta]
    (x : float) : FloatSpec.Core.Defs.FlocqFloat beta :=
  ⟨x.Fnum, x.Fexp⟩

@[simp] theorem float.ofCore_toCore (beta : Int) [ValidRadix beta]
    (x : float) : float.ofCore (x.toCore beta) = x := by
  cases x
  rfl

@[simp] theorem float.toCore_ofCore {beta : Int} [ValidRadix beta]
    (x : FloatSpec.Core.Defs.FlocqFloat beta) :
    (float.ofCore x).toCore beta = x := by
  cases x
  rfl

/-- Coq `Pff.FtoR`, total at every integer radix exported by the source. -/
noncomputable def FtoR (radix : Int) (x : float) : Real :=
  (x.Fnum : Real) * (radix : Real) ^ x.Fexp

/-- At a valid matching radix, the source observer agrees definitionally with
FloatSpec's indexed Core observer. -/
@[simp] theorem FtoR_toCore (beta : Int) [ValidRadix beta] (x : float) :
    FtoR beta x = _root_.F2R (x.toCore beta) := by
  rfl

def Fle (radix : Int) (x y : float) : Prop :=
  FtoR radix x ≤ FtoR radix y

def UniqueP (radix : Int) (P : Real → float → Prop) : Prop :=
  ∀ r p q, P r p → P r q → FtoR radix p = FtoR radix q

def MonotoneP (radix : Int) (P : Real → float → Prop) : Prop :=
  ∀ p q p' q', p < q → P p p' → P q q' →
    FtoR radix p' ≤ FtoR radix q'

theorem MinExList (radix : Int) (r : Real) (L : List float) :
    (∀ f ∈ L, r < FtoR radix f) ∨
    ∃ min ∈ L, FtoR radix min ≤ r ∧
      ∀ f ∈ L, FtoR radix f ≤ r → FtoR radix f ≤ FtoR radix min := by
  induction L with
  | nil => left; simp
  | cons a L ih =>
      by_cases ha : FtoR radix a ≤ r
      · right
        rcases ih with hall | ⟨m, hm, hmr, hmin⟩
        · exact ⟨a, by simp, ha, fun f hf hfr => by
            rcases List.mem_cons.mp hf with rfl | hf
            · exact le_rfl
            · exact absurd hfr (not_le.mpr (hall f hf))⟩
        · by_cases ham : FtoR radix a ≤ FtoR radix m
          · exact ⟨m, by simp [hm], hmr, fun f hf hfr => by
              rcases List.mem_cons.mp hf with rfl | hf
              · exact ham
              · exact hmin f hf hfr⟩
          · exact ⟨a, by simp, ha, fun f hf hfr => by
              rcases List.mem_cons.mp hf with rfl | hf
              · exact le_rfl
              · exact (hmin f hf hfr).trans (le_of_not_ge ham)⟩
      · push Not at ha
        rcases ih with hall | ⟨m, hm, hmr, hmin⟩
        · left
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact ha
          · exact hall f hf
        · right
          exact ⟨m, by simp [hm], hmr, fun f hf hfr => by
            rcases List.mem_cons.mp hf with rfl | hf
            · exact absurd hfr (not_le.mpr ha)
            · exact hmin f hf hfr⟩

def Fopp (x : float) : float :=
  ⟨-x.Fnum, x.Fexp⟩

def Fabs (x : float) : float :=
  ⟨x.Fnum.natAbs, x.Fexp⟩

/-- Coq `Pff.boundNat`, including its total behavior at every integer radix. -/
-- Source ID: Pff/Pff.v:boundNat:150939
noncomputable def boundNat (radix : Int) (n : Nat) : float :=
  ⟨1, _root_.digit radix n⟩

/-- Coq `Pff.boundR`; `up` is the strict ceiling `floor x + 1`. -/
-- Source ID: Pff/Pff.v:boundR:151409
noncomputable def boundR (radix : Int) (r : Real) : float :=
  boundNat radix (Int.natAbs (Int.floor |r| + 1))

/-- Coq `Pff.boundRrOpp`. -/
-- Source ID: Pff/Pff.v:boundRrOpp:152106
theorem boundRrOpp (radix : Int) (r : Real) :
    boundR radix r = boundR radix (-r) := by
  simp [boundR, abs_neg]

def Fplus (radix : Int) (x y : float) : float :=
  let commonExp := min x.Fexp y.Fexp
  ⟨x.Fnum * radix ^ Int.natAbs (x.Fexp - commonExp) +
      y.Fnum * radix ^ Int.natAbs (y.Fexp - commonExp),
    commonExp⟩

def Fminus (radix : Int) (x y : float) : float :=
  Fplus radix x (Fopp y)

/-- Source-shaped counterpart of Coq's `positive × N` bound record. -/
structure Fbound where
  vNum : Nat
  dExp : Nat
  vNum_pos : 0 < vNum

/-- Refine the source carrier into the arithmetic-friendly integrated bound. -/
def Fbound.toIntegrated (b : Fbound) : _root_.Fbound :=
  { vNum := b.vNum
    dExp := b.dExp
    vNum_pos := by exact_mod_cast b.vNum_pos
    dExp_nonneg := by omega }

/-- Forget the integer refinement representation used by the integrated layer. -/
def Fbound.ofIntegrated (b : _root_.Fbound) : Fbound :=
  { vNum := b.vNum.natAbs
    dExp := b.dExp.natAbs
    vNum_pos := by
      rw [Int.natAbs_pos]
      exact ne_of_gt b.vNum_pos
    }

@[simp] theorem Fbound.ofIntegrated_toIntegrated (b : Fbound) :
    Fbound.ofIntegrated b.toIntegrated = b := by
  cases b with
  | mk vNum dExp vNum_pos =>
      simp [Fbound.toIntegrated, Fbound.ofIntegrated]

@[simp] theorem Fbound.toIntegrated_ofIntegrated (b : _root_.Fbound) :
    (Fbound.ofIntegrated b).toIntegrated = b := by
  cases b with
  | mk dExp vNum dExp_nonneg vNum_pos =>
      simp [Fbound.ofIntegrated, Fbound.toIntegrated,
        Int.natAbs_of_nonneg dExp_nonneg,
        Int.natAbs_of_nonneg (le_of_lt vNum_pos)]

def Fbounded (b : Fbound) (x : float) : Prop :=
  |x.Fnum| < (b.vNum : Int) ∧ -(b.dExp : Int) ≤ x.Fexp

def Fnormal (radix : Int) (b : Fbound) (x : float) : Prop :=
  Fbounded b x ∧ (b.vNum : Int) ≤ |radix * x.Fnum|

def Fsubnormal (radix : Int) (b : Fbound) (x : float) : Prop :=
  Fbounded b x ∧ x.Fexp = -(b.dExp : Int) ∧
    |radix * x.Fnum| < (b.vNum : Int)

def Fcanonic (radix : Int) (b : Fbound) (x : float) : Prop :=
  Fnormal radix b x ∨ Fsubnormal radix b x

@[simp] theorem Fbounded_toCore (beta : Int) [ValidRadix beta]
    (b : Fbound) (x : float) :
    Fbounded b x ↔ _root_.Fbounded b.toIntegrated (x.toCore beta) := by
  rfl

@[simp] theorem Fnormal_toCore (beta : Int) [ValidRadix beta]
    (radix : Int) (b : Fbound) (x : float) :
    Fnormal radix b x ↔
      _root_.Fnormal radix b.toIntegrated (x.toCore beta) := by
  rfl

@[simp] theorem Fsubnormal_toCore (beta : Int) [ValidRadix beta]
    (radix : Int) (b : Fbound) (x : float) :
    Fsubnormal radix b x ↔
      _root_.Fsubnormal radix b.toIntegrated (x.toCore beta) := by
  rfl

@[simp] theorem Fcanonic_toCore (beta : Int) [ValidRadix beta]
    (radix : Int) (b : Fbound) (x : float) :
    Fcanonic radix b x ↔
      _root_.Fcanonic radix b.toIntegrated (x.toCore beta) := by
  rfl

private def digitAuxFuel (radix value : Int) : Int → Nat → Nat
  | _, 0 => 0
  | power, fuel + 1 =>
      if power > value then 0
      else Nat.succ (digitAuxFuel radix value (radix * power) fuel)

/-- Coq `Pff.digit`, retaining the source structural recursion on the entire
integer-radix domain.  The fuel is the constructor depth of `xO |q|`. -/
def digit (radix q : Int) : Nat :=
  if q = 0 then 0
  else digitAuxFuel radix q.natAbs 1 (Nat.log2 q.natAbs + 1)

def Fdigit (radix : Int) (x : float) : Nat :=
  digit radix x.Fnum

def Fshift (radix : Int) (amount : Nat) (x : float) : float :=
  ⟨x.Fnum * radix ^ amount, x.Fexp - (amount : Int)⟩

/-- Coq `Pff.Fnormalize`, including its observable behavior outside the
section's non-exported `1 < radix` hypothesis. -/
def Fnormalize (radix : Int) (b : Fbound) (precision : Nat)
    (x : float) : float :=
  if x.Fnum = 0 then
    ⟨0, -(b.dExp : Int)⟩
  else
    Fshift radix
      (min (precision - Fdigit radix x)
        (Int.natAbs ((b.dExp : Int) + x.Fexp)))
      x

/-- Coq `Pff.Fulp`, observed using the same explicit radix that normalization
uses rather than an independent type index. -/
noncomputable def Fulp (b : Fbound) (radix : Int) (precision : Nat)
    (x : float) : Real :=
  (radix : Real) ^ (Fnormalize radix b precision x).Fexp

/-- Coq `Pff.nNormMin`, retaining the source `Nat.pred` at precision zero. -/
noncomputable def nNormMin (radix : Int) (precision : Nat) : Int :=
  Zpower_nat radix (Nat.pred precision)

/-- Coq `Pff.firstNormalPos`. -/
noncomputable def firstNormalPos (radix : Int) (b : Fbound)
    (precision : Nat) : float :=
  ⟨nNormMin radix precision, -(b.dExp : Int)⟩

/-- Coq `Pff.RND_Min_Pos`.

The source declaration has one explicit radix and a natural precision.  In
particular, the threshold is observed with that same radix; there is no
independent type-level `beta` that could select a different branch. -/
noncomputable def RND_Min_Pos (b : Fbound) (radix : Int)
    (precision : Nat) (r : Real) : float :=
  let firstNormPosValue := FtoR radix (firstNormalPos radix b precision)
  if firstNormPosValue ≤ r then
    let e : Int :=
      IRNDD (Real.log r / Real.log (radix : Real) +
        (-(precision : Int) + 1 : Int))
    ⟨IRNDD (r * (radix : Real) ^ (-e)), e⟩
  else
    ⟨IRNDD (r * (radix : Real) ^ (b.dExp : Int)), -(b.dExp : Int)⟩

end FloatSpec.Pff.Source
