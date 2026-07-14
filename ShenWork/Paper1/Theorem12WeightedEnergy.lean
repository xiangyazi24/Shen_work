import ShenWork.Paper1.Theorem12MeanCoefficients
import ShenWork.Paper1.Theorem12WeightedResolver
import ShenWork.PaperOne.WholeLineDiffusionIBPDecay
import ShenWork.PaperOne.WholeLineEnergyTimeLeibnizPDE
import ShenWork.PaperOne.WholeLineChemotaxisIBP

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Corrected Section 5 weighted-energy atoms

This file formalizes the estimates of `J₁,...,J₄` following the corrected
version of (5.19).  The estimates are first proved pointwise; integration and
the whole-line time/space regularity producer are kept in the later sections.

The corrected signal term is `χ(η b₃-b₄)VW`.  Its sign differs from the
printed (5.19), but the absolute `J₄` estimate is unchanged.
-/

/-- The corrected scalar coefficient multiplying the squared population
perturbation in (5.19). -/
def paper5CorrectedJ2Coefficient
    (p : CMParams) (η c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  η ^ 2 - c * η + 1 - paper5A (1 + p.α) u U t x -
    p.χ *
      (paper5CorrectedChemZeroCoefficient p u v U t x -
        η * paper5B1 p u v t x + paper5B2 p u v U t x)

/-- Pointwise Young estimate for the variable part of `J₁`. -/
theorem paper5J1VariableDensity_le
    (p : CMParams) {B1 x : ℝ} {b1 Wx W : ℝ → ℝ}
    (hb1 : |b1 x| ≤ B1) :
    -p.χ * b1 x * Wx x * W x ≤
      (1 / 2 : ℝ) * (Wx x) ^ 2 +
        (1 / 2 : ℝ) * |p.χ| ^ 2 * B1 ^ 2 * (W x) ^ 2 := by
  calc
    -p.χ * b1 x * Wx x * W x
        ≤ |-p.χ * b1 x * Wx x * W x| := le_abs_self _
    _ = |p.χ| * |b1 x| * |Wx x| * |W x| := by
      simp only [abs_neg, abs_mul]
    _ ≤ |p.χ| * B1 * |Wx x| * |W x| := by
      gcongr
    _ ≤ (1 / 2 : ℝ) * |Wx x| ^ 2 +
          (1 / 2 : ℝ) * (|p.χ| * B1 * |W x|) ^ 2 := by
      nlinarith [two_mul_le_add_sq (|Wx x|) (|p.χ| * B1 * |W x|)]
    _ = (1 / 2 : ℝ) * (Wx x) ^ 2 +
          (1 / 2 : ℝ) * |p.χ| ^ 2 * B1 ^ 2 * (W x) ^ 2 := by
      simp only [mul_pow, sq_abs]
      ring

/-- Corrected pointwise estimate behind (5.28).  It is uniform in the sign
of `χ`, unlike the one-sided intermediate assertion printed in the paper. -/
theorem paper5CorrectedJ2Coefficient_le
    (p : CMParams) {η c M B1 B2 t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hv : v t x ∈ Set.Icc (0 : ℝ) (M ^ p.γ))
    (hb1 : |paper5B1 p u v t x| ≤ B1)
    (hb2 : |paper5B2 p u v U t x| ≤ B2) :
    paper5CorrectedJ2Coefficient p η c u v U t x ≤
      η ^ 2 - c * η + 1 +
        |p.χ| *
          ((2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
            η * B1 + B2) := by
  have ha_nonneg : 0 ≤ paper5A (1 + p.α) u U t x := by
    exact paper5MeanCoefficient_nonneg (by linarith [p.hα]) hM hu hU
  have hzero :=
    paper5CorrectedChemZeroCoefficient_abs_le p hM hu hU hv
  have hηb1 : |η * paper5B1 p u v t x| ≤ η * B1 := by
    rw [abs_mul, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left hb1 hη
  have hinner :
      |paper5CorrectedChemZeroCoefficient p u v U t x -
          η * paper5B1 p u v t x + paper5B2 p u v U t x| ≤
        (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) + η * B1 + B2 := by
    calc
      |paper5CorrectedChemZeroCoefficient p u v U t x -
            η * paper5B1 p u v t x + paper5B2 p u v U t x|
          ≤ |paper5CorrectedChemZeroCoefficient p u v U t x -
                η * paper5B1 p u v t x| +
              |paper5B2 p u v U t x| := abs_add_le _ _
      _ ≤ |paper5CorrectedChemZeroCoefficient p u v U t x| +
            |η * paper5B1 p u v t x| +
              |paper5B2 p u v U t x| := by
          gcongr
          exact abs_sub _ _
      _ ≤ (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
            η * B1 + B2 := by
          gcongr
  have hchem :
      -p.χ *
          (paper5CorrectedChemZeroCoefficient p u v U t x -
            η * paper5B1 p u v t x + paper5B2 p u v U t x) ≤
        |p.χ| *
          ((2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
            η * B1 + B2) := by
    calc
      -p.χ *
          (paper5CorrectedChemZeroCoefficient p u v U t x -
            η * paper5B1 p u v t x + paper5B2 p u v U t x)
          ≤ |-p.χ *
              (paper5CorrectedChemZeroCoefficient p u v U t x -
                η * paper5B1 p u v t x + paper5B2 p u v U t x)| :=
            le_abs_self _
      _ = |p.χ| *
          |paper5CorrectedChemZeroCoefficient p u v U t x -
            η * paper5B1 p u v t x + paper5B2 p u v U t x| := by
            simp only [abs_neg, abs_mul]
      _ ≤ |p.χ| *
          ((2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
            η * B1 + B2) :=
        mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
  unfold paper5CorrectedJ2Coefficient
  linarith

/-- Pointwise Young estimate for the corrected `J₃` density. -/
theorem paper5J3Density_le
    (p : CMParams) {B3 x : ℝ} {b3 Zx W : ℝ → ℝ}
    (hB3 : 0 ≤ B3) (hb3 : |b3 x| ≤ B3) :
    -p.χ * b3 x * Zx x * W x ≤
      |p.χ| * B3 / 2 * ((Zx x) ^ 2 + (W x) ^ 2) := by
  have hcoef : 0 ≤ |p.χ| * B3 / 2 := by positivity
  have hyoung :
      2 * |Zx x| * |W x| ≤ (Zx x) ^ 2 + (W x) ^ 2 := by
    simpa [sq_abs] using two_mul_le_add_sq (|Zx x|) (|W x|)
  calc
    -p.χ * b3 x * Zx x * W x
        ≤ |-p.χ * b3 x * Zx x * W x| := le_abs_self _
    _ = |p.χ| * |b3 x| * |Zx x| * |W x| := by
      simp only [abs_neg, abs_mul]
    _ ≤ |p.χ| * B3 * |Zx x| * |W x| := by
      gcongr
    _ = (|p.χ| * B3 / 2) * (2 * |Zx x| * |W x|) := by ring
    _ ≤ (|p.χ| * B3 / 2) * ((Zx x) ^ 2 + (W x) ^ 2) :=
      mul_le_mul_of_nonneg_left hyoung hcoef

/-- Pointwise Young estimate for the corrected `J₄` density
`χ(η b₃-b₄) Z W`. -/
theorem paper5CorrectedJ4Density_le
    (p : CMParams) {η B3 B4 x : ℝ} {b3 b4 Z W : ℝ → ℝ}
    (hη : 0 ≤ η) (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4)
    (hb3 : |b3 x| ≤ B3) (hb4 : |b4 x| ≤ B4) :
    p.χ * (η * b3 x - b4 x) * Z x * W x ≤
      |p.χ| * (η * B3 + B4) / 2 *
        ((Z x) ^ 2 + (W x) ^ 2) := by
  have hcoeff_abs : |η * b3 x - b4 x| ≤ η * B3 + B4 := by
    calc
      |η * b3 x - b4 x| ≤ |η * b3 x| + |b4 x| := abs_sub _ _
      _ = η * |b3 x| + |b4 x| := by rw [abs_mul, abs_of_nonneg hη]
      _ ≤ η * B3 + B4 := add_le_add
        (mul_le_mul_of_nonneg_left hb3 hη) hb4
  have hcoef : 0 ≤ |p.χ| * (η * B3 + B4) / 2 := by positivity
  have hyoung :
      2 * |Z x| * |W x| ≤ (Z x) ^ 2 + (W x) ^ 2 := by
    simpa [sq_abs] using two_mul_le_add_sq (|Z x|) (|W x|)
  calc
    p.χ * (η * b3 x - b4 x) * Z x * W x
        ≤ |p.χ * (η * b3 x - b4 x) * Z x * W x| := le_abs_self _
    _ = |p.χ| * |η * b3 x - b4 x| * |Z x| * |W x| := by
      simp only [abs_mul]
    _ ≤ |p.χ| * (η * B3 + B4) * |Z x| * |W x| := by
      gcongr
    _ = (|p.χ| * (η * B3 + B4) / 2) *
          (2 * |Z x| * |W x|) := by ring
    _ ≤ (|p.χ| * (η * B3 + B4) / 2) *
          ((Z x) ^ 2 + (W x) ^ 2) :=
      mul_le_mul_of_nonneg_left hyoung hcoef

/-! ## The corrected pointwise remainder -/

/-- The four lower-order densities in the corrected weighted population
equation, before whole-line integration. -/
def paper5CorrectedRemainderDensity
    (p : CMParams) (η c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U W Wx V Vx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  -p.χ * paper5B1 p u v t x * Wx x * W x +
    paper5CorrectedJ2Coefficient p η c u v U t x * (W x) ^ 2 -
    p.χ * paper5B3 p U x * Vx x * W x +
    p.χ * (η * paper5B3 p U x - paper5B4 p U x) * V x * W x

/-- The exact scalar coefficient obtained after applying the four pointwise
Young estimates but before using the weighted resolver bounds. -/
def paper5RawW2Coefficient
    (p : CMParams) (η c M B1 B2 B3 B4 : ℝ) : ℝ :=
  η ^ 2 - c * η + 1 +
    |p.χ| * ((2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) + η * B1 + B2) +
    (1 / 2 : ℝ) * |p.χ| ^ 2 * B1 ^ 2 +
    |p.χ| * B3 / 2 + |p.χ| * (η * B3 + B4) / 2

/-- Corrected pointwise sum of `J₁,...,J₄`.  No sign of `χ` is used. -/
theorem paper5CorrectedRemainderDensity_le
    (p : CMParams) {η c M B1 B2 B3 B4 t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx V Vx : ℝ → ℝ}
    (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4)
    (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hv : v t x ∈ Set.Icc (0 : ℝ) (M ^ p.γ))
    (hb1 : |paper5B1 p u v t x| ≤ B1)
    (hb2 : |paper5B2 p u v U t x| ≤ B2)
    (hb3 : |paper5B3 p U x| ≤ B3)
    (hb4 : |paper5B4 p U x| ≤ B4) :
    paper5CorrectedRemainderDensity p η c u v U W Wx V Vx t x ≤
      (1 / 2 : ℝ) * (Wx x) ^ 2 +
        paper5RawW2Coefficient p η c M B1 B2 B3 B4 * (W x) ^ 2 +
        (|p.χ| * B3 / 2) * (Vx x) ^ 2 +
        (|p.χ| * (η * B3 + B4) / 2) * (V x) ^ 2 := by
  have h1 := paper5J1VariableDensity_le p
    (b1 := paper5B1 p u v t) (Wx := Wx) (W := W) hb1
  have h2 := paper5CorrectedJ2Coefficient_le p
    (η := η) (c := c) (M := M) (B1 := B1) (B2 := B2)
    hη hM hu hU hv hb1 hb2
  have h2W := mul_le_mul_of_nonneg_right h2 (sq_nonneg (W x))
  have h3 := paper5J3Density_le p
    (b3 := paper5B3 p U) (Zx := Vx) (W := W) hB3 hb3
  have h4 := paper5CorrectedJ4Density_le p
    (b3 := paper5B3 p U) (b4 := paper5B4 p U) (Z := V) (W := W)
    hη hB3 hB4 hb3 hb4
  unfold paper5CorrectedRemainderDensity paper5RawW2Coefficient
  linarith

/-! ## Whole-line integration of the corrected remainder -/

/-- Integrating the corrected pointwise remainder.  All four square-density
integrability hypotheses are explicit, so the Bochner integral cannot fall
back to Mathlib's zero value for a non-integrable function. -/
theorem paper5CorrectedRemainderIntegral_le
    (p : CMParams) {η c M B1 B2 B3 B4 t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx V Vx : ℝ → ℝ}
    (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4)
    (hu : ∀ x, u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hv : ∀ x, v t x ∈ Set.Icc (0 : ℝ) (M ^ p.γ))
    (hb1 : ∀ x, |paper5B1 p u v t x| ≤ B1)
    (hb2 : ∀ x, |paper5B2 p u v U t x| ≤ B2)
    (hb3 : ∀ x, |paper5B3 p U x| ≤ B3)
    (hb4 : ∀ x, |paper5B4 p U x| ≤ B4)
    (hdensity : Integrable
      (paper5CorrectedRemainderDensity p η c u v U W Wx V Vx t))
    (hWx2 : Integrable (fun x : ℝ => (Wx x) ^ 2))
    (hW2 : Integrable (fun x : ℝ => (W x) ^ 2))
    (hVx2 : Integrable (fun x : ℝ => (Vx x) ^ 2))
    (hV2 : Integrable (fun x : ℝ => (V x) ^ 2)) :
    (∫ x : ℝ, paper5CorrectedRemainderDensity
        p η c u v U W Wx V Vx t x) ≤
      (1 / 2 : ℝ) * (∫ x : ℝ, (Wx x) ^ 2) +
        paper5RawW2Coefficient p η c M B1 B2 B3 B4 *
          (∫ x : ℝ, (W x) ^ 2) +
        (|p.χ| * B3 / 2) * (∫ x : ℝ, (Vx x) ^ 2) +
        (|p.χ| * (η * B3 + B4) / 2) * (∫ x : ℝ, (V x) ^ 2) := by
  let rhs : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * (Wx x) ^ 2 +
      paper5RawW2Coefficient p η c M B1 B2 B3 B4 * (W x) ^ 2 +
      (|p.χ| * B3 / 2) * (Vx x) ^ 2 +
      (|p.χ| * (η * B3 + B4) / 2) * (V x) ^ 2
  have hrhs : Integrable rhs := by
    dsimp [rhs]
    exact (((hWx2.const_mul (1 / 2 : ℝ)).add
      (hW2.const_mul (paper5RawW2Coefficient p η c M B1 B2 B3 B4))).add
        (hVx2.const_mul (|p.χ| * B3 / 2))).add
          (hV2.const_mul (|p.χ| * (η * B3 + B4) / 2))
  have hi1 := hWx2.const_mul (1 / 2 : ℝ)
  have hi2 := hW2.const_mul
    (paper5RawW2Coefficient p η c M B1 B2 B3 B4)
  have hi3 := hVx2.const_mul (|p.χ| * B3 / 2)
  have hi4 := hV2.const_mul (|p.χ| * (η * B3 + B4) / 2)
  let f1 : ℝ → ℝ := fun x => (1 / 2 : ℝ) * (Wx x) ^ 2
  let f2 : ℝ → ℝ := fun x =>
    paper5RawW2Coefficient p η c M B1 B2 B3 B4 * (W x) ^ 2
  let f3 : ℝ → ℝ := fun x => (|p.χ| * B3 / 2) * (Vx x) ^ 2
  let f4 : ℝ → ℝ := fun x =>
    (|p.χ| * (η * B3 + B4) / 2) * (V x) ^ 2
  have hf1 : Integrable f1 := by simpa [f1] using hi1
  have hf2 : Integrable f2 := by simpa [f2] using hi2
  have hf3 : Integrable f3 := by simpa [f3] using hi3
  have hf4 : Integrable f4 := by simpa [f4] using hi4
  have hf12 : Integrable (fun x => f1 x + f2 x) := hf1.add hf2
  have hf123 : Integrable (fun x => f1 x + f2 x + f3 x) :=
    hf12.add hf3
  have hrhs_eq : rhs = ((f1 + f2) + f3) + f4 := by
    funext x
    rfl
  have hmono :
      (∫ x : ℝ, paper5CorrectedRemainderDensity
          p η c u v U W Wx V Vx t x) ≤ ∫ x : ℝ, rhs x :=
    integral_mono hdensity hrhs (fun x =>
      paper5CorrectedRemainderDensity_le p hη hM hB3 hB4
        (hu x) (hU x) (hv x) (hb1 x) (hb2 x) (hb3 x) (hb4 x))
  calc
    (∫ x : ℝ, paper5CorrectedRemainderDensity
        p η c u v U W Wx V Vx t x) ≤ ∫ x : ℝ, rhs x := hmono
    _ = (1 / 2 : ℝ) * (∫ x : ℝ, (Wx x) ^ 2) +
        paper5RawW2Coefficient p η c M B1 B2 B3 B4 *
          (∫ x : ℝ, (W x) ^ 2) +
        (|p.χ| * B3 / 2) * (∫ x : ℝ, (Vx x) ^ 2) +
        (|p.χ| * (η * B3 + B4) / 2) * (∫ x : ℝ, (V x) ^ 2) := by
      rw [hrhs_eq]
      simp only [Pi.add_apply]
      rw [integral_add (f := fun x => f1 x + f2 x + f3 x) (g := f4)
          hf123 hf4,
        integral_add (f := fun x => f1 x + f2 x) (g := f3) hf12 hf3,
        integral_add (f := f1) (g := f2) hf1 hf2]
      simp only [f1, f2, f3, f4,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul]

/-! ## Resolver substitution and diffusion absorption -/

/-- The constant moving-frame drift contributes zero on the whole line.  The
boundary condition is stated as decay of `W²`, which is exactly the boundary
term in integration by parts. -/
theorem wholeLine_weightedDriftIntegral_eq_zero
    (W Wx : ℝ → ℝ)
    (hW_deriv : ∀ x ∈ tsupport W, HasDerivAt W (Wx x) x)
    (hcross_int : Integrable (fun x : ℝ => Wx x * W x))
    (hdecay_bot : Tendsto (fun x : ℝ => W x * W x) atBot (𝓝 0))
    (hdecay_top : Tendsto (fun x : ℝ => W x * W x) atTop (𝓝 0)) :
    (∫ x : ℝ, Wx x * W x) = 0 := by
  have hcross_int' : Integrable (fun x : ℝ => W x * Wx x) := by
    simpa [mul_comm] using hcross_int
  have hIBP := ShenWork.PaperOne.wholeLine_chemotaxis_postIBP_with_derivatives
    W Wx W Wx hW_deriv hW_deriv hcross_int' hcross_int
      hdecay_bot hdecay_top
  have hsame : (∫ x : ℝ, W x * Wx x) = ∫ x : ℝ, Wx x * W x := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hsame] at hIBP
  linarith

/-- The scalar coefficient after substituting abstract weighted `L²` bounds
for the signal perturbation and its first derivative. -/
def paper5ResolvedW2Coefficient
    (p : CMParams) (η c M B1 B2 B3 B4 RV RVx : ℝ) : ℝ :=
  paper5RawW2Coefficient p η c M B1 B2 B3 B4 +
    (|p.χ| * B3 / 2) * RVx +
    (|p.χ| * (η * B3 + B4) / 2) * RV

/-- Corrected coefficient of `η` in (5.31), expressed using a common upper
bound `K` for `1 + RV` and `1 + RVx`. -/
def paper531CorrectedAFromBounds
    (p : CMParams) (B1 B3 K : ℝ) : ℝ :=
  |p.χ| * B1 + |p.χ| * B3 / 2 * K

/-- Corrected constant coefficient in (5.31).  In particular the `J₁`
contribution is `|χ|² B1² / 2`; the printed (5.33) loses one factor of
`B1`. -/
def paper531CorrectedBFromBounds
    (p : CMParams) (M B1 B2 B3 B4 K : ℝ) : ℝ :=
  |p.χ| * ((2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) + B2) +
    (1 / 2 : ℝ) * |p.χ| ^ 2 * B1 ^ 2 +
    |p.χ| * B3 / 2 * K + |p.χ| * B4 / 2 * K

/-- The `V` factor exported by Lemma 5.3. -/
def paper5WeightedResolverVFactor
    (p : CMParams) (M η : ℝ) : ℝ :=
  p.γ ^ 2 * M ^ (2 * (p.γ - 1)) / (1 - η) ^ 2

/-- The `Vₓ` factor exported by Lemma 5.3. -/
def paper5WeightedResolverVxFactor
    (p : CMParams) (M η : ℝ) : ℝ :=
  p.γ ^ 2 * M ^ (2 * (p.γ - 1)) / (1 - η ^ 2)

/-- A common upper bound for `1 + RV` and `1 + RVx` throughout the
admissible weight interval.  The factor `M^(2(γ-1))`, absent from the
printed (5.29)--(5.30), is required by Lemma 5.3. -/
def paper5CorrectedResolverCapFactor
    (p : CMParams) (M : ℝ) : ℝ :=
  let x := |p.χ| ^ paper5Sigma
  1 + p.γ ^ 2 * M ^ (2 * (p.γ - 1)) * (1 + x) ^ 2 / x ^ 2

/-- Uniform resolver-factor bounds below the paper's weight cap, away from
the trivial `χ = 0` branch. -/
theorem paper5WeightedResolverFactors_le_cap
    (p : CMParams) {M η : ℝ}
    (hχ : p.χ ≠ 0) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hηcap : η < stabilityWeightCap p) :
    1 + paper5WeightedResolverVFactor p M η ≤
        paper5CorrectedResolverCapFactor p M ∧
      1 + paper5WeightedResolverVxFactor p M η ≤
        paper5CorrectedResolverCapFactor p M := by
  let x : ℝ := |p.χ| ^ paper5Sigma
  have hx : 0 < x :=
    Real.rpow_pos_of_pos (abs_pos.mpr hχ) paper5Sigma
  have h1x : 0 < 1 + x := by linarith
  have hcap : η < 1 / (1 + x) := by
    simpa [stabilityWeightCap, paper5Sigma, x] using hηcap
  have hcap_le_one : 1 / (1 + x) ≤ 1 := by
    rw [div_le_one h1x]
    linarith
  have hηone : η < 1 := lt_of_lt_of_le hcap hcap_le_one
  have hden : 0 < 1 - η := sub_pos.mpr hηone
  have hfrac : x / (1 + x) < 1 - η := by
    have hid : 1 - 1 / (1 + x) = x / (1 + x) := by
      field_simp [ne_of_gt h1x]
      ring
    linarith
  have hfrac0 : 0 ≤ x / (1 + x) :=
    div_nonneg hx.le h1x.le
  have hsq : (x / (1 + x)) ^ 2 ≤ (1 - η) ^ 2 :=
    (sq_le_sq₀ hfrac0 hden.le).2 hfrac.le
  have hinv : 1 / (1 - η) ^ 2 ≤ 1 / (x / (1 + x)) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos (div_pos hx h1x)) hsq
  have hinv_rewrite :
      1 / (x / (1 + x)) ^ 2 = (1 + x) ^ 2 / x ^ 2 := by
    field_simp [ne_of_gt hx, ne_of_gt h1x]
  let N : ℝ := p.γ ^ 2 * M ^ (2 * (p.γ - 1))
  have hN : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg hM _)
  have hV :
      1 + paper5WeightedResolverVFactor p M η ≤
        paper5CorrectedResolverCapFactor p M := by
    unfold paper5WeightedResolverVFactor paper5CorrectedResolverCapFactor
    dsimp only
    change 1 + N / (1 - η) ^ 2 ≤
      1 + N * (1 + x) ^ 2 / x ^ 2
    have hmul := mul_le_mul_of_nonneg_left hinv hN
    calc
      1 + N / (1 - η) ^ 2 = 1 + N * (1 / (1 - η) ^ 2) := by ring
      _ ≤ 1 + N * (1 / (x / (1 + x)) ^ 2) :=
        by simpa [add_comm] using add_le_add_left hmul 1
      _ = 1 + N * (1 + x) ^ 2 / x ^ 2 := by
        rw [hinv_rewrite]
        ring
  have hden_compare : (1 - η) ^ 2 ≤ 1 - η ^ 2 := by
    nlinarith [mul_nonneg hη (sub_nonneg.mpr hηone.le)]
  have hinv_x : 1 / (1 - η ^ 2) ≤ 1 / (1 - η) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hden) hden_compare
  have hVx_to_V :
      1 + paper5WeightedResolverVxFactor p M η ≤
        1 + paper5WeightedResolverVFactor p M η := by
    unfold paper5WeightedResolverVxFactor paper5WeightedResolverVFactor
    change 1 + N / (1 - η ^ 2) ≤ 1 + N / (1 - η) ^ 2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hinv_x hN) 1)
  exact ⟨hV, hVx_to_V.trans hV⟩

/-- Exact algebraic passage from the resolved coefficient to the corrected
quadratic form. -/
theorem paper5ResolvedW2Coefficient_le_corrected531
    (p : CMParams) {η c M B1 B2 B3 B4 RV RVx K : ℝ}
    (hη : 0 ≤ η) (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4)
    (hRV : 1 + RV ≤ K) (hRVx : 1 + RVx ≤ K) :
    paper5ResolvedW2Coefficient p η c M B1 B2 B3 B4 RV RVx ≤
      paper531Quadratic c
        (paper531CorrectedAFromBounds p B1 B3 K)
        (paper531CorrectedBFromBounds p M B1 B2 B3 B4 K) η := by
  have hk3 : 0 ≤ |p.χ| * B3 / 2 := by positivity
  have hk4 : 0 ≤ |p.χ| * (η * B3 + B4) / 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hRVx hk3
  have h4 := mul_le_mul_of_nonneg_left hRV hk4
  unfold paper5ResolvedW2Coefficient paper5RawW2Coefficient
    paper531CorrectedAFromBounds paper531CorrectedBFromBounds
    paper531Quadratic
  nlinarith

/-- Substitute the two signal `L²` inequalities into the integrated
remainder estimate. -/
theorem paper5CorrectedRemainderIntegral_le_of_resolver
    (p : CMParams) {η c M B1 B2 B3 B4 RV RVx IW IWx IV IVx IR : ℝ}
    (hη : 0 ≤ η) (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4)
    (hraw : IR ≤
      (1 / 2 : ℝ) * IWx +
        paper5RawW2Coefficient p η c M B1 B2 B3 B4 * IW +
        (|p.χ| * B3 / 2) * IVx +
        (|p.χ| * (η * B3 + B4) / 2) * IV)
    (hVx : IVx ≤ RVx * IW) (hV : IV ≤ RV * IW) :
    IR ≤ (1 / 2 : ℝ) * IWx +
      paper5ResolvedW2Coefficient p η c M B1 B2 B3 B4 RV RVx * IW := by
  have hk3 : 0 ≤ |p.χ| * B3 / 2 := by positivity
  have hk4 : 0 ≤ |p.χ| * (η * B3 + B4) / 2 := by positivity
  have hVx' := mul_le_mul_of_nonneg_left hVx hk3
  have hV' := mul_le_mul_of_nonneg_left hV hk4
  unfold paper5ResolvedW2Coefficient
  nlinarith

/-- After whole-line diffusion integration by parts, half of the gradient
dissipation absorbs `J₁`; discarding the remaining nonpositive half leaves
the resolved scalar coefficient. -/
theorem paper5CorrectedEnergyRHS_le_resolved
    (p : CMParams) {η c M B1 B2 B3 B4 RV RVx IW IWx IR : ℝ}
    (hIWx : 0 ≤ IWx)
    (hrem : IR ≤ (1 / 2 : ℝ) * IWx +
      paper5ResolvedW2Coefficient p η c M B1 B2 B3 B4 RV RVx * IW) :
    -IWx + IR ≤
      paper5ResolvedW2Coefficient p η c M B1 B2 B3 B4 RV RVx * IW := by
  linarith

section Theorem12WeightedEnergyAxiomAudit
#print axioms paper5J1VariableDensity_le
#print axioms paper5CorrectedJ2Coefficient_le
#print axioms paper5J3Density_le
#print axioms paper5CorrectedJ4Density_le
#print axioms paper5CorrectedRemainderDensity_le
#print axioms paper5CorrectedRemainderIntegral_le
#print axioms wholeLine_weightedDriftIntegral_eq_zero
#print axioms paper5CorrectedRemainderIntegral_le_of_resolver
#print axioms paper5CorrectedEnergyRHS_le_resolved
#print axioms paper5ResolvedW2Coefficient_le_corrected531
#print axioms paper5WeightedResolverFactors_le_cap
end Theorem12WeightedEnergyAxiomAudit

end ShenWork.Paper1
