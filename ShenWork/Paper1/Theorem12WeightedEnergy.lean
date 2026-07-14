import ShenWork.Paper1.Theorem12MeanCoefficients
import ShenWork.Paper1.Theorem12WeightedResolver
import ShenWork.Paper1.Theorem12CoordinateAudit
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

/-! ## Exact corrected weighted perturbation equation -/

/-- The material derivative in the frame `z = x - c t`, written as the
fixed-space laboratory time derivative plus the transport term. -/
def paper5CoMovingMaterialTime
    (c : ℝ) (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun s => u s (x + c * t)) t +
    c * deriv (coMovingPath c u t) x

/-- A classical laboratory solution satisfies the population equation in the
co-moving frame when its time derivative is interpreted as the material
derivative above.  This step uses only the already-proved fixed-translation
invariance of `IsClassicalSolution`; the diagonal time chain rule is stated
separately below. -/
theorem paper5CoMovingMaterialPDE_of_classical
    (p : CMParams) {T c t x : ℝ} {u v : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T) :
    paper5CoMovingMaterialTime c u t x =
      iteratedDeriv 2 (coMovingPath c u t) x +
        c * deriv (coMovingPath c u t) x -
        p.χ * deriv
          (fun y => (coMovingPath c u t y) ^ p.m *
            deriv (coMovingPath c v t) y) x +
        coMovingPath c u t x *
          (1 - (coMovingPath c u t x) ^ p.α) := by
  have hpde := (hsol.shift_space (c * t)).pde_u t x ht0 htT
  unfold paper5CoMovingMaterialTime coMovingPath
  linarith

/-- Joint differentiability turns the material field into the genuine time
derivative of the moving-frame slice.  This is the precise extra regularity
missing from the minimal `IsClassicalSolution` record. -/
theorem paper5CoMovingPath_hasDerivAt_of_joint
    {c t x : ℝ} {u : ℝ → ℝ → ℝ}
    (hjoint : HasFDerivAt
      (fun q : ℝ × ℝ => u q.1 q.2)
      (deriv (fun s => u s (x + c * t)) t •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (u t) (x + c * t) •
          ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, x + c * t)) :
    HasDerivAt (fun s => coMovingPath c u s x)
      (paper5CoMovingMaterialTime c u t x) t := by
  let A := deriv (fun s => u s (x + c * t)) t
  let B := deriv (u t) (x + c * t)
  have hc :
      HasDerivAt (fun s : ℝ => ((s, x + c * s) : ℝ × ℝ)) (1, c) t := by
    have h₁ : HasDerivAt (fun s : ℝ => s) 1 t := by
      simpa using hasDerivAt_id t
    have h₂ : HasDerivAt (fun s : ℝ => x + c * s) c t := by
      simpa [add_comm] using (hasDerivAt_id t).const_mul c |>.const_add x
    exact h₁.prodMk h₂
  have hcomp := hjoint.comp_hasDerivAt
    (f := fun s : ℝ => ((s, x + c * s) : ℝ × ℝ)) (x := t) hc
  have hspace_shift :
      deriv (coMovingPath c u t) x = B := by
    exact deriv_comp_add_const (u t) (c * t) x
  change HasDerivAt (fun s => u s (x + c * s))
    (deriv (fun s => u s (x + c * t)) t +
      c * deriv (fun z => u t (z + c * t)) x) t
  have hspace_shift' :
      deriv (fun z => u t (z + c * t)) x = B := by
    simpa [coMovingPath] using hspace_shift
  rw [hspace_shift']
  convert hcomp using 1
  simp [B, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  ring

/-- Product differentiation plus the elliptic equation realizes the
chemotactic flux derivative.  The `C¹/C²` assumptions are explicit because
the minimal `IsClassicalSolution` structure records only first spatial
differentiability. -/
theorem paper5FluxDerivative_realization
    (p : CMParams) {f g : ℝ → ℝ} {x : ℝ}
    (hf1 : ContDiff ℝ 1 f) (hg2 : ContDiff ℝ 2 g)
    (hell : iteratedDeriv 2 g x - g x + (f x) ^ p.γ = 0) :
    deriv (fun y => (f y) ^ p.m * deriv g y) x =
      p.m * (f x) ^ (p.m - 1) * deriv f x * deriv g x +
        (f x) ^ p.m * (g x - (f x) ^ p.γ) := by
  have hf_diff : Differentiable ℝ f :=
    (contDiff_one_iff_deriv.mp hf1).1
  have hg2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) g := by
    simpa using hg2
  have hgd1 : ContDiff ℝ 1 (deriv g) :=
    (contDiff_succ_iff_deriv.mp hg2').2.2
  have hgd_diff : Differentiable ℝ (deriv g) :=
    (contDiff_one_iff_deriv.mp hgd1).1
  have hpow :
      HasDerivAt (fun y => (f y) ^ p.m)
        (deriv f x * p.m * (f x) ^ (p.m - 1)) x :=
    (hf_diff x).hasDerivAt.rpow_const (Or.inr p.hm)
  have hprod := hpow.mul (hgd_diff x).hasDerivAt
  have hiter : iteratedDeriv 2 g x = deriv (deriv g) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  have hsecond : deriv (deriv g) x = g x - (f x) ^ p.γ := by
    rw [hiter] at hell
    linarith
  have hfun :
      (fun y => (f y) ^ p.m * deriv g y) =
        (fun y => (f y) ^ p.m) * deriv g := by
    funext y
    rfl
  rw [hfun, hprod.deriv, hsecond]
  ring

/-- The dynamic co-moving flux realization supplied by classical elliptic
regularity at a fixed positive time. -/
theorem paper5CoMovingFluxDerivative_realization_of_classical
    (p : CMParams) {T c t x : ℝ} {u v : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t)) :
    deriv
        (fun y => (coMovingPath c u t y) ^ p.m *
          deriv (coMovingPath c v t) y) x =
      p.m * (coMovingPath c u t x) ^ (p.m - 1) *
          deriv (coMovingPath c u t) x * deriv (coMovingPath c v t) x +
        (coMovingPath c u t x) ^ p.m *
          (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ) := by
  apply paper5FluxDerivative_realization p hu1 hv2
  exact (hsol.shift_space (c * t)).pde_v t x ht0 htT

/-- The traveling-wave flux realization supplied by profile `C¹/C²`
regularity. -/
theorem paper5WaveFluxDerivative_realization
    (p : CMParams) {c x : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    deriv (fun y => (U y) ^ p.m * deriv V y) x =
      p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
        (U x) ^ p.m * (V x - (U x) ^ p.γ) :=
  paper5FluxDerivative_realization p hU1 hV2 (hTW.ode_V x)

/-- Exponentially weighted population perturbation in an already co-moving
spatial coordinate. -/
def paper5WeightedPopulation
    (η : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (η * x) * (u t x - U x)

/-- Its formal first spatial derivative, written using the derivatives of the
unweighted fields. -/
def paper5WeightedPopulationX
    (η : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  η * paper5WeightedPopulation η u U t x +
    Real.exp (η * x) * (deriv (u t) x - deriv U x)

/-- Its formal second spatial derivative. -/
def paper5WeightedPopulationXX
    (η : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  η ^ 2 * paper5WeightedPopulation η u U t x +
    2 * η * Real.exp (η * x) * (deriv (u t) x - deriv U x) +
    Real.exp (η * x) *
      (iteratedDeriv 2 (u t) x - iteratedDeriv 2 U x)

/-- Exponentially weighted signal perturbation. -/
def paper5WeightedSignal
    (η : ℝ) (v : ℝ → ℝ → ℝ) (V : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (η * x) * (v t x - V x)

/-- Its formal first spatial derivative. -/
def paper5WeightedSignalX
    (η : ℝ) (v : ℝ → ℝ → ℝ) (V : ℝ → ℝ) (t x : ℝ) : ℝ :=
  η * paper5WeightedSignal η v V t x +
    Real.exp (η * x) * (deriv (v t) x - deriv V x)

/-- Weighted material-time density for a supplied co-moving time field
`ut`. -/
def paper5WeightedPopulationT
    (η : ℝ) (ut : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (η * x) * ut t x

/-- The formal weighted first population derivative is the actual spatial
derivative. -/
theorem paper5WeightedPopulation_space_hasDerivAt
    {η t x : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu : DifferentiableAt ℝ (u t) x) (hU : DifferentiableAt ℝ U x) :
    HasDerivAt (paper5WeightedPopulation η u U t)
      (paper5WeightedPopulationX η u U t x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (η * y))
      (η * Real.exp (η * x)) x := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using
      (((hasDerivAt_id x).const_mul η).exp)
  have hsub := hu.hasDerivAt.sub hU.hasDerivAt
  have hprod := hexp.mul hsub
  change HasDerivAt (fun y => Real.exp (η * y) * (u t y - U y))
    (η * (Real.exp (η * x) * (u t x - U x)) +
      Real.exp (η * x) * (deriv (u t) x - deriv U x)) x
  convert hprod using 1 <;> simp [Pi.mul_apply, Pi.sub_apply] <;> ring

/-- The formal weighted signal derivative is the actual spatial derivative. -/
theorem paper5WeightedSignal_space_hasDerivAt
    {η t x : ℝ} {v : ℝ → ℝ → ℝ} {V : ℝ → ℝ}
    (hv : DifferentiableAt ℝ (v t) x) (hV : DifferentiableAt ℝ V x) :
    HasDerivAt (paper5WeightedSignal η v V t)
      (paper5WeightedSignalX η v V t x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (η * y))
      (η * Real.exp (η * x)) x := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using
      (((hasDerivAt_id x).const_mul η).exp)
  have hsub := hv.hasDerivAt.sub hV.hasDerivAt
  have hprod := hexp.mul hsub
  change HasDerivAt (fun y => Real.exp (η * y) * (v t y - V y))
    (η * (Real.exp (η * x) * (v t x - V x)) +
      Real.exp (η * x) * (deriv (v t) x - deriv V x)) x
  convert hprod using 1 <;> simp [Pi.mul_apply, Pi.sub_apply] <;> ring

/-- The formal weighted second population derivative is the derivative of the
formal first derivative under explicit `C²` regularity. -/
theorem paper5WeightedPopulationX_space_hasDerivAt
    {η t x : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U) :
    HasDerivAt (paper5WeightedPopulationX η u U t)
      (paper5WeightedPopulationXX η u U t x) x := by
  have hu1 : ContDiff ℝ 1 (u t) := hu2.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 U := hU2.of_le (by norm_num)
  have hW := paper5WeightedPopulation_space_hasDerivAt
    (η := η) (t := t) (x := x)
    ((contDiff_one_iff_deriv.mp hu1).1 x)
    ((contDiff_one_iff_deriv.mp hU1).1 x)
  have hu2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (u t) := by
    simpa using hu2
  have hU2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) U := by
    simpa using hU2
  have hud1 : ContDiff ℝ 1 (deriv (u t)) :=
    (contDiff_succ_iff_deriv.mp hu2').2.2
  have hUd1 : ContDiff ℝ 1 (deriv U) :=
    (contDiff_succ_iff_deriv.mp hU2').2.2
  have hdsub :=
    ((contDiff_one_iff_deriv.mp hud1).1 x).hasDerivAt.sub
      ((contDiff_one_iff_deriv.mp hUd1).1 x).hasDerivAt
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (η * y))
      (η * Real.exp (η * x)) x := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using
      (((hasDerivAt_id x).const_mul η).exp)
  have hsum := hW.const_mul η |>.add (hexp.mul hdsub)
  have huiter : iteratedDeriv 2 (u t) x = deriv (deriv (u t)) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  have hUiter : iteratedDeriv 2 U x = deriv (deriv U) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  convert hsum using 1
  · simp [paper5WeightedPopulationXX, paper5WeightedPopulationX,
      paper5WeightedPopulation, huiter, hUiter]
    ring

/-- Whole-line diffusion IBP for the actual weighted population perturbation,
with its formal first and second derivative fields now realized. -/
theorem paper5WeightedPopulation_diffusion_ibp
    {η t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U)
    (hlhs : Integrable (fun x =>
      paper5WeightedPopulation η u U t x *
        paper5WeightedPopulationXX η u U t x))
    (hgrad : Integrable (fun x =>
      paper5WeightedPopulationX η u U t x *
        paper5WeightedPopulationX η u U t x))
    (hdecay_bot : Tendsto (fun x =>
      paper5WeightedPopulation η u U t x *
        paper5WeightedPopulationX η u U t x) atBot (𝓝 0))
    (hdecay_top : Tendsto (fun x =>
      paper5WeightedPopulation η u U t x *
        paper5WeightedPopulationX η u U t x) atTop (𝓝 0)) :
    (∫ x, paper5WeightedPopulation η u U t x *
        paper5WeightedPopulationXX η u U t x) =
      -∫ x, (paper5WeightedPopulationX η u U t x) ^ 2 := by
  have hu1 : ContDiff ℝ 1 (u t) := hu2.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 U := hU2.of_le (by norm_num)
  have hfirst : ∀ x,
      HasDerivAt (paper5WeightedPopulation η u U t)
        (paper5WeightedPopulationX η u U t x) x := by
    intro x
    exact paper5WeightedPopulation_space_hasDerivAt
      ((contDiff_one_iff_deriv.mp hu1).1 x)
      ((contDiff_one_iff_deriv.mp hU1).1 x)
  have hsecond : ∀ x,
      HasDerivAt (paper5WeightedPopulationX η u U t)
        (paper5WeightedPopulationXX η u U t x) x := by
    intro x
    exact paper5WeightedPopulationX_space_hasDerivAt hu2 hU2
  have hIBP :=
    _root_.ShenWork.PaperOne.wholeLine_diffusion_ibp_decay_with_derivatives
      (paper5WeightedPopulation η u U t)
      (paper5WeightedPopulationX η u U t)
      (paper5WeightedPopulationXX η u U t)
      (fun x _ => hfirst x) (fun x _ => hsecond x)
      hlhs hgrad hdecay_bot hdecay_top
  simpa [pow_two] using hIBP

/-- Nonnegativity of the realized weighted gradient energy. -/
theorem paper5WeightedPopulation_gradientIntegral_nonneg
    {η t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} :
    0 ≤ ∫ x, (paper5WeightedPopulationX η u U t x) ^ 2 :=
  integral_nonneg fun _ => sq_nonneg _

/-- The formal weighted material-time density is the genuine time derivative
of the weighted moving-frame perturbation under joint differentiability. -/
theorem paper5WeightedPopulation_time_hasDerivAt_of_joint
    {η c t x : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hjoint : HasFDerivAt
      (fun q : ℝ × ℝ => u q.1 q.2)
      (deriv (fun s => u s (x + c * t)) t •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (u t) (x + c * t) •
          ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, x + c * t)) :
    HasDerivAt
      (fun s => paper5WeightedPopulation η (coMovingPath c u) U s x)
      (paper5WeightedPopulationT η (paper5CoMovingMaterialTime c u) t x) t := by
  have hmove := paper5CoMovingPath_hasDerivAt_of_joint
    (c := c) (t := t) (x := x) hjoint
  have hsub := hmove.sub_const (U x)
  have hmul := hsub.const_mul (Real.exp (η * x))
  simpa [paper5WeightedPopulation, paper5WeightedPopulationT] using hmul

/-- The corrected pointwise version of (5.19).  The input `hPDE` is the
population equation after the change to the moving coordinate; no spatial or
time chain rule is hidden in this algebraic theorem. -/
theorem paper5WeightedPerturbationEquation_corrected
    (p : CMParams) {η c t x : ℝ}
    {u v ut : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hu : 0 ≤ u t x)
    (hPDE : ut t x =
      iteratedDeriv 2 (u t) x + c * deriv (u t) x -
        p.χ * deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x +
        u t x * (1 - (u t x) ^ p.α))
    (hflux_u :
      deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x =
        p.m * (u t x) ^ (p.m - 1) * deriv (u t) x * deriv (v t) x +
          (u t x) ^ p.m * (v t x - (u t x) ^ p.γ))
    (hflux_U :
      deriv (fun y => (U y) ^ p.m * deriv V y) x =
        p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
          (U x) ^ p.m * (V x - (U x) ^ p.γ)) :
    paper5WeightedPopulationT η ut t x =
      paper5WeightedPopulationXX η u U t x +
        (c - 2 * η) * paper5WeightedPopulationX η u U t x +
        paper5CorrectedJ2Coefficient p η c u v U t x *
          paper5WeightedPopulation η u U t x -
        p.χ * paper5B1 p u v t x *
          paper5WeightedPopulationX η u U t x -
        p.χ * paper5B3 p U x * paper5WeightedSignalX η v V t x +
        p.χ * (η * paper5B3 p U x - paper5B4 p U x) *
          paper5WeightedSignal η v V t x := by
  have hU0 : 0 ≤ U x := (hTW.U_pos x).le
  have hpow_u : u t x * (u t x) ^ p.α = (u t x) ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hu zero_le_one (zero_le_one.trans p.hα),
      Real.rpow_one]
  have hpow_U : U x * (U x) ^ p.α = (U x) ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hU0 zero_le_one (zero_le_one.trans p.hα),
      Real.rpow_one]
  have hreact :
      u t x * (1 - (u t x) ^ p.α) -
          U x * (1 - (U x) ^ p.α) =
        (1 - paper5A (1 + p.α) u U t x) * (u t x - U x) := by
    have hA := paper5A_mul_sub (1 + p.α) u U t x
    rw [show u t x * (1 - (u t x) ^ p.α) =
        u t x - u t x * (u t x) ^ p.α by ring,
      show U x * (1 - (U x) ^ p.α) =
        U x - U x * (U x) ^ p.α by ring,
      hpow_u, hpow_U]
    ring_nf at hA ⊢
    linarith
  have hflux :=
    paper5ChemFluxDifference_expansion_corrected p u v U V t x hu hU0
  have hflux_diff :
      deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x -
          deriv (fun y => (U y) ^ p.m * deriv V y) x =
        paper5B1 p u v t x * (deriv (u t) x - deriv U x) +
          (paper5B2 p u v U t x +
              paper5CorrectedChemZeroCoefficient p u v U t x) *
            (u t x - U x) +
          paper5B3 p U x * (deriv (v t) x - deriv V x) +
          paper5B4 p U x * (v t x - V x) := by
    rw [hflux_u, hflux_U]
    simpa only [paper5CorrectedChemZeroCoefficient, add_sub_assoc] using hflux
  have hode := hTW.ode_U x
  have hdiff :
      ut t x =
        (iteratedDeriv 2 (u t) x - iteratedDeriv 2 U x) +
          c * (deriv (u t) x - deriv U x) -
          p.χ * (paper5B1 p u v t x *
              (deriv (u t) x - deriv U x) +
            (paper5B2 p u v U t x +
                paper5CorrectedChemZeroCoefficient p u v U t x) *
              (u t x - U x) +
            paper5B3 p U x * (deriv (v t) x - deriv V x) +
            paper5B4 p U x * (v t x - V x)) +
          (1 - paper5A (1 + p.α) u U t x) * (u t x - U x) := by
    rw [hPDE]
    linear_combination hode + hreact - p.χ * hflux_diff
  unfold paper5WeightedPopulationT paper5WeightedPopulationXX
    paper5WeightedPopulationX paper5WeightedPopulation
    paper5WeightedSignalX paper5WeightedSignal
    paper5CorrectedJ2Coefficient
  rw [hdiff]
  ring

/-- The corrected pointwise weighted equation with all PDE and flux-expansion
inputs produced from a classical solution and explicit spatial regularity. -/
theorem paper5WeightedPerturbationEquation_corrected_of_classical
    (p : CMParams) {T η c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    paper5WeightedPopulationT η (paper5CoMovingMaterialTime c u) t x =
      paper5WeightedPopulationXX η (coMovingPath c u) U t x +
        (c - 2 * η) *
          paper5WeightedPopulationX η (coMovingPath c u) U t x +
        paper5CorrectedJ2Coefficient p η c
            (coMovingPath c u) (coMovingPath c v) U t x *
          paper5WeightedPopulation η (coMovingPath c u) U t x -
        p.χ * paper5B1 p (coMovingPath c u) (coMovingPath c v) t x *
          paper5WeightedPopulationX η (coMovingPath c u) U t x -
        p.χ * paper5B3 p U x *
          paper5WeightedSignalX η (coMovingPath c v) V t x +
        p.χ * (η * paper5B3 p U x - paper5B4 p U x) *
          paper5WeightedSignal η (coMovingPath c v) V t x := by
  apply paper5WeightedPerturbationEquation_corrected p hTW hu
  · exact paper5CoMovingMaterialPDE_of_classical p hsol ht0 htT
  · exact paper5CoMovingFluxDerivative_realization_of_classical
      p hsol ht0 htT hu1 hv2
  · exact paper5WaveFluxDerivative_realization p hTW hU1 hV2

/-! ## From the pointwise equation to the scalar energy inequality -/

/-- Multiplying the corrected pointwise equation by `W` produces exactly the
diffusion, drift, and corrected remainder densities used below. -/
theorem paper5CorrectedWeightedDensity_identity
    (p : CMParams) {η c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Wxx Z Zx WT : ℝ → ℝ}
    (heq : WT x =
      Wxx x + (c - 2 * η) * Wx x +
        paper5CorrectedJ2Coefficient p η c u v U t x * W x -
        p.χ * paper5B1 p u v t x * Wx x -
        p.χ * paper5B3 p U x * Zx x +
        p.χ * (η * paper5B3 p U x - paper5B4 p U x) * Z x) :
    W x * WT x =
      W x * Wxx x + (c - 2 * η) * (Wx x * W x) +
        paper5CorrectedRemainderDensity
          p η c u v U W Wx Z Zx t x := by
  rw [heq]
  unfold paper5CorrectedRemainderDensity
  ring

/-- Classical-solution specialization of the multiplied density identity. -/
theorem paper5CorrectedWeightedDensity_identity_of_classical
    (p : CMParams) {T η c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    ∀ x,
      paper5WeightedPopulation η (coMovingPath c u) U t x *
          paper5WeightedPopulationT η
            (paper5CoMovingMaterialTime c u) t x =
        paper5WeightedPopulation η (coMovingPath c u) U t x *
            paper5WeightedPopulationXX η (coMovingPath c u) U t x +
          (c - 2 * η) *
            (paper5WeightedPopulationX η (coMovingPath c u) U t x *
              paper5WeightedPopulation η (coMovingPath c u) U t x) +
          paper5CorrectedRemainderDensity p η c
            (coMovingPath c u) (coMovingPath c v) U
            (paper5WeightedPopulation η (coMovingPath c u) U t)
            (paper5WeightedPopulationX η (coMovingPath c u) U t)
            (paper5WeightedSignal η (coMovingPath c v) V t)
            (paper5WeightedSignalX η (coMovingPath c v) V t) t x := by
  intro x
  apply paper5CorrectedWeightedDensity_identity p
  exact paper5WeightedPerturbationEquation_corrected_of_classical
    p hsol ht0 htT hTW (hu x) hu1 hv2 hU1 hV2

/-- Integrate the corrected weighted equation after multiplication by the
population perturbation.  Every integrability input is explicit, so no
Bochner integral can collapse to zero by convention. -/
theorem paper5CorrectedWeightedTimeIntegral_eq
    (p : CMParams) {η c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Wxx Z Zx WT : ℝ → ℝ}
    (hpoint : ∀ x,
      W x * WT x =
        W x * Wxx x + (c - 2 * η) * (Wx x * W x) +
          paper5CorrectedRemainderDensity
            p η c u v U W Wx Z Zx t x)
    (hdiff : Integrable (fun x => W x * Wxx x))
    (hdrift : Integrable (fun x => Wx x * W x))
    (hrem : Integrable
      (paper5CorrectedRemainderDensity p η c u v U W Wx Z Zx t)) :
    (∫ x, W x * WT x) =
      (∫ x, W x * Wxx x) +
        (c - 2 * η) * (∫ x, Wx x * W x) +
        ∫ x, paper5CorrectedRemainderDensity
          p η c u v U W Wx Z Zx t x := by
  calc
    (∫ x, W x * WT x) =
        ∫ x, (W x * Wxx x + (c - 2 * η) * (Wx x * W x)) +
          paper5CorrectedRemainderDensity
            p η c u v U W Wx Z Zx t x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (∫ x, W x * Wxx x) +
          (c - 2 * η) * (∫ x, Wx x * W x) +
          ∫ x, paper5CorrectedRemainderDensity
            p η c u v U W Wx Z Zx t x := by
      have hdrift' : Integrable
          (fun x => (c - 2 * η) * (Wx x * W x)) :=
        hdrift.const_mul (c - 2 * η)
      rw [← MeasureTheory.integral_const_mul,
        ← integral_add hdiff hdrift']
      simpa only [Pi.add_apply] using
        (integral_add (hdiff.add hdrift') hrem)

/-- The corrected scalar energy inequality after diffusion IBP, drift
cancellation, and resolver substitution.  This is the analytic shape of
(5.31), with the corrected coefficient. -/
theorem paper5CorrectedHalfEnergy_deriv_le_of_remainder
    {c η C t : ℝ}
    {E W Wx Wxx WT : ℝ → ℝ} {IR : ℝ}
    (htime : deriv E t = ∫ x, W x * WT x)
    (hpde : (∫ x, W x * WT x) =
      (∫ x, W x * Wxx x) +
        (c - 2 * η) * (∫ x, Wx x * W x) + IR)
    (hdiff : (∫ x, W x * Wxx x) = -∫ x, (Wx x) ^ 2)
    (hdrift : (∫ x, Wx x * W x) = 0)
    (hrem : IR ≤
      (1 / 2 : ℝ) * (∫ x, (Wx x) ^ 2) +
        C * (∫ x, (W x) ^ 2))
    (hgrad_nonneg : 0 ≤ ∫ x, (Wx x) ^ 2) :
    deriv E t ≤ C * ∫ x, (W x) ^ 2 := by
  rw [htime, hpde, hdiff, hdrift]
  have hhalf :
      -(∫ x, (Wx x) ^ 2) +
          ((1 / 2 : ℝ) * (∫ x, (Wx x) ^ 2) +
            C * (∫ x, (W x) ^ 2)) ≤
        C * (∫ x, (W x) ^ 2) := by
    linarith
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

/-- Drift cancellation for the realized weighted population derivative. -/
theorem paper5WeightedPopulation_driftIntegral_eq_zero
    {η t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu1 : ContDiff ℝ 1 (u t)) (hU1 : ContDiff ℝ 1 U)
    (hcross : Integrable (fun x =>
      paper5WeightedPopulationX η u U t x *
        paper5WeightedPopulation η u U t x))
    (hdecay_bot : Tendsto (fun x =>
      paper5WeightedPopulation η u U t x *
        paper5WeightedPopulation η u U t x) atBot (𝓝 0))
    (hdecay_top : Tendsto (fun x =>
      paper5WeightedPopulation η u U t x *
        paper5WeightedPopulation η u U t x) atTop (𝓝 0)) :
    (∫ x, paper5WeightedPopulationX η u U t x *
        paper5WeightedPopulation η u U t x) = 0 := by
  apply wholeLine_weightedDriftIntegral_eq_zero
    (paper5WeightedPopulation η u U t)
    (paper5WeightedPopulationX η u U t)
  · intro x _
    exact paper5WeightedPopulation_space_hasDerivAt
      ((contDiff_one_iff_deriv.mp hu1).1 x)
      ((contDiff_one_iff_deriv.mp hU1).1 x)
  · exact hcross
  · exact hdecay_bot
  · exact hdecay_top

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

/-- Complete corrected (5.31) scalar closure: time Leibniz, the integrated
pointwise equation, diffusion IBP, drift cancellation, the two resolver
estimates, and the corrected coefficient grouping. -/
theorem paper5CorrectedHalfEnergy_deriv_le_corrected531
    (p : CMParams) {η c M B1 B2 B3 B4 RV RVx K t IR : ℝ}
    {E W Wx Wxx WT : ℝ → ℝ}
    (hη : 0 ≤ η) (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4)
    (htime : deriv E t = ∫ x, W x * WT x)
    (hpde : (∫ x, W x * WT x) =
      (∫ x, W x * Wxx x) +
        (c - 2 * η) * (∫ x, Wx x * W x) + IR)
    (hdiff : (∫ x, W x * Wxx x) = -∫ x, (Wx x) ^ 2)
    (hdrift : (∫ x, Wx x * W x) = 0)
    (hraw : IR ≤
      (1 / 2 : ℝ) * (∫ x, (Wx x) ^ 2) +
        paper5RawW2Coefficient p η c M B1 B2 B3 B4 *
          (∫ x, (W x) ^ 2) +
        (|p.χ| * B3 / 2) * RVx * (∫ x, (W x) ^ 2) +
        (|p.χ| * (η * B3 + B4) / 2) * RV *
          (∫ x, (W x) ^ 2))
    (hgrad : 0 ≤ ∫ x, (Wx x) ^ 2)
    (hW : 0 ≤ ∫ x, (W x) ^ 2)
    (hRV : 1 + RV ≤ K) (hRVx : 1 + RVx ≤ K) :
    deriv E t ≤
      paper531Quadratic c
        (paper531CorrectedAFromBounds p B1 B3 K)
        (paper531CorrectedBFromBounds p M B1 B2 B3 B4 K) η *
        ∫ x, (W x) ^ 2 := by
  have hresolved : IR ≤
      (1 / 2 : ℝ) * (∫ x, (Wx x) ^ 2) +
        paper5ResolvedW2Coefficient p η c M B1 B2 B3 B4 RV RVx *
          (∫ x, (W x) ^ 2) := by
    unfold paper5ResolvedW2Coefficient
    linarith
  have henergy := paper5CorrectedHalfEnergy_deriv_le_of_remainder
    (c := c) (η := η)
    (C := paper5ResolvedW2Coefficient p η c M B1 B2 B3 B4 RV RVx)
    htime hpde hdiff hdrift hresolved hgrad
  have hcoef := paper5ResolvedW2Coefficient_le_corrected531 p
    (η := η) (c := c) (M := M) (B1 := B1) (B2 := B2)
    (B3 := B3) (B4 := B4) (RV := RV) (RVx := RVx) (K := K)
    hη hB3 hB4 hRV hRVx
  exact henergy.trans (mul_le_mul_of_nonneg_right hcoef hW)

section Theorem12WeightedEnergyAxiomAudit
#print axioms paper5CoMovingMaterialPDE_of_classical
#print axioms paper5CoMovingPath_hasDerivAt_of_joint
#print axioms paper5WeightedPopulation_time_hasDerivAt_of_joint
#print axioms paper5FluxDerivative_realization
#print axioms paper5WeightedPopulation_space_hasDerivAt
#print axioms paper5WeightedSignal_space_hasDerivAt
#print axioms paper5WeightedPopulationX_space_hasDerivAt
#print axioms paper5WeightedPopulation_diffusion_ibp
#print axioms paper5WeightedPopulation_gradientIntegral_nonneg
#print axioms paper5WeightedPerturbationEquation_corrected
#print axioms paper5WeightedPerturbationEquation_corrected_of_classical
#print axioms paper5CorrectedWeightedDensity_identity_of_classical
#print axioms paper5CorrectedWeightedTimeIntegral_eq
#print axioms paper5CorrectedHalfEnergy_deriv_le_of_remainder
#print axioms paper5J1VariableDensity_le
#print axioms paper5CorrectedJ2Coefficient_le
#print axioms paper5J3Density_le
#print axioms paper5CorrectedJ4Density_le
#print axioms paper5CorrectedRemainderDensity_le
#print axioms paper5CorrectedRemainderIntegral_le
#print axioms wholeLine_weightedDriftIntegral_eq_zero
#print axioms paper5WeightedPopulation_driftIntegral_eq_zero
#print axioms paper5CorrectedRemainderIntegral_le_of_resolver
#print axioms paper5CorrectedEnergyRHS_le_resolved
#print axioms paper5ResolvedW2Coefficient_le_corrected531
#print axioms paper5WeightedResolverFactors_le_cap
#print axioms paper5CorrectedHalfEnergy_deriv_le_corrected531
end Theorem12WeightedEnergyAxiomAudit

end ShenWork.Paper1
