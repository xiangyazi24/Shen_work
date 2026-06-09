/-
# The full periodised Neumann image heat kernel on `[0,1]` and its cosine-spectral form

This file introduces the **full** method-of-images Neumann heat kernel on the unit
interval — the one summed over *all* reflections —

  `K_full t x y = ∑_{k ∈ ℤ} (G_t(x − y + 2k) + G_t(x + y + 2k))`,

(`G_t` = `heatKernel t`), and the associated propagator

  `intervalFullSemigroupOperator t f x = ∫_{[0,1]} K_full t x y * f y`.

The classical fact (Jacobi theta / Poisson summation) is that `K_full` — unlike the
two-term `normalizedZerothReflectionKernel` analysed in
`IntervalSemigroupSpectralForm.lean` — is *exactly* the Neumann heat kernel, so its
propagator equals the cosine eigenfunction series
`unitIntervalCosineHeatValue t (cosineCoeffs f) x`.

## What is proved clean here (no `sorry`/`admit`/axiom)

The analytic core is the **period-`2` shifted Gaussian Poisson summation identity**

  `∑_{k∈ℤ} G_t(z + 2k) = (1/2) ∑_{m∈ℤ} exp(-t (mπ)²) · exp(I·mπ·z)`        (★)

(`gaussianLatticeSum_poisson_complex`), proved from Mathlib's
`Complex.tsum_exp_neg_quadratic` by matching the quadratic form `A = 1/(πt)`,
`B = -z/(2πt)`, collapsing the prefactor `(4πt)^{-1/2}·√(πt) = 1/2`.  This is the
period-`2` analogue of the prior agent's `heatKernel_lattice_poisson` (the `z = 0`,
period-`1` special case), and is the exact statement that turns the periodised image
Gaussian into the cosine spectral kernel.  Its real-cosine corollary
`gaussianLatticeSum_poisson` follows by taking real parts.

## Precise reduction of the kernel↔spectral identity (Theorem 3)

`intervalFullSemigroupOperator_eq_cosineHeatValue` (Theorem 3) and the pointwise
kernel identity `intervalNeumannFullKernel_eq_cosineKernel` are reduced to **named
hypotheses** capturing exactly the residual bookkeeping (no Mathlib gap):

* `LatticeGaussianSummable` — summability of the shifted lattice Gaussian
  `k ↦ G_t(z+2k)` (Gaussian tail; `Real.summable_exp_neg_*`-type, repo bookkeeping);
* `FullKernelIntegralInterchange` — `MeasureTheory.integral_tsum` interchange of
  `∑_{m∈ℤ}` with `∫_{[0,1]}` (dominated by summable `exp(-t(mπ)²)·‖f‖∞`) **plus** the
  `ℤ → ℕ` even-reflection reindexing folding `∑_{m∈ℤ}` onto the Neumann `∑_{n≥0}`
  (weight `n=0 ↦ 1`, `n≥1 ↦ 2`), the same reindexing as
  `unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff` in `CosineParsevalBridge`.

The deep analytic input `(★)` — the genuinely Poisson-summation part — is proved clean.
-/

import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.IntervalSemigroupSpectralForm
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.PDE.IntervalDomainRegularityBootstrap
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.SmoothSeries

open MeasureTheory

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open scoped Real
open ShenWork.IntervalDomain
open Complex (I)

/-! ## The full periodised Neumann image kernel -/

/-- The **full** periodised method-of-images Neumann heat kernel on `[0,1]`:
the integer lattice sum (period `2`) of the direct and reflected Gaussian images.
Unlike `normalizedZerothReflectionKernel`, this keeps **all** reflections, and is the
genuine Neumann heat kernel of `[0,1]`. -/
def intervalNeumannFullKernel (t x y : ℝ) : ℝ :=
  ∑' k : ℤ, (heatKernel t (x - y + 2 * k) + heatKernel t (x + y + 2 * k))

/-- The full periodised-image Neumann heat propagator on `[0,1]`. -/
def intervalFullSemigroupOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1

/-- The cosine coefficients used on the spectral side: the normalized Neumann cosine
coefficients (zeroth mode unscaled, positive modes carrying the factor `2`). -/
def cosineCoeffs (f : ℝ → ℝ) : ℕ → ℝ :=
  fun n => ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
    (fun x => (f x : ℂ)) n

/-! ## The analytic core: period-`2` shifted Gaussian Poisson summation -/

/-- Single-variable periodised Gaussian along the period-`2` lattice. -/
def gaussianLatticeSum (t z : ℝ) : ℝ :=
  ∑' k : ℤ, heatKernel t (z + 2 * k)

/-- **(★) Period-`2` shifted Gaussian Poisson summation, complex form.**

`∑_{k∈ℤ} G_t(z + 2k) = (1/2) ∑_{m∈ℤ} exp(-t (mπ)²) · exp(I · mπ · z)`.

The genuine Jacobi-theta transformation converting the periodised image Gaussian into
the cosine spectral kernel; the period-`2` analogue of `heatKernel_lattice_poisson`.
Proved from Mathlib's `Complex.tsum_exp_neg_quadratic` with `A = 1/(πt)`,
`B = -z/(2πt)`, the prefactor collapsing as `(4πt)^{-1/2}·√(πt) = 1/2`. -/
theorem gaussianLatticeSum_poisson_complex (t : ℝ) (ht : 0 < t) (z : ℝ) :
    (gaussianLatticeSum t z : ℂ) =
      (1 / 2 : ℂ) * ∑' m : ℤ, Complex.exp (-t * ((m : ℂ) * Real.pi) ^ 2) *
        Complex.exp (I * ((m : ℂ) * Real.pi) * z) := by
  set a : ℂ := ((1 / (Real.pi * t) : ℝ) : ℂ) with ha_def
  set b : ℂ := ((-z / (2 * Real.pi * t) : ℝ) : ℂ) with hb_def
  have hpit : 0 < Real.pi * t := by positivity
  have hpit_ne : (Real.pi * t : ℝ) ≠ 0 := ne_of_gt hpit
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht
  have ha_re : 0 < a.re := by rw [ha_def, Complex.ofReal_re]; positivity
  -- Mathlib Poisson summation (shifted Gaussian, integer lattice).
  have hpoisson := Complex.tsum_exp_neg_quadratic ha_re b
  -- (1) Rewrite LHS as a constant times the Poisson left-hand sum.
  have hLHS : (gaussianLatticeSum t z : ℂ) =
      ((1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-z ^ 2 / (4 * t)) : ℝ) : ℂ) *
        ∑' k : ℤ, Complex.exp
          (-Real.pi * a * (k : ℂ) ^ 2 + 2 * Real.pi * b * (k : ℂ)) := by
    rw [gaussianLatticeSum, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    have hterm : ((heatKernel t (z + 2 * (k : ℝ)) : ℝ) : ℂ) =
        ((1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-z ^ 2 / (4 * t)) : ℝ) : ℂ) *
          Complex.exp (-Real.pi * a * (k : ℂ) ^ 2 + 2 * Real.pi * b * (k : ℂ)) := by
      have hexp : ((Real.exp (-(z + 2 * (k : ℝ)) ^ 2 / (4 * t)) : ℝ) : ℂ)
          = ((Real.exp (-z ^ 2 / (4 * t)) : ℝ) : ℂ) *
              Complex.exp (-Real.pi * a * (k : ℂ) ^ 2 + 2 * Real.pi * b * (k : ℂ)) := by
        rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        rw [ha_def, hb_def]
        push_cast
        field_simp
        ring
      simp only [heatKernel]
      rw [Complex.ofReal_mul, Complex.ofReal_mul, hexp]
      ring
    rw [hterm]
  -- (2) Rewrite the Poisson dual side termwise.
  have hdual : ∀ m : ℤ,
      Complex.exp (-Real.pi / a * ((m : ℂ) + I * b) ^ 2) =
        (Real.exp (z ^ 2 / (4 * t)) : ℂ) *
          (Complex.exp (-t * ((m : ℂ) * Real.pi) ^ 2) *
            Complex.exp (I * ((m : ℂ) * Real.pi) * z)) := by
    intro m
    simp only [ha_def, hb_def]
    rw [Complex.ofReal_exp]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hane : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact Real.pi_ne_zero
    have htne : ((t : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact ne_of_gt ht
    have hI2 : (I : ℂ) ^ 2 = -1 := Complex.I_sq
    push_cast
    field_simp
    ring_nf
    simp only [hI2]
    ring
  -- (3) Collapse the prefactor `(4πt)^{-1/2} · (1/a^{1/2}) · exp(z²/4t) · exp(-z²/4t) = 1/2`.
  have hapow : a ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi * t)⁻¹ : ℝ) : ℂ) := by
    rw [ha_def, show (1 / (Real.pi * t) : ℝ) = (Real.pi * t)⁻¹ by ring]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow]
  have hpre : ((1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-z ^ 2 / (4 * t)) : ℝ) : ℂ) *
      ((1 : ℂ) / a ^ (1 / 2 : ℂ)) * (Real.exp (z ^ 2 / (4 * t)) : ℂ) = (1 / 2 : ℂ) := by
    rw [hapow]
    have hsqrtpt : Real.sqrt (Real.pi * t)⁻¹ = (Real.sqrt (Real.pi * t))⁻¹ := by
      rw [Real.sqrt_inv]
    have hcollapse : (1 / Real.sqrt (4 * Real.pi * t)) *
        (1 / Real.sqrt (Real.pi * t)⁻¹) = (1 / 2 : ℝ) := by
      rw [hsqrtpt]
      rw [show (4 * Real.pi * t : ℝ) = 4 * (Real.pi * t) by ring]
      rw [Real.sqrt_mul (by norm_num) (Real.pi * t)]
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]
      have hsqrtpt_pos : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr hpit
      field_simp
    rw [show ((1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-z ^ 2 / (4 * t)) : ℝ) : ℂ) *
        ((1 : ℂ) / ((Real.sqrt (Real.pi * t)⁻¹ : ℝ) : ℂ)) * (Real.exp (z ^ 2 / (4 * t)) : ℂ)
        = (((1 / Real.sqrt (4 * Real.pi * t)) * (1 / Real.sqrt (Real.pi * t)⁻¹) : ℝ) : ℂ) *
          ((Real.exp (-z ^ 2 / (4 * t)) * Real.exp (z ^ 2 / (4 * t)) : ℝ) : ℂ) from by
      push_cast; ring]
    rw [hcollapse]
    rw [← Real.exp_add]
    rw [show (-z ^ 2 / (4 * t) + z ^ 2 / (4 * t) : ℝ) = 0 by ring, Real.exp_zero]
    norm_num
  -- (4) Assemble.
  rw [hLHS, hpoisson]
  rw [tsum_congr hdual]
  rw [tsum_mul_left, ← mul_assoc, ← mul_assoc]
  rw [hpre]

/-- **(★) real-cosine corollary.** Taking real parts of the complex Poisson identity:

  `∑_{k∈ℤ} G_t(z + 2k) = (1/2) ∑_{m∈ℤ} exp(-t (mπ)²) cos(mπ z)`. -/
theorem gaussianLatticeSum_poisson (t : ℝ) (ht : 0 < t) (z : ℝ) :
    gaussianLatticeSum t z =
      (1 / 2) * ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        Real.cos ((m : ℝ) * Real.pi * z) := by
  have hc := gaussianLatticeSum_poisson_complex t ht z
  -- complex summability of the spectral series (norm = exp(-t(mπ)²), summable)
  have hsummC : Summable (fun m : ℤ => Complex.exp (-t * ((m : ℂ) * Real.pi) ^ 2) *
      Complex.exp (I * ((m : ℂ) * Real.pi) * z)) := by
    have hnorm : ∀ m : ℤ, ‖Complex.exp (-t * ((m : ℂ) * Real.pi) ^ 2) *
        Complex.exp (I * ((m : ℂ) * Real.pi) * z)‖
        = Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) := by
      intro m
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
      have h1 : (-t * ((m : ℂ) * Real.pi) ^ 2).re
          = -t * ((m : ℝ) * Real.pi) ^ 2 := by
        have : (-t * ((m : ℂ) * Real.pi) ^ 2)
            = ((-t * ((m : ℝ) * Real.pi) ^ 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      have h2 : (I * ((m : ℂ) * Real.pi) * z).re = 0 := by
        have : (I * ((m : ℂ) * Real.pi) * z)
            = ((m : ℝ) * Real.pi * z : ℝ) * I := by push_cast; ring
        rw [this, Complex.re_ofReal_mul, Complex.I_re, mul_zero]
      rw [h1, h2, Real.exp_zero, mul_one]
    apply Summable.of_norm
    have hsumReal : Summable (fun m : ℤ =>
        Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2)) := by
      set c : ℝ := t * Real.pi ^ 2 with hc_def
      have hc_pos : 0 < c := by rw [hc_def]; positivity
      have heq : (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2))
          = (fun m : ℤ => Real.exp (-c * ((m : ℝ)) ^ 2)) := by
        funext m; congr 1; rw [hc_def]; ring
      rw [heq]
      -- summability over ℤ via ℕ ⊕ (negated ℕ), each `exp(-c n²)` summable since n ≤ n²
      apply Summable.of_nat_of_neg
      · -- n ≥ 0 branch
        have hle : ∀ i : ℕ, (i : ℝ) ≤ (i : ℝ) ^ 2 := by
          intro i
          have : i ≤ i ^ 2 := by nlinarith [Nat.zero_le i]
          calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
            _ ≤ ((i ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
            _ = (i : ℝ) ^ 2 := by push_cast; ring
        have := Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
          (f := fun n : ℕ => (n : ℝ) ^ 2) hle
        simpa using this
      · -- negated branch: exp(-c (-n)²) = exp(-c n²)
        have hle : ∀ i : ℕ, (i : ℝ) ≤ (i : ℝ) ^ 2 := by
          intro i
          have : i ≤ i ^ 2 := by nlinarith [Nat.zero_le i]
          calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
            _ ≤ ((i ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
            _ = (i : ℝ) ^ 2 := by push_cast; ring
        have := Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
          (f := fun n : ℕ => (n : ℝ) ^ 2) hle
        have heq2 : (fun n : ℕ => Real.exp (-c * (((-(n : ℤ) : ℤ) : ℝ)) ^ 2))
            = (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2)) := by
          funext n; congr 1; push_cast; ring
        rw [heq2]
        simpa using this
    exact hsumReal.congr (fun m => (hnorm m).symm)
  -- termwise real part:  (cexp(-t(mπ)²)·cexp(I mπ z)).re = exp(-t(mπ)²)·cos(mπ z)
  have htermeq : ∀ m : ℤ,
      (Complex.exp (-t * ((m : ℂ) * Real.pi) ^ 2) *
          Complex.exp (I * ((m : ℂ) * Real.pi) * z)).re
      = Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          Real.cos ((m : ℝ) * Real.pi * z) := by
    intro m
    have hcexp1 : Complex.exp (-t * ((m : ℂ) * Real.pi) ^ 2)
        = ((Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast; ring
    have hcexp2 : Complex.exp (I * ((m : ℂ) * Real.pi) * z)
        = Complex.exp (((m : ℝ) * Real.pi * z : ℝ) * I) := by
      congr 1; push_cast; ring
    rw [hcexp1, hcexp2, Complex.exp_ofReal_mul_I, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sin_ofReal_re]
    ring
  -- take real parts of the complex Poisson identity
  have hre := congrArg Complex.re hc
  rw [Complex.ofReal_re] at hre
  have hhalf_re : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have hhalf_im : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [hre, Complex.mul_re, hhalf_re, hhalf_im, zero_mul, sub_zero,
    Complex.re_tsum hsummC, tsum_congr htermeq]

/-! ## The pointwise kernel↔spectral identity (reduced to a summability hypothesis) -/

/-- Summability of the period-`2` shifted lattice Gaussian (Gaussian tail). -/
def LatticeGaussianSummable (t z : ℝ) : Prop :=
  Summable (fun k : ℤ => heatKernel t (z + 2 * k))

/-- **Lattice Gaussian summability (proved, not assumed).**  For `t > 0` the
period-`2` shifted lattice Gaussian `k ↦ heatKernel t (z + 2k)` is summable.

The Gaussian tail dominates the linear shift: completing the square gives, for
*every* real lattice argument `a`, the bound `a² ≥ 2k² − z²` (from the perfect
square `2(k ± z)² ≥ 0`), so each term is bounded by
`exp(z²/(4t)) · exp(−k²/(2t))`, and `∑ₖ exp(−k²/(2t))` converges (`k ≤ k²`,
`Real.summable_exp_nat_mul_of_ge`).  This discharges the `LatticeGaussianSummable`
hypotheses appearing in the kernel↔spectral identities below. -/
theorem latticeGaussianSummable {t : ℝ} (ht : 0 < t) (z : ℝ) :
    LatticeGaussianSummable t z := by
  unfold LatticeGaussianSummable
  -- `heatKernel t (z+2k) = (1/√(4πt)) · exp(−(z+2k)²/(4t))`; the constant factors out.
  simp only [heatKernel]
  apply Summable.mul_left
  -- `Summable (fun k : ℤ ↦ exp(−(z+2k)²/(4t)))`.
  set c : ℝ := -(1 / (2 * t)) with hc_def
  have hc : c < 0 := by
    rw [hc_def]
    have hpos : 0 < 1 / (2 * t) := by positivity
    linarith
  have ht4 : (0 : ℝ) < 4 * t := by linarith
  -- the dominating one-sided Gaussian `∑ₙ exp(c · n²)` converges (`n ≤ n²`).
  have hbase : Summable (fun n : ℕ => Real.exp (c * (n : ℝ) ^ 2)) := by
    refine Real.summable_exp_nat_mul_of_ge hc (f := fun n : ℕ => (n : ℝ) ^ 2) (fun i => ?_)
    have hnat : i ≤ i ^ 2 := by nlinarith [Nat.zero_le i]
    calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
      _ ≤ ((i ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (i : ℝ) ^ 2 := by push_cast; ring
  -- core comparison: any one-sided lattice with `a n` satisfying `a² ≥ 2n²−z²` is summable.
  have core : ∀ a : ℕ → ℝ, (∀ n : ℕ, 2 * (n : ℝ) ^ 2 - z ^ 2 ≤ (a n) ^ 2) →
      Summable (fun n : ℕ => Real.exp (-(a n) ^ 2 / (4 * t))) := by
    intro a ha
    refine (hbase.mul_left (Real.exp (z ^ 2 / (4 * t)))).of_nonneg_of_le
      (fun n => Real.exp_nonneg _) (fun n => ?_)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc -(a n) ^ 2 / (4 * t)
        ≤ (z ^ 2 - 2 * (n : ℝ) ^ 2) / (4 * t) :=
          (div_le_div_iff_of_pos_right ht4).mpr (by linarith [ha n])
      _ = z ^ 2 / (4 * t) + c * (n : ℝ) ^ 2 := by
          rw [hc_def]; field_simp; ring
  -- split `ℤ = ℕ ⊕ (−ℕ)`; each side is a one-sided lattice handled by `core`.
  apply Summable.of_nat_of_neg
  · refine core _ (fun n => ?_)
    push_cast; nlinarith [sq_nonneg ((n : ℝ) + z)]
  · refine core _ (fun n => ?_)
    push_cast; nlinarith [sq_nonneg ((n : ℝ) - z)]

/-- **Exp-form lattice summability.**  The bare shifted Gaussian
`k ↦ exp(−(z+2k)²/(4s))` is summable for `s > 0`; this is `heatKernel s`
stripped of its `(4πs)^{-1/2}` prefactor, recovered by `Summable.mul_left`. -/
theorem latticeExpSummable {s : ℝ} (hs : 0 < s) (z : ℝ) :
    Summable (fun k : ℤ => Real.exp (-(z + 2 * (k : ℝ)) ^ 2 / (4 * s))) := by
  have hne : Real.sqrt (4 * Real.pi * s) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  refine ((latticeGaussianSummable hs z).mul_left
    (Real.sqrt (4 * Real.pi * s))).congr (fun k => ?_)
  unfold heatKernel
  rw [← mul_assoc, mul_one_div, div_self hne, one_mul]

/-- The pointwise heat-gradient bound constant `(1/(2t))·(4πt)^{-1/2}·√(8t)`. -/
def heatGradPointwiseBound (t : ℝ) : ℝ :=
  (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) * Real.sqrt (4 * (2 * t))

/-- **Pointwise Gaussian-gradient bound.**  For `t > 0`, the heat-kernel spatial
derivative obeys `|deriv (heatKernel t) x| ≤ heatGradPointwiseBound t · exp(−x²/(8t))`
— the linear `x` prefactor of `deriv` is absorbed into the *half-rate* Gaussian by
the elementary bound `|x|·exp(−x²/(8t)) ≤ √(8t)` (`Real.abs_mulExpNegMulSq_le` with
`ε = 1/(8t)`).  The surviving half-rate Gaussian `exp(−x²/(8t))` is what makes the
derivative lattice summable (and uniformly so on bounded sets). -/
theorem abs_deriv_heatKernel_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |deriv (fun u : ℝ => heatKernel t u) x|
      ≤ heatGradPointwiseBound t * Real.exp (-x ^ 2 / (4 * (2 * t))) := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  -- elementary Gaussian-gradient bound  |x|·exp(−x²/(4·2t)) ≤ √(4·2t)
  have hw : |x| * Real.exp (-x ^ 2 / (4 * (2 * t))) ≤ Real.sqrt (4 * (2 * t)) := by
    have hε : (0 : ℝ) < 1 / (4 * (2 * t)) := by positivity
    have hb := Real.abs_mulExpNegMulSq_le hε (x := x)
    rw [Real.mulExpNegSq_apply] at hb
    rw [show -(1 / (4 * (2 * t)) * x * x) = -x ^ 2 / (4 * (2 * t)) by ring,
        abs_mul, abs_of_pos (Real.exp_pos _)] at hb
    have hsqrt : (Real.sqrt (1 / (4 * (2 * t))))⁻¹ = Real.sqrt (4 * (2 * t)) := by
      rw [one_div, Real.sqrt_inv, inv_inv]
    rwa [hsqrt] at hb
  -- split the heat-rate Gaussian into two half-rate Gaussians
  have hsplit : Real.exp (-x ^ 2 / (4 * t))
      = Real.exp (-x ^ 2 / (4 * (2 * t))) * Real.exp (-x ^ 2 / (4 * (2 * t))) := by
    rw [← Real.exp_add]; congr 1
    field_simp
    ring
  have hfac : 0 ≤ (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) := by positivity
  have hcore : |x| * Real.exp (-x ^ 2 / (4 * t))
      ≤ Real.sqrt (4 * (2 * t)) * Real.exp (-x ^ 2 / (4 * (2 * t))) := by
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
  rw [deriv_heatKernel ht, abs_mul, abs_neg, abs_div, abs_of_pos h2t,
    abs_of_nonneg (heatKernel_nonneg ht _)]
  unfold heatKernel heatGradPointwiseBound
  calc |x| / (2 * t) * (1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t)))
      = (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))
          * (|x| * Real.exp (-x ^ 2 / (4 * t))) := by ring
    _ ≤ (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))
          * (Real.sqrt (4 * (2 * t)) * Real.exp (-x ^ 2 / (4 * (2 * t)))) :=
        mul_le_mul_of_nonneg_left hcore hfac
    _ = (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) * Real.sqrt (4 * (2 * t))
          * Real.exp (-x ^ 2 / (4 * (2 * t))) := by ring

/-- **Gradient lattice summability (proved).**  For `t > 0` the derivative
lattice `k ↦ deriv (heatKernel t) (z + 2k) = −((z+2k)/(2t))·heatKernel t (z+2k)`
is summable, dominated termwise by `heatGradPointwiseBound t · exp(−(z+2k)²/(8t))`
(`abs_deriv_heatKernel_le`), whose lattice sum is `latticeExpSummable (2t)`. -/
theorem latticeGaussianGradSummable {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Summable (fun k : ℤ => deriv (fun w : ℝ => heatKernel t w) (z + 2 * (k : ℝ))) := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  apply Summable.of_abs
  exact ((latticeExpSummable h2t z).mul_left (heatGradPointwiseBound t)).of_nonneg_of_le
    (fun k => abs_nonneg _) (fun k => abs_deriv_heatKernel_le ht _)

/-- **Termwise differentiation of the lattice heat sum.**  For `t > 0` and any
shift `b`, the lattice `w ↦ ∑ₖ heatKernel t (w + b + 2k)` is differentiable in
`w`, with derivative the termwise lattice sum of the heat-kernel derivatives.

Proof via `hasDerivAt_tsum_of_isPreconnected` on the open interval `(x−1, x+1)`:
the per-term uniform derivative bound is `abs_deriv_heatKernel_le` followed by the
Young inequality `(A+B)² ≥ ½A² − B²` (with `A = x+b+2k`, `B = w − x`, `|B| < 1`),
giving a `k`-summable majorant `latticeExpSummable (4t)`. -/
theorem hasDerivAt_heatKernel_lattice_tsum {t : ℝ} (ht : 0 < t) (b x : ℝ) :
    HasDerivAt (fun w : ℝ => ∑' k : ℤ, heatKernel t (w + b + 2 * (k : ℝ)))
      (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + b + 2 * (k : ℝ))) x := by
  have h4t : (0 : ℝ) < 4 * t := by linarith
  -- the uniform summable majorant on `(x−1, x+1)`
  set u : ℤ → ℝ := fun k =>
    heatGradPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
      * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) with hu_def
  have hu : Summable u :=
    (latticeExpSummable h4t (x + b)).mul_left
      (heatGradPointwiseBound t * Real.exp (1 / (4 * (2 * t))))
  -- per-term derivative (chain rule through the affine shift `w ↦ w+b+2k`)
  have hg : ∀ (k : ℤ) (w : ℝ), w ∈ Set.Ioo (x - 1) (x + 1) →
      HasDerivAt (fun w : ℝ => heatKernel t (w + b + 2 * (k : ℝ)))
        (deriv (fun u : ℝ => heatKernel t u) (w + b + 2 * (k : ℝ))) w := by
    intro k w _
    have hinner : HasDerivAt (fun w : ℝ => w + b + 2 * (k : ℝ)) 1 w := by
      simpa using ((hasDerivAt_id w).add_const b).add_const (2 * (k : ℝ))
    have hcomp := (heatKernel_hasDerivAt ht (w + b + 2 * (k : ℝ))).comp w hinner
    rw [deriv_heatKernel ht]
    simpa using hcomp
  -- uniform derivative bound: pointwise bound + Young inequality
  have hg' : ∀ (k : ℤ) (w : ℝ), w ∈ Set.Ioo (x - 1) (x + 1) →
      ‖deriv (fun u : ℝ => heatKernel t u) (w + b + 2 * (k : ℝ))‖ ≤ u k := by
    intro k w hw
    rw [Real.norm_eq_abs]
    refine (abs_deriv_heatKernel_le ht (w + b + 2 * (k : ℝ))).trans ?_
    rw [hu_def]
    have hP : (1 / 2) * (x + b + 2 * (k : ℝ)) ^ 2 - 1 ≤ (w + b + 2 * (k : ℝ)) ^ 2 := by
      have hB : (w - x) ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
      nlinarith [sq_nonneg (2 * w - x + b + 2 * (k : ℝ)), hB]
    have hexp : Real.exp (-(w + b + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ Real.exp (1 / (4 * (2 * t)))
          * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htne : t ≠ 0 := ne_of_gt ht
      have e1 : -(w + b + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t))
          = (-2 * (w + b + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by
        field_simp
        ring
      have e2 : 1 / (4 * (2 * t)) + -(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))
          = (2 - (x + b + 2 * (k : ℝ)) ^ 2) / (4 * (4 * t)) := by
        field_simp
        ring
      rw [e1, e2]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * (4 * t))).mpr
      nlinarith [hP]
    calc heatGradPointwiseBound t
            * Real.exp (-(w + b + 2 * (k : ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ heatGradPointwiseBound t * (Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t)))) :=
          mul_le_mul_of_nonneg_left hexp (by unfold heatGradPointwiseBound; positivity)
      _ = heatGradPointwiseBound t * Real.exp (1 / (4 * (2 * t)))
            * Real.exp (-(x + b + 2 * (k : ℝ)) ^ 2 / (4 * (4 * t))) := by ring
  have hg0 : Summable (fun k : ℤ => heatKernel t (x + b + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (x + b)
  exact hasDerivAt_tsum_of_isPreconnected (u := u) (t := Set.Ioo (x - 1) (x + 1))
    (g := fun (k : ℤ) (w : ℝ) => heatKernel t (w + b + 2 * (k : ℝ)))
    (g' := fun (k : ℤ) (w : ℝ) => deriv (fun u : ℝ => heatKernel t u) (w + b + 2 * (k : ℝ)))
    hu isOpen_Ioo (convex_Ioo _ _).isPreconnected hg hg'
    (y₀ := x) (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hg0
    (y := x) (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)

/-- **`∂ₓ` of the full periodised Neumann kernel.**  For `t > 0`, the full kernel
`K_full t · y = ∑ₖ (heat(·−y+2k) + heat(·+y+2k))` is differentiable in its first
argument, with derivative the sum of the two termwise-differentiated lattice
series.  Both the value split (`Summable.tsum_add` on the kernel) and the two
lattice derivatives come from `hasDerivAt_heatKernel_lattice_tsum` (with shifts
`b = −y` and `b = y`). -/
theorem hasDerivAt_intervalNeumannFullKernel_fst {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun x : ℝ => intervalNeumannFullKernel t x y)
      ((∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ)))) x := by
  -- reflected family (shift `b = −y`)
  have hL : HasDerivAt (fun w : ℝ => ∑' k : ℤ, heatKernel t (w - y + 2 * (k : ℝ)))
      (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ))) x := by
    simpa only [sub_eq_add_neg] using hasDerivAt_heatKernel_lattice_tsum ht (-y) x
  -- direct family (shift `b = y`)
  have hR : HasDerivAt (fun w : ℝ => ∑' k : ℤ, heatKernel t (w + y + 2 * (k : ℝ)))
      (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ))) x :=
    hasDerivAt_heatKernel_lattice_tsum ht y x
  -- split the kernel's single tsum into the two lattice sums
  have hfun : (fun w : ℝ => intervalNeumannFullKernel t w y)
      = fun w => (∑' k : ℤ, heatKernel t (w - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, heatKernel t (w + y + 2 * (k : ℝ))) := by
    funext w
    rw [intervalNeumannFullKernel]
    exact Summable.tsum_add (latticeGaussianSummable ht (w - y)) (latticeGaussianSummable ht (w + y))
  rw [hfun]
  exact hL.add hR

/-- **Pointwise integrand bound for the full-kernel gradient `L¹` estimate.**
At every `y`, the `x`-derivative of the full Neumann kernel is dominated by the
termwise-absolute lattice sum:

  `|∂ₓ K_full(t,x,y)| ≤ ∑ₖ (|∂heat(x−y+2k)| + |∂heat(x+y+2k)|)`.

Triangle inequality on the two-tsum derivative (`hasDerivAt_intervalNeumannFull
Kernel_fst`) via `abs_add` and `norm_tsum_le_tsum_norm` (norm-summability from
`latticeGaussianGradSummable` + `summable_abs_iff`), recombined by
`Summable.tsum_add`.  Integrating this in `y` over `[0,1]` and applying the
tiling identity `tsum_cell_heatGrad_abs_integral_eq` yields the `(1/√π)t^(−1/2)`
gradient `L¹` bound. -/
theorem abs_deriv_intervalNeumannFullKernel_fst_le {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |deriv (fun x : ℝ => intervalNeumannFullKernel t x y) x|
      ≤ ∑' k : ℤ, (|deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
          + |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) := by
  rw [(hasDerivAt_intervalNeumannFullKernel_fst ht x y).deriv]
  have hsumA : Summable (fun k : ℤ => |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianGradSummable ht (x - y))
  have hsumB : Summable (fun k : ℤ => |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianGradSummable ht (x + y))
  have hA : |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
      ≤ ∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k : ℤ => deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumA)
  have hB : |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|
      ≤ ∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k : ℤ => deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumB)
  calc |(∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ)))|
      ≤ |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
          + |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))| := abs_add_le _ _
    _ ≤ (∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
          + (∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
        add_le_add hA hB
    _ = ∑' k : ℤ, (|deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
          + |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
        (Summable.tsum_add hsumA hsumB).symm

/-- **Pointwise kernel identity** (reduced).  Given lattice-Gaussian summability at the
two shifts, the full periodised image kernel equals the cosine spectral kernel:

  `K_full t x y = ∑_{m∈ℤ} exp(-t(mπ)²) cos(mπ x) cos(mπ y)`.

Obtained from `(★)` at `z = x − y` and `z = x + y` and the product-to-sum identity. -/
theorem intervalNeumannFullKernel_eq_cosineKernel (t : ℝ) (ht : 0 < t) (x y : ℝ)
    (hxy : LatticeGaussianSummable t (x - y)) (hxy' : LatticeGaussianSummable t (x + y))
    (hcos : Summable (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
      Real.cos ((m : ℝ) * Real.pi * (x - y)))
      ∧ Summable (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        Real.cos ((m : ℝ) * Real.pi * (x + y)))) :
    intervalNeumannFullKernel t x y =
      ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)) := by
  rw [intervalNeumannFullKernel]
  have hsplit : (∑' k : ℤ,
        (heatKernel t (x - y + 2 * k) + heatKernel t (x + y + 2 * k)))
      = gaussianLatticeSum t (x - y) + gaussianLatticeSum t (x + y) := by
    rw [gaussianLatticeSum, gaussianLatticeSum, ← Summable.tsum_add hxy hxy']
  rw [hsplit, gaussianLatticeSum_poisson t ht (x - y),
      gaussianLatticeSum_poisson t ht (x + y), ← mul_add,
      ← Summable.tsum_add hcos.1 hcos.2, ← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  -- product-to-sum:  cos A cos B = ½(cos(A−B) + cos(A+B))
  have hp2s : Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)
      = (1 / 2) * (Real.cos ((m : ℝ) * Real.pi * (x - y))
          + Real.cos ((m : ℝ) * Real.pi * (x + y))) := by
    have hargsub : (m : ℝ) * Real.pi * (x - y)
        = (m : ℝ) * Real.pi * x - (m : ℝ) * Real.pi * y := by ring
    have hargadd : (m : ℝ) * Real.pi * (x + y)
        = (m : ℝ) * Real.pi * x + (m : ℝ) * Real.pi * y := by ring
    rw [hargsub, hargadd, Real.cos_sub, Real.cos_add]; ring
  rw [hp2s]; ring

/-! ## The kernel↔spectral identity (Theorem 3) — reduced to one named lemma -/

/-- **Named reduction lemma.**  The only step between the proved pointwise kernel
identity and Theorem 3: the `∑_{m∈ℤ}`↔`∫_{[0,1]}` interchange together with the
`ℤ → ℕ` even-reflection reindexing turning `∫₀¹ cos(mπ y) f y` into `cosineCoeffs f n`.
No Mathlib gap. -/
def FullKernelIntegralInterchange (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  (∫ y, (∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
      (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y
        ∂ intervalMeasure 1)
    = unitIntervalCosineHeatValue t (cosineCoeffs f) x

/-- **Theorem 3 (kernel↔spectral identity), reduced.**  For `t > 0` and `x ∈ (0,1)`,
the full periodised-image Neumann propagator equals the cosine spectral heat value,
given the pointwise kernel identity (the Poisson/theta content, discharged by
`intervalNeumannFullKernel_eq_cosineKernel`) and the single named
interchange/reindexing lemma `FullKernelIntegralInterchange`. -/
theorem intervalFullSemigroupOperator_eq_cosineHeatValue
    (t : ℝ) (_ht : 0 < t) (f : ℝ → ℝ) (x : ℝ)
    (_hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hkernel : ∀ y, intervalNeumannFullKernel t x y =
      ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)))
    (hinterchange : FullKernelIntegralInterchange t f x) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  rw [intervalFullSemigroupOperator]
  rw [show (fun y => intervalNeumannFullKernel t x y * f y)
        = (fun y => (∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
            (Real.cos ((m : ℝ) * Real.pi * x) *
              Real.cos ((m : ℝ) * Real.pi * y))) * f y) from by
      funext y; rw [hkernel y]]
  exact hinterchange

/-! ## Corollary: spatial `C²` regularity of the full propagator -/

/-- **Corollary (spatial `C²`).**  Composing Theorem 3 with the proven
`unitIntervalCosineHeatValue_contDiff_two`, the full periodised Neumann propagator
`intervalFullSemigroupOperator t f` is `C²` in space, given the kernel↔spectral
identity (as a function identity). -/
theorem intervalFullSemigroupOperator_contDiff_two
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    (hidentity : (fun x => intervalFullSemigroupOperator t f x)
        = fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x) :
    ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator t f x) := by
  rw [hidentity]
  exact ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatValue_contDiff_two ht hM

end ShenWork.IntervalNeumannFullKernel

/-- The semigroup operator depends on `f` only through its values on `[0,1]`.
If `f₁ = f₂` on `[0,1]`, then `S(t)f₁ = S(t)f₂` at every point. -/
theorem intervalFullSemigroupOperator_congr_Icc
    {t : ℝ} {f₁ f₂ : ℝ → ℝ}
    (heq : Set.EqOn f₁ f₂ (Set.Icc (0:ℝ) 1)) (x : ℝ) :
    intervalFullSemigroupOperator t f₁ x = intervalFullSemigroupOperator t f₂ x := by
  unfold intervalFullSemigroupOperator
  congr 1
  apply MeasureTheory.integral_congr_ae
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.Icc (0:ℝ) 1, ?_, fun y hy => by rw [heq hy]⟩
  sorry -- ae_of_all: Icc 0 1 has full measure under intervalMeasure 1


/-- **Spectral identity via cosine series proxy.**  If `f = cs` on `[0,1]`
where `cs x = ∑ₙ aₙ cos(nπx)` with eigenvalue-summable coefficients,
then `S(t)f(x) = ∑ₙ e^{-tλₙ} aₙ cos(nπx)` on `[0,1]`.
This avoids the global `Continuous f` hypothesis by routing through the
globally-C² cosine series. -/
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_of_representation
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {a : ℕ → ℝ}
    (hsum : Summable (fun n => unitIntervalCosineEigenvalue n * |a n|))
    (hagree : Set.EqOn f (fun x => ∑' n, a n * cosineMode n x) (Set.Icc (0:ℝ) 1))
    (hcoeffs : ∀ n, cosineCoeffs f n = a n)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  sorry

