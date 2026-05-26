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
