/-
  ShenWork/Paper2/IntervalDomainLemma21.lean

  Paper 2 Lemma 2.1 on intervalDomain: concrete heat-semigroup bridge.

  This file connects the already proved unit-interval heat estimates to the
  Paper2 interval-domain function interface.  It does not claim the full
  `Lemma_2_1 intervalDomain` package yet: the remaining missing analytic input
  is the fractional-domain graph norm / semigroup-difference estimate

    ‖S(t)u - u‖₂ ≤ C t^σ ‖u‖_{X^σ_2}

  for the actual Neumann heat semigroup on `[0,1]`, with a real-valued total
  `fractionalNorm` compatible with the statement layer.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.HeatKernelGradientEstimates

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLemma21

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates

/-! ### Concrete interval-domain heat-semigroup interface -/

/-- The `LpSeminorm` used for interval-domain functions through the concrete
zero-extension `intervalDomainLift`. -/
def intervalDomainLpNorm (q : ℝ) (u : intervalDomain.Point → ℝ) : ℝ :=
  lpNorm (intervalDomainLift u) (ENNReal.ofReal q) (intervalMeasure 1)

/-- The restricted reflected heat operator as an interval-domain point
function.  This is the H0.1 helper operator on the unit interval. -/
def intervalDomainHeatSemigroup
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomain.Point → ℝ :=
  fun x => intervalSemigroupOperator 1 t (intervalDomainLift u) x.1

/-- Real-valued `lpNorm` respects almost-everywhere equality.  Mathlib has the
corresponding theorem for `eLpNorm`; this is the `toReal` wrapper needed by the
statement-layer real norms. -/
theorem lpNorm_congr_ae_real
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} {μ : Measure α} {f g : α → E}
    (hfg : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have hg : AEStronglyMeasurable g μ :=
      (aestronglyMeasurable_congr hfg).mp hf
    rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg, eLpNorm_congr_ae hfg]
  · have hg : ¬ AEStronglyMeasurable g μ := by
      intro hg
      exact hf ((aestronglyMeasurable_congr hfg).mpr hg)
    simp [lpNorm, hf, hg]

/-- On the restricted unit interval measure, lifting the point-function heat
output agrees almost everywhere with the real-line helper operator. -/
theorem intervalDomainHeatSemigroup_lift_ae_eq
    (t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLift (intervalDomainHeatSemigroup t u)
      =ᵐ[intervalMeasure 1]
        fun x : ℝ => intervalSemigroupOperator 1 t (intervalDomainLift u) x := by
  unfold intervalMeasure intervalSet
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet (Set.Icc (0 : ℝ) 1) by simp)] with x hx
  simp [intervalDomainLift, intervalDomainHeatSemigroup, hx]

/-- The point-function heat output has the same `LpSeminorm` as the concrete
real helper operator on `[0,1]`. -/
theorem intervalDomainHeatSemigroup_lpNorm_eq
    (q t : ℝ) (u : intervalDomain.Point → ℝ) :
    intervalDomainLpNorm q (intervalDomainHeatSemigroup t u) =
      lpNorm
        (fun x : ℝ => intervalSemigroupOperator 1 t (intervalDomainLift u) x)
        (ENNReal.ofReal q) (intervalMeasure 1) := by
  exact lpNorm_congr_ae_real
    (intervalDomainHeatSemigroup_lift_ae_eq t u)

/-! ### H0.1/H0.2 estimates specialized to intervalDomain -/

/-- H0.1 specialized to `intervalDomain`: finite `L^p → L^q` smoothing for
the concrete unit-interval helper heat operator, stated on point functions via
`intervalDomainLift`. -/
theorem intervalDomainHeat_Lp_Lq_bound_from_memLp
    {t p q r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    (hpq : p ≤ q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    intervalDomainLpNorm q (intervalDomainHeatSemigroup t u) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p - 1 / q) *
        intervalDomainLpNorm p u := by
  rw [intervalDomainHeatSemigroup_lpNorm_eq]
  exact intervalHeatSemigroup_Lp_Lq_bound
    (L := 1) (t := t) (p := p) (q := q) (r := r)
    ht hrp hpq (f := intervalDomainLift u) hu_mem

/-- H0.2 specialized to `intervalDomain`: finite `L^p → L^q` smoothing for
the spatial derivative of the unit-interval helper heat operator. -/
theorem intervalDomainHeat_grad_Lp_Lq_bound_from_memLp
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t * intervalDomainLpNorm p u := by
  exact unitIntervalSemigroupOperator_grad_Lp_Lq_lpNorm_bound
    (t := t) (p := p) (q := q) ht hp hq
    (f := intervalDomainLift u) hu_mem

/-- The corresponding `L^p → L∞` derivative estimate for the unit-interval
helper heat operator. -/
theorem intervalDomainHeat_grad_Lp_Linfty_bound_from_memLp
    {t p : ℝ} (ht : 0 < t) (hp : 1 ≤ p)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        ∞ (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t * intervalDomainLpNorm p u := by
  exact unitIntervalSemigroupOperator_grad_Lp_Linfty_lpNorm_bound
    (t := t) (p := p) ht hp
    (f := intervalDomainLift u) hu_mem

/-! ### Fractional semigroup multiplier estimates -/

/-- Elementary bound used for fractional time regularity:
`1 - exp(-x) ≤ x` on the nonnegative half-line. -/
theorem one_sub_exp_neg_le_self (x : ℝ) :
    1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- For `0 < σ ≤ 1`, the heat multiplier difference is bounded by the
fractional power of the time-frequency product. -/
theorem abs_exp_neg_sub_one_le_rpow
    {x sigma : ℝ} (hx : 0 ≤ x) (hsigma_pos : 0 < sigma)
    (hsigma_le : sigma ≤ 1) :
    |Real.exp (-x) - 1| ≤ x ^ sigma := by
  have hexp_le_one : Real.exp (-x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hexp_le_one)]
  by_cases hx_le_one : x ≤ 1
  · have hbasic : 1 - Real.exp (-x) ≤ x :=
      one_sub_exp_neg_le_self x
    have hx_pow : x ≤ x ^ sigma := by
      have hpow : x ^ (1 : ℝ) ≤ x ^ sigma :=
        Real.rpow_le_rpow_of_exponent_ge' hx hx_le_one
          (le_of_lt hsigma_pos) hsigma_le
      simpa [Real.rpow_one] using hpow
    have hneg : -(Real.exp (-x) - 1) = 1 - Real.exp (-x) := by ring
    rw [hneg]
    exact hbasic.trans hx_pow
  · have hone_le_x : 1 ≤ x := le_of_not_ge hx_le_one
    have hone_le_pow : 1 ≤ x ^ sigma :=
      Real.one_le_rpow hone_le_x (le_of_lt hsigma_pos)
    have hdiff_le_one : 1 - Real.exp (-x) ≤ 1 := by
      have hnonneg : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
      linarith
    have hneg : -(Real.exp (-x) - 1) = 1 - Real.exp (-x) := by ring
    rw [hneg]
    exact hdiff_le_one.trans hone_le_pow

/-- Rescaled form of `abs_exp_neg_sub_one_le_rpow`, suitable for spectral
coefficients with eigenvalue `λ`. -/
theorem heat_time_multiplier_difference_le_fractional
    {lambda t sigma : ℝ} (hlambda : 0 ≤ lambda) (ht : 0 < t)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1) :
    |Real.exp (-(t * lambda)) - 1| ≤ t ^ sigma * lambda ^ sigma := by
  have htl_nonneg : 0 ≤ t * lambda := mul_nonneg (le_of_lt ht) hlambda
  have h :=
    abs_exp_neg_sub_one_le_rpow
      (x := t * lambda) (sigma := sigma) htl_nonneg
      hsigma_pos hsigma_le
  rwa [Real.mul_rpow (le_of_lt ht) hlambda] at h

/-- The endpoint analytic-semigroup multiplier bound on `0 ≤ σ ≤ 1`. -/
theorem rpow_mul_exp_neg_le_one_of_le_one
    {x sigma : ℝ} (hx : 0 < x) (hsigma_nonneg : 0 ≤ sigma)
    (hsigma_le : sigma ≤ 1) :
    x ^ sigma * Real.exp (-x) ≤ 1 := by
  by_cases hx_le_one : x ≤ 1
  · have hpow : x ^ sigma ≤ 1 :=
      Real.rpow_le_one (le_of_lt hx) hx_le_one hsigma_nonneg
    have hexp : Real.exp (-x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    exact mul_le_one₀ hpow (Real.exp_nonneg _) hexp
  · have hone_le_x : 1 ≤ x := le_of_not_ge hx_le_one
    have hpow : x ^ sigma ≤ x := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hone_le_x hsigma_le
    have hprod : x ^ sigma * Real.exp (-x) ≤ x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    have hte : x * Real.exp (-x) ≤ Real.exp (-1) :=
      Real.mul_exp_neg_le_exp_neg_one x
    have he1 : Real.exp (-1 : ℝ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by norm_num)
    exact hprod.trans (hte.trans he1)

/-- Equivalent decay form of `rpow_mul_exp_neg_le_one_of_le_one`. -/
theorem exp_neg_le_rpow_neg_of_le_one
    {x sigma : ℝ} (hx : 0 < x) (hsigma_nonneg : 0 ≤ sigma)
    (hsigma_le : sigma ≤ 1) :
    Real.exp (-x) ≤ x ^ (-sigma) := by
  have hmul :=
    rpow_mul_exp_neg_le_one_of_le_one
      (x := x) (sigma := sigma) hx hsigma_nonneg hsigma_le
  have hxpow_pos : 0 < x ^ sigma :=
    Real.rpow_pos_of_pos hx sigma
  rw [Real.rpow_neg (le_of_lt hx)]
  have h' : Real.exp (-x) ≤ (1 : ℝ) * (x ^ sigma)⁻¹ := by
    exact (le_mul_inv_iff₀ hxpow_pos).mpr
      (by simpa [mul_comm] using hmul)
  simpa using h'

/-- Spectral smoothing multiplier:
`λ^σ exp(-tλ) ≤ t^{-σ}` for positive `t, λ` and `0 ≤ σ ≤ 1`. -/
theorem heat_time_multiplier_smoothing_le
    {lambda t sigma : ℝ} (hlambda : 0 < lambda) (ht : 0 < t)
    (hsigma_nonneg : 0 ≤ sigma) (hsigma_le : sigma ≤ 1) :
    lambda ^ sigma * Real.exp (-(t * lambda)) ≤ t ^ (-sigma) := by
  have htl_pos : 0 < t * lambda := mul_pos ht hlambda
  have hmul :=
    rpow_mul_exp_neg_le_one_of_le_one
      (x := t * lambda) (sigma := sigma) htl_pos
      hsigma_nonneg hsigma_le
  rw [Real.mul_rpow (le_of_lt ht) (le_of_lt hlambda)] at hmul
  have htspow_pos : 0 < t ^ sigma :=
    Real.rpow_pos_of_pos ht sigma
  rw [Real.rpow_neg (le_of_lt ht)]
  have h' :
      lambda ^ sigma * Real.exp (-(t * lambda)) ≤
        (1 : ℝ) * (t ^ sigma)⁻¹ := by
    exact (le_mul_inv_iff₀ htspow_pos).mpr
      (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  simpa using h'

/-! ### Finite spectral-coefficient consequences -/

/-- Single-coefficient form of the fractional `S(t)-I` multiplier estimate. -/
theorem spectralCoeff_heat_difference_sq_le
    {lambda t sigma : ℝ} {a : ℂ}
    (hlambda : 0 ≤ lambda) (ht : 0 < t)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1) :
    ‖(((Real.exp (-(t * lambda)) - 1 : ℝ) : ℂ) * a)‖ ^ 2 ≤
      ((t ^ sigma * lambda ^ sigma) ^ 2) * ‖a‖ ^ 2 := by
  have habs :=
    heat_time_multiplier_difference_le_fractional
      (lambda := lambda) (t := t) (sigma := sigma)
      hlambda ht hsigma_pos hsigma_le
  have hscale_nonneg : 0 ≤ t ^ sigma * lambda ^ sigma := by
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
      (Real.rpow_nonneg hlambda _)
  have hnorm_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have hmul :
      |Real.exp (-(t * lambda)) - 1| * ‖a‖ ≤
        (t ^ sigma * lambda ^ sigma) * ‖a‖ :=
    mul_le_mul_of_nonneg_right habs hnorm_nonneg
  have hlhs_nonneg :
      0 ≤ |Real.exp (-(t * lambda)) - 1| * ‖a‖ :=
    mul_nonneg (abs_nonneg _) hnorm_nonneg
  have hrhs_nonneg :
      0 ≤ (t ^ sigma * lambda ^ sigma) * ‖a‖ :=
    mul_nonneg hscale_nonneg hnorm_nonneg
  calc
    ‖(((Real.exp (-(t * lambda)) - 1 : ℝ) : ℂ) * a)‖ ^ 2
        =
          (|Real.exp (-(t * lambda)) - 1| * ‖a‖) ^ 2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ((t ^ sigma * lambda ^ sigma) * ‖a‖) ^ 2 := by
            nlinarith
    _ = ((t ^ sigma * lambda ^ sigma) ^ 2) * ‖a‖ ^ 2 := by
            ring

/-- Finite-mode coefficient-energy form of the fractional `S(t)-I`
estimate for the unit-interval Neumann spectrum. -/
theorem finiteSpectralCoeff_heat_difference_energy_le
    (s : Finset ℕ) {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1) :
    (∑ n ∈ s,
        ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
          a n)‖ ^ 2) ≤
      (t ^ sigma) ^ 2 *
        ∑ n ∈ s,
          (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 * ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro n _hn
  have hlambda : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have hterm :=
    spectralCoeff_heat_difference_sq_le
      (lambda := unitIntervalCosineEigenvalue n) (t := t)
      (sigma := sigma) (a := a n)
      hlambda ht hsigma_pos hsigma_le
  calc
    ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) - 1 : ℝ) : ℂ) *
          a n)‖ ^ 2
        ≤
          ((t ^ sigma * unitIntervalCosineEigenvalue n ^ sigma) ^ 2) *
            ‖a n‖ ^ 2 :=
            hterm
    _ =
          (t ^ sigma) ^ 2 *
            ((unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
              ‖a n‖ ^ 2) := by
            ring

/-- Single-coefficient form of the spectral smoothing multiplier estimate. -/
theorem spectralCoeff_heat_smoothing_sq_le
    {lambda t sigma : ℝ} {a : ℂ}
    (hlambda : 0 < lambda) (ht : 0 < t)
    (hsigma_nonneg : 0 ≤ sigma) (hsigma_le : sigma ≤ 1) :
    (lambda ^ sigma) ^ 2 *
        ‖(((Real.exp (-(t * lambda)) : ℝ) : ℂ) * a)‖ ^ 2 ≤
      (t ^ (-sigma)) ^ 2 * ‖a‖ ^ 2 := by
  have hmul :=
    heat_time_multiplier_smoothing_le
      (lambda := lambda) (t := t) (sigma := sigma)
      hlambda ht hsigma_nonneg hsigma_le
  have hnorm_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have hmul_norm :
      (lambda ^ sigma * Real.exp (-(t * lambda))) * ‖a‖ ≤
        t ^ (-sigma) * ‖a‖ :=
    mul_le_mul_of_nonneg_right hmul hnorm_nonneg
  have hlambda_pow_nonneg : 0 ≤ lambda ^ sigma :=
    Real.rpow_nonneg (le_of_lt hlambda) _
  have hexp_nonneg : 0 ≤ Real.exp (-(t * lambda)) :=
    Real.exp_nonneg _
  have hleft_nonneg :
      0 ≤ (lambda ^ sigma * Real.exp (-(t * lambda))) * ‖a‖ :=
    mul_nonneg (mul_nonneg hlambda_pow_nonneg hexp_nonneg) hnorm_nonneg
  have hright_nonneg : 0 ≤ t ^ (-sigma) * ‖a‖ :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) hnorm_nonneg
  calc
    (lambda ^ sigma) ^ 2 *
        ‖(((Real.exp (-(t * lambda)) : ℝ) : ℂ) * a)‖ ^ 2
        =
          ((lambda ^ sigma * Real.exp (-(t * lambda))) * ‖a‖) ^ 2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hexp_nonneg]
            ring
    _ ≤ (t ^ (-sigma) * ‖a‖) ^ 2 := by
            nlinarith
    _ = (t ^ (-sigma)) ^ 2 * ‖a‖ ^ 2 := by
            ring

/-- Finite-mode coefficient-energy form of `A^σ e^{-tA}` smoothing over
nonzero Neumann modes. -/
theorem finiteSpectralCoeff_heat_smoothing_energy_le
    (s : Finset ℕ) {t sigma : ℝ} (a : ℕ → ℂ)
    (ht : 0 < t) (hsigma_nonneg : 0 ≤ sigma) (hsigma_le : sigma ≤ 1)
    (hs_nonzero : ∀ n ∈ s, n ≠ 0) :
    (∑ n ∈ s,
        (unitIntervalCosineEigenvalue n ^ sigma) ^ 2 *
          ‖(((Real.exp (-(t * unitIntervalCosineEigenvalue n)) : ℝ) : ℂ) *
            a n)‖ ^ 2) ≤
      (t ^ (-sigma)) ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro n hn
  have hn0 : n ≠ 0 := hs_nonzero n hn
  have hn_pos_real : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlambda_pos : 0 < unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  exact
    spectralCoeff_heat_smoothing_sq_le
      (lambda := unitIntervalCosineEigenvalue n) (t := t)
      (sigma := sigma) (a := a n)
      hlambda_pos ht hsigma_nonneg hsigma_le

/-! ### Hilbert-basis coefficient bridge for finite sums -/

/-- The complex `L²` representative of an interval-domain real function,
through the existing zero-extension to the unit interval. -/
def intervalDomainLiftComplexLp2
    (u : intervalDomain.Point → ℝ)
    (hu : MemLp (intervalDomainLift u) (2 : ℝ≥0∞) (intervalMeasure 1)) :
    Lp ℂ 2 (intervalMeasure 1) :=
  (hu.ofReal).toLp (fun x : ℝ => (intervalDomainLift u x : ℂ))

/-- Finite Bessel inequality for the complete Neumann cosine Hilbert basis. -/
theorem unitIntervalCosineHilbertCoeff_finite_sq_le_norm_sq
    (s : Finset ℕ) (v : Lp ℂ 2 (intervalMeasure 1)) :
    (∑ n ∈ s, ‖unitIntervalCosineHilbertBasis.repr v n‖ ^ 2) ≤
      ‖v‖ ^ 2 := by
  have h :=
    (unitIntervalCosineHilbertBasis.orthonormal).sum_inner_products_le
      (x := v) (s := s)
  simpa [HilbertBasis.repr_apply_apply] using h

/-- The finite cosine-coefficient square sum of an interval-domain input is
controlled by its concrete `L²` seminorm. -/
theorem intervalDomainCosineHilbertCoeff_finite_sq_le_lpNorm_sq
    (s : Finset ℕ) (u : intervalDomain.Point → ℝ)
    (hu : MemLp (intervalDomainLift u) (2 : ℝ≥0∞) (intervalMeasure 1)) :
    (∑ n ∈ s,
        ‖unitIntervalCosineHilbertBasis.repr
          (intervalDomainLiftComplexLp2 u hu) n‖ ^ 2) ≤
      intervalDomainLpNorm 2 u ^ 2 := by
  have hbase :=
    unitIntervalCosineHilbertCoeff_finite_sq_le_norm_sq
      s (intervalDomainLiftComplexLp2 u hu)
  have hnorm :
      ‖intervalDomainLiftComplexLp2 u hu‖ =
        intervalDomainLpNorm 2 u := by
    calc
      ‖intervalDomainLiftComplexLp2 u hu‖
          =
            lpNorm (fun x : ℝ => (intervalDomainLift u x : ℂ))
              (2 : ℝ≥0∞) (intervalMeasure 1) := by
              rw [intervalDomainLiftComplexLp2, Lp.norm_toLp,
                toReal_eLpNorm (hu.ofReal).aestronglyMeasurable]
      _ =
            lpNorm (intervalDomainLift u)
              (2 : ℝ≥0∞) (intervalMeasure 1) :=
              unitInterval_lpNorm_complex_ofReal_eq hu
      _ = intervalDomainLpNorm 2 u := by
              simp [intervalDomainLpNorm]
  rwa [hnorm] at hbase

end ShenWork.Paper2.IntervalDomainLemma21

end
