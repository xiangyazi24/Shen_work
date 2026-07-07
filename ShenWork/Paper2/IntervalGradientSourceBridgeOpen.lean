import ShenWork.Paper2.IntervalGradientSourceIBPOpen
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.Paper2.IntervalDivergenceModeIdentity

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalGradientSourceBridgeOpen

open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupNeumann
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.Paper2.IntervalDivergenceModeIdentity

/-- The sine-basis heat value on `[0,1]`, with the same heat eigenvalues as the
Neumann cosine side.  Mode `0` contributes zero because `sin 0 = 0`. -/
def unitIntervalSineHeatValue (t : ℝ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    Real.exp (-t * unitIntervalCosineEigenvalue n) *
      Real.sin ((n : ℝ) * Real.pi * x) * a n

/-- `sqrt ((nπ)^2) = nπ` in the repository's interval normalization. -/
theorem sqrt_unitIntervalCosineEigenvalue_eq_kpi (n : ℕ) :
    Real.sqrt (unitIntervalCosineEigenvalue n) = (n : ℝ) * Real.pi := by
  have hnonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
  unfold unitIntervalCosineEigenvalue
  rw [Real.sqrt_sq hnonneg]

/-- Spatial derivative of the cosine heat value, expressed as a sine heat value
with the expected `-sqrt(λ_n)` multiplier. -/
theorem deriv_unitIntervalCosineHeatValue_eq_sineHeat_weighted
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    deriv (fun z : ℝ => unitIntervalCosineHeatValue t a z) x =
      unitIntervalSineHeatValue t
        (fun n => -Real.sqrt (unitIntervalCosineEigenvalue n) * a n) x := by
  have hb : Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * a n|) :=
    heatCoeff_eigenvalue_summable ht hM
  rw [unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
  rw [(cosineCoeffSeries_grad_hasDerivAt hb x).deriv]
  unfold unitIntervalSineHeatValue
  refine tsum_congr (fun n => ?_)
  simp only
  rw [sqrt_unitIntervalCosineEigenvalue_eq_kpi n]
  ring_nf

/-- Sine coefficients of an open/right derivative: `sin` has zero boundary
values, so no endpoint condition on `Q` is needed. -/
theorem sineCoeffs_deriv_right_eq_neg_sqrtLambda_cosineCoeffs
    {Q Q' : ℝ → ℝ}
    (hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' y) (Set.Ioi y) y)
    (hQ'_int : IntervalIntegrable Q' volume 0 1) (n : ℕ) :
    sineCoeffs Q' n =
      -Real.sqrt (unitIntervalCosineEigenvalue n) * cosineCoeffs Q n := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp [sineCoeffs, unitIntervalCosineEigenvalue]
  · have hn : n ≠ 0 := Nat.pos_iff_ne_zero.mp hnpos
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    set S : ℝ → ℝ := fun y => Real.sin ((n : ℝ) * Real.pi * y) with hS
    set S' : ℝ → ℝ := fun y => (n : ℝ) * Real.pi *
      Real.cos ((n : ℝ) * Real.pi * y) with hS'
    have hScont : ContinuousOn S (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le h01]
      rw [hS]
      fun_prop
    have hQcont' : ContinuousOn Q (Set.uIcc (0 : ℝ) 1) := by
      rwa [Set.uIcc_of_le h01]
    have hSderiv :
        ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
          HasDerivWithinAt S (S' y) (Set.Ioi y) y := by
      intro y _hy
      have hinner : HasDerivAt (fun z : ℝ => (n : ℝ) * Real.pi * z)
          ((n : ℝ) * Real.pi) y := by
        simpa using (hasDerivAt_id y).const_mul ((n : ℝ) * Real.pi)
      have hsin : HasDerivAt S (S' y) y := by
        rw [hS, hS']
        convert (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * y)).comp y hinner using 1
        ring
      exact hsin.hasDerivWithinAt
    have hQderiv' :
        ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
          HasDerivWithinAt Q (Q' y) (Set.Ioi y) y := by
      intro y hy
      rw [min_eq_left h01, max_eq_right h01] at hy
      exact hQderiv y hy
    have hS'_int : IntervalIntegrable S' volume 0 1 := by
      apply Continuous.intervalIntegrable
      rw [hS']
      fun_prop
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
      hScont hQcont' hSderiv hQderiv' hS'_int hQ'_int
    have hraw :
        (∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * Q' y)
          = -((n : ℝ) * Real.pi) *
              ∫ y in (0 : ℝ)..1,
                Real.cos ((n : ℝ) * Real.pi * y) * Q y := by
      change (∫ y in (0 : ℝ)..1, S y * Q' y)
          = -((n : ℝ) * Real.pi) *
              ∫ y in (0 : ℝ)..1,
                Real.cos ((n : ℝ) * Real.pi * y) * Q y
      have hboundary : S 1 * Q 1 - S 0 * Q 0 = 0 := by
        rw [hS]
        simp only [mul_one, mul_zero, Real.sin_zero, zero_mul, sub_zero]
        rw [Real.sin_nat_mul_pi]
        simp
      have hS'int :
          (∫ y in (0 : ℝ)..1, S' y * Q y)
            = (n : ℝ) * Real.pi *
                ∫ y in (0 : ℝ)..1,
                  Real.cos ((n : ℝ) * Real.pi * y) * Q y := by
        rw [hS', ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun y _hy => ?_)
        ring
      rw [hibp, hboundary, zero_sub, hS'int]
      ring
    rw [sineCoeffs_pos hn,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hn,
      hraw, sqrt_unitIntervalCosineEigenvalue_eq_kpi n]
    ring

/-- The open gradient-source spectral bridge: the spatial derivative of the full
Neumann semigroup applied to `Q` is the sine heat value of the open derivative
`Q'`.  This is the spectral form of the Task294 kernel IBP identity. -/
theorem deriv_intervalFullSemigroupOperator_eq_sineHeatValue_open
    {t : ℝ} (ht : 0 < t)
    {Q Q' : ℝ → ℝ}
    (hQcont : Continuous Q)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' y) (Set.Ioi y) y)
    (hQ'_int : IntervalIntegrable Q' volume 0 1)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs Q n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x =
      unitIntervalSineHeatValue t (sineCoeffs Q') x := by
  have heq_eventual :
      (fun z : ℝ => intervalFullSemigroupOperator t Q z)
        =ᶠ[nhds x]
      (fun z : ℝ => unitIntervalCosineHeatValue t (cosineCoeffs Q) z) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hQcont hM
      (Set.Ioo_subset_Icc_self hz)
  rw [heq_eventual.deriv_eq]
  rw [deriv_unitIntervalCosineHeatValue_eq_sineHeat_weighted ht hM x]
  unfold unitIntervalSineHeatValue
  refine tsum_congr (fun n => ?_)
  rw [sineCoeffs_deriv_right_eq_neg_sqrtLambda_cosineCoeffs
    hQcont.continuousOn hQderiv hQ'_int n]

/-- Kernel-to-sine bridge for the gradient source leg.  Combining Task294's open
IBP formula with the spectral derivative bridge identifies the Ktilde source
integral with the sine heat value of the derivative source. -/
theorem neg_conjugateKernel_source_integral_eq_sineHeatValue_open
    {t : ℝ} (ht : 0 < t)
    {Q Q' : ℝ → ℝ}
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQcont : Continuous Q)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' y) (Set.Ioi y) y)
    (hQ'_int : IntervalIntegrable Q' volume 0 1)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs Q n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    -(∫ y in (0 : ℝ)..1,
        Q' y * intervalNeumannConjugateKernel t x y)
      = unitIntervalSineHeatValue t (sineCoeffs Q') x := by
  have hker :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral_open
      ht hQ_meas hQ_bound hQcont.continuousOn hQderiv hQ'_int x
  rw [← hker]
  exact deriv_intervalFullSemigroupOperator_eq_sineHeatValue_open ht hQcont
    hQderiv hQ'_int hM hx

end ShenWork.Paper2.IntervalGradientSourceBridgeOpen
