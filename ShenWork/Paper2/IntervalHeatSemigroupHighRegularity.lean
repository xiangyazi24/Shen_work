/-
  ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean

  The heat semigroup `S(t)u₀ = ∑ exp(-t λ_k) û₀_k cos(kπx)` has eigenvalue-
  squared-weighted summability for t > 0, hence C⁴ spatial regularity via
  `cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalParabolicDuhamelGainNonCircular
import ShenWork.Paper2.ChemMildC1etaComm

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupHighRegularity

/-- Eigenvalue-squared-weighted summability of heat semigroup coefficients.
For t > 0, `∑ λ_k² |exp(-tλ_k) û₀_k|` converges because:
`λ_k² |exp(-tλ_k)| |û₀_k| ≤ M₀ · λ_k² exp(-tλ_k)` and the latter sums
(by `eigenvalueSq_mul_exp_summable`). -/
theorem heatSemigroup_eigenvalueSq_summable
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => unitIntervalCosineEigenvalue k ^ 2 *
      |Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k|) := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (abs_nonneg _))
    (fun k => ?_)
    ((ShenWork.Paper2.eigenvalueSq_mul_exp_summable ht).mul_right M₀)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        |cosineCoeffs (intervalDomainLift u₀) k|)
      ≤ unitIntervalCosineEigenvalue k ^ 2 *
        (Real.exp (-t * unitIntervalCosineEigenvalue k) * M₀) := by
        gcongr
        exact hu₀_bound k
    _ = unitIntervalCosineEigenvalue k ^ 2 *
        Real.exp (-t * unitIntervalCosineEigenvalue k) * M₀ := by ring

set_option maxHeartbeats 800000 in
/-- The heat semigroup applied to bounded initial data is C⁴ in space for t > 0. -/
theorem heatSemigroup_contDiff_four
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 4 (fun x => ∑' k,
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x) := by
  apply ShenWork.Paper2.ParabolicDuhamelGainNonCircular.cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
  convert heatSemigroup_eigenvalueSq_summable hu₀_bound ht using 1
  ext k; ring

#print axioms heatSemigroup_eigenvalueSq_summable
#print axioms heatSemigroup_contDiff_four

end ShenWork.Paper2.HeatSemigroupHighRegularity
