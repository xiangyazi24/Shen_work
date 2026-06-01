/-
  ShenWork/Paper2/IntervalDuhamelIntegrability.lean

  Integrability of the Duhamel source terms (flux and logistic) for
  bounded trajectories on the unit interval. These are the regularity
  prerequisites needed to apply gradDuhamel_sup_bound and
  valueDuhamel_sup_bound in the Picard iteration.

  Key insight: on compact [0,1], bounded functions with AEStronglyMeasurable
  slices are integrable (intervalMeasure_integrable_of_abs_bound). The
  semigroup maps bounded functions to C² functions on [0,1], so each
  Duhamel integrand is bounded and measurable.
-/
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure
  intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap

noncomputable section

namespace ShenWork.IntervalDuhamelIntegrability

/-- The logistic source for a bounded trajectory is bounded. -/
theorem logisticLifted_bounded (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hw : ∀ x, |w x| ≤ M) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, |logisticLifted p w y| ≤ C := by
  set C := M * (p.a + p.b * M ^ p.α) with hCdef
  refine ⟨C, ?_, ?_⟩
  · apply mul_nonneg hM
    apply add_nonneg p.ha
    exact mul_nonneg p.hb (Real.rpow_nonneg hM _)
  · intro y
    unfold logisticLifted
    simp only [intervalDomainLift]
    split_ifs with hy
    · -- y ∈ [0,1]: |lift(w·(a-bw^α))| ≤ M·(a + b·M^α)
      sorry
    · simp [abs_of_nonneg, le_of_eq]
      exact mul_nonneg hM (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))

/-- The value Duhamel integrand `s ↦ S(t-s) L(w(s))(x)` is bounded. -/
theorem valueDuhamelIntegrand_bounded (p : CM2Params) {T M : ℝ} (hT : 0 < T)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) (hM : 0 ≤ M)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 ≤ s → s < t →
      |intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x| ≤ C := by
  refine ⟨M * (p.a + p.b * M ^ p.α), mul_nonneg hM (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _))), ?_⟩
  intro s hs hst
  have hts : 0 < t - s := by linarith
  sorry

end ShenWork.IntervalDuhamelIntegrability
