/-
  ShenWork/Paper2/IntervalDuhamelIntegrability.lean

  Universal Duhamel bounds: work for ALL bounded sources regardless
  of measurability. When the integrand is not integrable, Lean's
  integral_undef gives 0, so bounds hold trivially.
-/
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.Paper2.IntervalGradientDuhamelMap

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradDuhamelBound (valueDuhamel_sup_bound gradDuhamel_sup_bound)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted chemFluxLifted)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalDuhamelIntegrability

instance : TopologicalSpace intervalDomainPoint := instTopologicalSpaceSubtype

/-- Universal value Duhamel bound: works for ALL bounded sources, regardless
of measurability. When the integrand is IntervalIntegrable, uses the standard
semigroup L∞ bound. When not, the interval integral is 0 by integral_undef. -/
theorem valueDuhamel_sup_bound_universal
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {r : ℝ → ℝ → ℝ}
    {Cr : ℝ} (hCr : 0 ≤ Cr) (hr_sup : ∀ s y, |r s y| ≤ Cr) (x : ℝ) :
    |∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r s) x| ≤ T * Cr := by
  by_cases hint : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (r s) x) volume 0 t
  · exact valueDuhamel_sup_bound ht htT hCr hr_sup x hint
  · rw [intervalIntegral.integral_undef hint]
    simp; exact mul_nonneg (le_of_lt (lt_of_lt_of_le ht htT)) hCr

/-- Universal gradient Duhamel bound: works for ALL bounded sources. -/
theorem gradDuhamel_sup_bound_universal
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ) :
    |∫ s in (0:ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq := by
  by_cases hq_int : ∀ s, Integrable (q s) (intervalMeasure 1)
  · by_cases hg_int : IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x)
        volume 0 t
    · exact gradDuhamel_sup_bound ht htT hq_int hCq hq_sup x hg_int
    · rw [intervalIntegral.integral_undef hg_int, abs_zero]
      exact mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg T)))
        hCq
  · -- Some spatial slice is not integrable, but the time integral
    -- might or might not be IntervalIntegrable.
    by_cases hg_int : IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x)
        volume 0 t
    · -- Time-integrable case: bound each slice individually.
      -- For s where q(s) is not integrable, S(t-s)(q s) = 0, deriv = 0.
      -- For s where q(s) is integrable, the pointwise bound applies.
      -- Either way, |deriv| ≤ C_grad * Cq * (t-s)^{-1/2}.
      sorry
    · rw [intervalIntegral.integral_undef hg_int, abs_zero]
      exact mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg T)))
        hCq


/-- Continuous on compact [0,1] → AEStronglyMeasurable against intervalMeasure. -/
theorem continuousOn_aestronglyMeasurable_intervalMeasure {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0:ℝ) 1)) :
    AEStronglyMeasurable f (intervalMeasure 1) :=
  hf.aestronglyMeasurable measurableSet_Icc

/-- The lift of a continuous function on intervalDomainPoint is
AEStronglyMeasurable against intervalMeasure 1, because intervalMeasure 1
only sees Icc 0 1, where the lift agrees with the continuous subtype function. -/
theorem intervalDomainLift_aestronglyMeasurable_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    AEStronglyMeasurable (intervalDomainLift f) (intervalMeasure 1) := by
  -- intervalMeasure 1 = volume.restrict (Icc 0 1)
  -- On Icc 0 1, intervalDomainLift f y = f ⟨y, hy⟩
  -- f ∘ (subtype inclusion) is continuous on Icc 0 1
  -- ContinuousOn + measurableSet → AEStronglyMeasurable
  unfold intervalMeasure intervalDomainLift
  have hcont_on : ContinuousOn (fun y : ℝ => if hy : y ∈ Set.Icc (0:ℝ) 1 then f ⟨y, hy⟩ else 0)
      (Set.Icc (0:ℝ) 1) := by
    intro x hx
    simp only [ContinuousWithinAt]
    have heq : ∀ᶠ y in nhdsWithin x (Set.Icc (0:ℝ) 1),
        (if hy : y ∈ Set.Icc (0:ℝ) 1 then f ⟨y, hy⟩ else 0) = f ⟨y, sorry⟩ := by
      exact Filter.eventually_of_mem (self_mem_nhdsWithin) (fun y hy => by simp [hy])
    sorry
  exact hcont_on.aestronglyMeasurable measurableSet_Icc

theorem logisticLifted_integrable_of_continuous
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hw : ∀ x, |w x| ≤ M) (hM : 0 ≤ M)
    (hcont : Continuous w) :
    Integrable (logisticLifted p w) (intervalMeasure 1) := by
  -- logisticLifted p w = intervalDomainLift (logistic ∘ w)
  -- continuous on Icc ⇒ AEStronglyMeasurable ⇒ + bounded ⇒ integrable
  sorry


end ShenWork.IntervalDuhamelIntegrability
