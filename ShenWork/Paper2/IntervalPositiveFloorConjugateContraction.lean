import ShenWork.Paper2.IntervalPositiveFloorNonlinearLipschitz
import ShenWork.Paper2.IntervalConjugatePicardCoreInhabit

/-!
# Conjugate-map contraction on a positive trajectory cone

This is the banked B-form contraction with the source-power Lipschitz estimate
restricted to `c ≤ u,w ≤ M`.  It works for every `α,γ > 0`.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalPositiveFloorConjugateContraction

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
open ShenWork.IntervalConjugateChemFluxIntegrable
  (conjugateChemFlux_duhamel_intervalIntegrable_of_ball
   conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball)
open ShenWork.IntervalDuhamelIntegrability
  (chemFluxLifted_integrable_of_continuous)
open ShenWork.IntervalConjugateLogisticDiffBall
  (logistic_duhamel_diff_bound_of_ball)
open ShenWork.IntervalConjugatePicardBounds
  (intervalConjugateDuhamelMap_diff_bound_of_banked)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)

private def endpointZero : intervalDomainPoint :=
  ⟨0, by constructor <;> norm_num⟩

/-- The full B-form map is a contraction estimate on the positive cone. -/
theorem intervalConjugateDuhamelMap_diff_bound_of_positive_cone
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {T M c CQ CL d : ℝ}
    (hT : 0 < T) (hM : 0 < M) (hc : 0 < c) (hcM : c ≤ M)
    (hCQ : CQ =
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) +
        M * (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * powerLip p.γ c M))) +
        M * (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ))) * p.β *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
            (2 * (p.ν * powerLip p.γ c M))))
    (hCL_nn : 0 ≤ CL)
    (hCL_lip : ∀ r s : ℝ, |r| ≤ M → |s| ≤ M →
      |r * (p.a - p.b * r ^ p.α) - s * (p.a - p.b * s ^ p.α)| ≤
        CL * |r - s|)
    {u w : ℝ → intervalDomainPoint → ℝ}
    (hub : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M)
    (huf : ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ u t x)
    (hwb : ∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M)
    (hwf : ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x)
    (huc : HasContinuousSlices T u) (hwc : HasContinuousSlices T w)
    (hum : HasJointMeasurability u) (hwm : HasJointMeasurability w)
    (hd : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    |intervalConjugateDuhamelMap p u₀ u t x -
      intervalConjugateDuhamelMap p u₀ w t x| ≤
      (|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ) +
        T * CL) * d := by
  have hd_nn : 0 ≤ d :=
    (abs_nonneg _).trans (hd T hT le_rfl endpointZero)
  have hun : ∀ τ, 0 < τ → τ ≤ T → ∀ z, 0 ≤ u τ z := by
    intro τ hτ hτT z
    exact hc.le.trans (huf τ hτ hτT z)
  have hwn : ∀ τ, 0 < τ → τ ≤ T → ∀ z, 0 ≤ w τ z := by
    intro τ hτ hτT z
    exact hc.le.trans (hwf τ hτ hτT z)
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    have hLip := powerLip_nonneg p.hγ hc hcM
    have hRG : 0 ≤ Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
    have hRGL : 0 ≤ Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * powerLip p.γ c M)) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLip))
    have hRV : 0 ≤ Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverWeight p k) ^ 2) *
          (2 * (p.ν * powerLip p.γ c M)) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLip))
    exact add_nonneg (add_nonneg hRG (mul_nonneg hM.le hRGL))
      (mul_nonneg (mul_nonneg (mul_nonneg hM.le hRG) p.hβ) hRV)
  have hq_diff : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxLifted p (u s) y - chemFluxLifted p (w s) y| ≤ CQ * d := by
    intro s hs hsT y
    have hb := chemFluxLifted_diff_bound_of_pos_slice p hc hcM hd_nn
      (hub s hs hsT) (huf s hs hsT) (huc s hs hsT)
      (hwb s hs hsT) (hwf s hs hsT) (hwc s hs hsT)
      (hd s hs hsT) y
    simpa [hCQ] using hb
  have hq_int_diff : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y ↦ chemFluxLifted p (u s) y - chemFluxLifted p (w s) y)
      (intervalMeasure 1) := by
    intro s hs hsT
    exact (chemFluxLifted_integrable_of_continuous p (hub s hs hsT) hM.le
      (huc s hs hsT) (hun s hs hsT)).sub
      (chemFluxLifted_integrable_of_continuous p (hwb s hs hsT) hM.le
        (hwc s hs hsT) (hwn s hs hsT))
  have hkernel : ∀ (z : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ y, |z τ y| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ y, 0 ≤ z τ y) →
      HasContinuousSlices T z →
      ∀ s, 0 < s → s ≤ T → Integrable
        (fun y : ℝ ↦ deriv (fun y' : ℝ ↦ intervalNeumannFullKernel (t - s) x.1 y') y *
          chemFluxLifted p (z s) y) (intervalMeasure 1) := by
    intro z hzb hzn hzc s hs hsT
    have hKint : Integrable
        (fun y : ℝ ↦ deriv (fun y' : ℝ ↦ intervalNeumannFullKernel (t - s) x.1 y') y)
        (intervalMeasure 1) := by
      by_cases hts : 0 < t - s
      · simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
        exact (ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_snd
          hts x.1).integrableOn_Icc
      · have hkz : (fun y : ℝ ↦
            deriv (fun y' : ℝ ↦ intervalNeumannFullKernel (t - s) x.1 y') y) =
            fun _ ↦ (0 : ℝ) := by
          funext y
          have hk : (fun y' : ℝ ↦ intervalNeumannFullKernel (t - s) x.1 y') =
              fun _ ↦ (0 : ℝ) := by
            funext y'
            simp only [intervalNeumannFullKernel]
            rw [show (fun k : ℤ ↦
                heatKernel (t - s) (x.1 - y' + 2 * (k : ℝ)) +
                heatKernel (t - s) (x.1 + y' + 2 * (k : ℝ))) =
                fun _ ↦ (0 : ℝ) from by
              funext k
              rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
                ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts), add_zero]]
            exact tsum_zero
          rw [hk, deriv_const]
        rw [hkz]
        simp
    have hQint : Integrable (chemFluxLifted p (z s)) (intervalMeasure 1) :=
      chemFluxLifted_integrable_of_continuous p (hzb s hs hsT) hM.le
        (hzc s hs hsT) (hzn s hs hsT)
    have hQbdd := ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
      p hM.le (hzb s hs hsT) (hzn s hs hsT) (hzc s hs hsT)
    let Csup := M * (Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)))
    exact hKint.mul_bdd hQint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ by
        simpa [Csup, Real.norm_eq_abs] using hQbdd y)
  have hQsup_nn : 0 ≤ M * (Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ))) := by
    exact mul_nonneg hM.le (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _))))
  have hQsup : ∀ (z : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ y, |z τ y| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ y, 0 ≤ z τ y) →
      HasContinuousSlices T z →
      ∀ τ, 0 < τ → τ ≤ T → ∀ y,
        |chemFluxLifted p (z τ) y| ≤
          M * (Real.sqrt (∑' k : ℕ,
            (intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ))) := by
    intro z hzb hzn hzc τ hτ hτT y
    exact ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
      p hM.le (hzb τ hτ hτT) (hzn τ hτ hτT) (hzc τ hτ hτT) y
  have hBu := conjugateChemFlux_duhamel_intervalIntegrable_of_ball
    p hM.le hQsup_nn hub hun huc hum (hQsup u hub hun huc) ht htT x
  have hBw := conjugateChemFlux_duhamel_intervalIntegrable_of_ball
    p hM.le hQsup_nn hwb hwn hwc hwm (hQsup w hwb hwn hwc) ht htT x
  have hQdiff2 : ∀ τ, 0 < τ → τ ≤ T → ∀ y,
      |chemFluxLifted p (u τ) y - chemFluxLifted p (w τ) y| ≤
        2 * (M * (Real.sqrt (∑' k : ℕ,
          (intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)))) := by
    intro τ hτ hτT y
    calc
      |chemFluxLifted p (u τ) y - chemFluxLifted p (w τ) y| ≤
          |chemFluxLifted p (u τ) y| + |chemFluxLifted p (w τ) y| := abs_sub _ _
      _ ≤ _ := by
        have huq := hQsup u hub hun huc τ hτ hτT y
        have hwq := hQsup w hwb hwn hwc τ hτ hτT y
        linarith
  have hBdiff := conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball
    p hM.le (by positivity)
    hub hun hwb hwn huc hwc hum hwm hQdiff2 ht htT x
  have hlog := logistic_duhamel_diff_bound_of_ball p hT hM hCL_nn hd_nn hCL_lip
    hub hun hwb hwn huc hwc hum hwm hd ht htT x
  have hbank := intervalConjugateDuhamelMap_diff_bound_of_banked
    p (u₀ := u₀) ht htT x (Dq := CQ * d) (Cv := T * (CL * d))
    (mul_nonneg hCQ_nn hd_nn) hq_diff hq_int_diff
    (hkernel u hub hun huc) (hkernel w hwb hwn hwc) hBu hBw hBdiff hlog
  calc
    |intervalConjugateDuhamelMap p u₀ u t x - intervalConjugateDuhamelMap p u₀ w t x| ≤
        |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * (CQ * d)) +
          T * (CL * d) := hbank
    _ = (|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ) +
          T * CL) * d := by ring

#print axioms intervalConjugateDuhamelMap_diff_bound_of_positive_cone

end ShenWork.IntervalPositiveFloorConjugateContraction

end
