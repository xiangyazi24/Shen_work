/-
  Duhamel-leg integrability producers for the B-form conjugate Picard limit.

  This file proves the two analytic inputs `hB_int` and `hlog_int` needed by
  `conjugatePicardLimit_hB_global_of_open_sourceBridgeData` from the existing
  `ConjugateMildExistenceData` package.  It does not add headline aliases or
  route wrappers.
-/
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalConjugateLimitDuhamelIntegrability

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugateMildSolutionData_of_data conjugatePicardLimit)
open ShenWork.IntervalConjugateChemFluxIntegrable
  (chemFluxLifted_sup_bound_of_ball
   conjugateChemFlux_duhamel_intervalIntegrable_of_ball)
open ShenWork.IntervalDuhamelIntegrability
  (valueDuhamel_intervalIntegrable_of_joint_measurable)
open ShenWork.IntervalMildPicardThreshold (logisticLifted_joint_measurable')

/-- The Picard-limit ball, nonnegativity, slice-continuity, and joint
measurability package extracted from `ConjugateMildExistenceData`. -/
theorem conjugatePicardLimit_ball_package
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        |conjugatePicardLimit p u₀ D.T t x| ≤ D.M) ∧
    (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        0 ≤ conjugatePicardLimit p u₀ D.T t x) ∧
    HasContinuousSlices D.T (conjugatePicardLimit p u₀ D.T) ∧
    HasJointMeasurability (conjugatePicardLimit p u₀ D.T) := by
  let S := conjugateMildSolutionData_of_data D
  exact ⟨S.hbound, S.hnonneg, S.hcont, S.hmeas⟩

/-- The uniform chemotaxis-flux bound constant for the Picard limit. -/
def limitCQ {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : ℝ :=
  D.M * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * D.M ^ p.γ)))

theorem limitCQ_nonneg {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : 0 ≤ limitCQ D := by
  unfold limitCQ
  exact mul_nonneg D.hM.le
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))

/-- The uniform logistic bound constant for the Picard limit. -/
def limitCL {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : ℝ :=
  D.M * (p.a + p.b * D.M ^ p.α)

theorem limitCL_nonneg {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : 0 ≤ limitCL D :=
  mul_nonneg D.hM.le (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))

/-- Windowed chemotaxis-flux sup bound for the conjugate Picard limit. -/
theorem conjugatePicardLimit_chemFlux_windowBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |chemFluxLifted p (conjugatePicardLimit p u₀ D.T s) y| ≤ limitCQ D := by
  intro s hs hsT y
  obtain ⟨hbound, hnn, hcont, _hmeas⟩ := conjugatePicardLimit_ball_package D
  exact chemFluxLifted_sup_bound_of_ball p D.hM.le
    (hbound s hs hsT) (hnn s hs hsT) (hcont s hs hsT) y

/-- Windowed logistic sup bound for the conjugate Picard limit. -/
theorem conjugatePicardLimit_logistic_windowBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |logisticLifted p (conjugatePicardLimit p u₀ D.T s) y| ≤ limitCL D := by
  intro s hs hsT y
  obtain ⟨hbound, _hnn, _hcont, _hmeas⟩ := conjugatePicardLimit_ball_package D
  exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
    p D.hM (hbound s hs hsT) y

/-- `hB_int` for the conjugate Picard limit from the Picard existence data. -/
theorem conjugatePicardLimit_chemFlux_duhamel_intervalIntegrable_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (conjugatePicardLimit p u₀ D.T s)) x.1)
      volume 0 t := by
  obtain ⟨hbound, hnn, hcont, hmeas⟩ := conjugatePicardLimit_ball_package D
  exact conjugateChemFlux_duhamel_intervalIntegrable_of_ball
    p D.hM.le (limitCQ_nonneg D) hbound hnn hcont hmeas
    (conjugatePicardLimit_chemFlux_windowBound D) ht htT x

/-- `hlog_int` for the conjugate Picard limit from the Picard existence data. -/
theorem conjugatePicardLimit_logistic_duhamel_intervalIntegrable_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (conjugatePicardLimit p u₀ D.T s)) x.1)
      volume 0 t := by
  obtain ⟨_hbound, _hnn, _hcont, hmeas⟩ := conjugatePicardLimit_ball_package D
  set q : ℝ → ℝ → ℝ :=
    fun s yy =>
      if 0 < s ∧ s ≤ D.T then
        logisticLifted p (conjugatePicardLimit p u₀ D.T s) yy
      else 0 with hq
  have hq_meas : Measurable (Function.uncurry q) := by
    have hbase : Measurable
        (fun z : ℝ × ℝ => logisticLifted p (conjugatePicardLimit p u₀ D.T z.1) z.2) :=
      logisticLifted_joint_measurable' hmeas
    simp only [hq]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hq_sup : ∀ s yy, |q s yy| ≤ limitCL D := by
    intro s yy
    simp only [hq]
    split_ifs with h
    · exact conjugatePicardLimit_logistic_windowBound D s h.1 h.2 yy
    · simpa using limitCL_nonneg D
  have hbase_int :=
    valueDuhamel_intervalIntegrable_of_joint_measurable ht hq_meas
      (limitCL_nonneg D) hq_sup x.1
  have hcongr : Set.EqOn
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (q s) x.1)
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (conjugatePicardLimit p u₀ D.T s)) x.1)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hmem : 0 < s ∧ s ≤ D.T := ⟨hs.1, le_trans hs.2 htT⟩
    simp only [hq, if_pos hmem]
  exact hbase_int.congr hcongr

#print axioms conjugatePicardLimit_ball_package
#print axioms conjugatePicardLimit_chemFlux_windowBound
#print axioms conjugatePicardLimit_logistic_windowBound
#print axioms conjugatePicardLimit_chemFlux_duhamel_intervalIntegrable_of_data
#print axioms conjugatePicardLimit_logistic_duhamel_intervalIntegrable_of_data

end ShenWork.IntervalConjugateLimitDuhamelIntegrability

