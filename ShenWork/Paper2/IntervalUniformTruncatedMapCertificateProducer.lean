import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.Paper2.IntervalConjugateBallSupBound
import ShenWork.Paper2.IntervalConjugateFluxDiffBall
import ShenWork.Paper2.IntervalConjugatePicardBounds
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.Paper2.IntervalTruncatedWindowedSourceMeasurable

open Filter Topology Set MeasureTheory
open scoped Topology

set_option maxHeartbeats 1000000

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateKernelOperator_abs_le)
open ShenWork.IntervalConjugatePicard
  (UniformConjugateMildExistenceCore)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalMildPicardThreshold
  (intervalFullSemigroupOperator_joint_measurable'
   variable_interval_integral_measurable'
   intervalFullSemigroupOperator_s_param_joint_measurable')
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_s_param_joint_measurable
   intervalConjugateKernelOperator_continuous_of_bounded)
open ShenWork.IntervalDuhamelIntegrability
  (chemFluxLifted_integrable_of_continuous
   intervalFullSemigroupOperator_continuous_of_bounded
   valueDuhamel_sup_bound_universal)
open ShenWork.IntervalConjugateChemFluxIntegrable
  (chemFluxLifted_sup_bound_of_ball)
open ShenWork.IntervalConjugateBallSupBound
  (conjugateDuhamel_sup_bound_of_ball_univ)
open ShenWork.Paper2.TruncatedPositiveTimeBootstrap
  (truncatedChemFluxLifted_joint_measurable_of_lift_joint
   truncatedLogisticLifted_joint_measurable_of_lift_joint)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Realization of the two source-sup budgets stored abstractly in the scalar
uniform core.  These equalities are true for the core constructed by
`uniformConjugateMildExistenceCore_exists`, but the scalar structure does not
currently retain them. -/
structure UniformTruncatedSourceSupBudgetRealization
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) : Prop where
  hCQsup_eq :
    C.CQsup = C.R *
      (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * C.R ^ p.γ)))
  hCLsup_eq : C.CLsup = C.R * (p.a + p.b * C.R ^ p.α)
  hCQ_eq : C.CQ =
    Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * C.R ^ p.γ)) +
      C.R * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * (p.γ * C.R ^ (p.γ - 1))))) +
      C.R * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * C.R ^ p.γ))) * p.β *
        (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
            (2 * (p.ν * (p.γ * C.R ^ (p.γ - 1)))))

/-- The two componentwise Duhamel difference estimates still needed after the
source-sup, continuity, and measurability facts have been discharged.  Keeping
these as component bounds, rather than restating full-map contraction, exposes
the exact remaining analytic content. -/
structure UniformTruncatedDuhamelDifferenceCertificate
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) : Prop where
  chemDiff : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.R) →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T u →
    HasContinuousSlices C.T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |(-p.χ₀) *
        ((∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (truncatedChemFluxLifted p (u s)) x.1) -
          (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (truncatedChemFluxLifted p (w s)) x.1))| ≤
        |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt C.T) * (C.CQ * d))
  logisticDiff : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.R) →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
    HasContinuousSlices C.T u →
    HasContinuousSlices C.T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
      |(∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (truncatedLogisticLifted p (u s)) x.1) -
        (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (truncatedLogisticLifted p (w s)) x.1)| ≤
        C.T * (C.CL * d)

theorem truncatedChemFluxLifted_bound_of_realized_budget
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (H : UniformTruncatedSourceSupBudgetRealization p C)
    {w : intervalDomainPoint → ℝ}
    (hwb : ∀ x, |w x| ≤ C.R) (hwc : Continuous w) :
    ∀ y, |truncatedChemFluxLifted p w y| ≤ C.CQsup := by
  intro y
  rw [truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice,
    H.hCQsup_eq]
  exact
    chemFluxLifted_sup_bound_of_ball p C.hR.le
        (fun x => (abs_positivePart_le_abs (w x)).trans (hwb x))
        (positivePartSlice_nonneg w)
        (by
          simpa [positivePartSlice, positivePart] using
            hwc.max continuous_const)
        y

theorem truncatedLogisticLifted_bound_of_realized_budget
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (H : UniformTruncatedSourceSupBudgetRealization p C)
    {w : intervalDomainPoint → ℝ}
    (hwb : ∀ x, |w x| ≤ C.R) :
    ∀ y, |truncatedLogisticLifted p w y| ≤ C.CLsup := by
  intro y
  have hlift : |intervalDomainLift w y| ≤ C.R := by
    unfold intervalDomainLift
    split_ifs with hy
    · exact hwb ⟨y, hy⟩
    · simpa using C.hR.le
  have hpos_le : positivePart (intervalDomainLift w y) ≤ C.R := by
    have habs := abs_positivePart_le_abs (intervalDomainLift w y)
    rw [abs_of_nonneg (positivePart_nonneg _)] at habs
    exact habs.trans hlift
  have hpow_le :
      positivePart (intervalDomainLift w y) ^ p.α ≤ C.R ^ p.α :=
    Real.rpow_le_rpow (positivePart_nonneg _) hpos_le p.hα.le
  have hreaction :
      |p.a - p.b * positivePart (intervalDomainLift w y) ^ p.α| ≤
        p.a + p.b * C.R ^ p.α := by
    calc
      |p.a - p.b * positivePart (intervalDomainLift w y) ^ p.α|
          ≤ |p.a| + |p.b * positivePart (intervalDomainLift w y) ^ p.α| :=
            abs_sub _ _
      _ = p.a + p.b * positivePart (intervalDomainLift w y) ^ p.α := by
        rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb,
          abs_of_nonneg (Real.rpow_nonneg (positivePart_nonneg _) _)]
      _ ≤ p.a + p.b * C.R ^ p.α := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow_le p.hb)
  rw [H.hCLsup_eq]
  simp only [truncatedLogisticLifted, truncatedLogisticLocal, abs_mul]
  exact mul_le_mul hlift hreaction (abs_nonneg _) C.hR.le

/-- Ball-conditional sup estimate for the truncated chemotaxis Duhamel leg. -/
theorem truncatedChemDuhamel_sup_bound_of_realized_budget
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (H : UniformTruncatedSourceSupBudgetRealization p C)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hwb : ∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R)
    (hwc : HasContinuousSlices C.T w)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ C.T)
    (x : intervalDomainPoint) :
    |∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p (w s)) x.1| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt C.T) * C.CQsup := by
  have hfull :=
    conjugateDuhamel_sup_bound_of_ball_univ p C.hR.le C.hCQsup
        (positivePartTrajectory_ball hwb)
        (positivePartTrajectory_nonneg w)
        (positivePartTrajectory_continuous hwc)
        (fun s hs hsT y => by
          change |ShenWork.IntervalGradientDuhamelMap.chemFluxLifted p
            (positivePartSlice (w s)) y| ≤ C.CQsup
          rw [← truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
          exact truncatedChemFluxLifted_bound_of_realized_budget H
            (hwb s hs hsT) (hwc s hs hsT) y)
        ht htT x
  simpa only [positivePartTrajectory,
    ← truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice] using hfull

/-- Ball-conditional sup estimate for the truncated logistic Duhamel leg. -/
theorem truncatedLogisticDuhamel_sup_bound_of_realized_budget
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (H : UniformTruncatedSourceSupBudgetRealization p C)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hwb : ∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ C.T)
    (x : intervalDomainPoint) :
    |∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (w s)) x.1| ≤ C.T * C.CLsup := by
  let r : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ C.T then truncatedLogisticLifted p (w s) y else 0
  have hr_bound : ∀ s y, |r s y| ≤ C.CLsup := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ C.T
    · simpa [r, hs] using
        truncatedLogisticLifted_bound_of_realized_budget H
          (hwb s hs.1 hs.2) y
    · simp [r, hs, C.hCLsup]
  have hint_eq :
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r s) x.1) =
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (truncatedLogisticLifted p (w s)) x.1 := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le ht.le] at hs
      simp [r, hs.1, hs.2.trans htT]
  rw [← hint_eq]
  exact valueDuhamel_sup_bound_universal
    ht htT C.hCLsup hr_bound x.1

/-- The scalar maps-to budget becomes an actual maps-to theorem once its two
stored source-sup constants are tied to the formulas used to choose them. -/
theorem truncatedConjugateDuhamelMap_mapsTo_of_realized_budget
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (H : UniformTruncatedSourceSupBudgetRealization p C)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hwb : ∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R)
    (hwc : HasContinuousSlices C.T w)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ C.T)
    (x : intervalDomainPoint) :
    |truncatedConjugateDuhamelMap p u₀ w t x| ≤ C.R := by
  have hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ C.M0 := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact C.hbase_ball ⟨y, hy⟩
    · simpa using C.hM0.le
  have hbase :
      |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| ≤ C.M0 :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht C.hM0.le hLift_bound x.1
  have hchem := truncatedChemDuhamel_sup_bound_of_realized_budget H hwb hwc ht htT x
  have hchem' :
      |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p (w s)) x.1)| ≤
        |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt C.T) * C.CQsup) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hchem (abs_nonneg _)
  have hlog := truncatedLogisticDuhamel_sup_bound_of_realized_budget H hwb ht htT x
  calc
    |truncatedConjugateDuhamelMap p u₀ w t x| ≤
        |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| +
          |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (truncatedChemFluxLifted p (w s)) x.1)| +
          |∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (w s)) x.1| := by
      simpa only [truncatedConjugateDuhamelMap] using
        (abs_add_le
          (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
            (-p.χ₀) * (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p (w s)) x.1))
          (∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (w s)) x.1)).trans
            (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C.M0 +
        |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt C.T) * C.CQsup) + C.T * C.CLsup :=
      add_le_add (add_le_add hbase hchem') hlog
    _ ≤ C.R := by
      simpa [add_assoc] using C.hmapsTo_budget

/-- Continuous-slice preservation for the faithful truncated map.  The proof
uses the same dominated interval-integral argument as the full conjugate map,
with the two truncated source families substituted explicitly. -/
theorem truncatedConjugateDuhamelMap_hasContinuousSlices_of_realized_budget
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (H : UniformTruncatedSourceSupBudgetRealization p C)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hwb : ∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R)
    (hwc : HasContinuousSlices C.T w)
    (hwm : HasJointMeasurability w) :
    HasContinuousSlices C.T
      (fun t x => truncatedConjugateDuhamelMap p u₀ w t x) := by
  have hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ C.M0 := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact C.hbase_ball ⟨y, hy⟩
    · simpa using C.hM0.le
  have hQ_meas : Measurable
      (Function.uncurry (fun s => truncatedChemFluxLifted p (w s))) :=
    truncatedChemFluxLifted_joint_measurable_of_lift_joint hwm
  have hL_meas : Measurable
      (Function.uncurry (fun s => truncatedLogisticLifted p (w s))) :=
    truncatedLogisticLifted_joint_measurable_of_lift_joint hwm
  have hQ_slice_int : ∀ s, 0 < s → s ≤ C.T →
      Integrable (truncatedChemFluxLifted p (w s)) (intervalMeasure 1) := by
    intro s hs hsT
    rw [truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
    exact
      chemFluxLifted_integrable_of_continuous
        p
        (fun x => (abs_positivePart_le_abs (w s x)).trans (hwb s hs hsT x))
        C.hR.le
        (by
          simpa [positivePartSlice, positivePart] using
            (hwc s hs hsT).max continuous_const)
        (positivePartSlice_nonneg (w s))
  have hL_slice_meas : ∀ s,
      AEStronglyMeasurable (truncatedLogisticLifted p (w s))
        (intervalMeasure 1) := by
    intro s
    exact (hL_meas.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hQ_bound : ∀ s, 0 < s → s ≤ C.T → ∀ y,
      |truncatedChemFluxLifted p (w s) y| ≤ C.CQsup := by
    intro s hs hsT
    exact truncatedChemFluxLifted_bound_of_realized_budget H
      (hwb s hs hsT) (hwc s hs hsT)
  have hL_bound : ∀ s, 0 < s → s ≤ C.T → ∀ y,
      |truncatedLogisticLifted p (w s) y| ≤ C.CLsup := by
    intro s hs hsT
    exact truncatedLogisticLifted_bound_of_realized_budget H (hwb s hs hsT)
  intro t ht htT
  let Cg :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  have hne_t : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hL_joint : Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalFullSemigroupOperator (r.1.1 - r.2)
        (truncatedLogisticLifted p (w r.2)) r.1.2) :=
    intervalFullSemigroupOperator_s_param_joint_measurable' hL_meas
  have hB_joint : Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalConjugateKernelOperator (r.1.1 - r.2)
        (truncatedChemFluxLifted p (w r.2)) r.1.2) :=
    intervalConjugateKernelOperator_s_param_joint_measurable hQ_meas
  have hVal_cont : Continuous (fun x : intervalDomainPoint =>
      ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (w s)) x.1) := by
    refine intervalIntegral.continuous_of_dominated_interval ( μ := volume)
      (F := fun x : intervalDomainPoint => fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (w s)) x.1)
      (bound := fun _ : ℝ => C.CLsup) ?_ ?_ intervalIntegrable_const ?_
    · intro x
      have hmap : Measurable (fun s : ℝ =>
          (((t, x.1), s) : (ℝ × ℝ) × ℝ)) :=
        measurable_const.prodMk measurable_id
      exact (hL_joint.comp hmap).aestronglyMeasurable
    · intro x
      filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      rw [Real.norm_eq_abs]
      exact
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
          hts C.hCLsup (hL_bound s hsI.1 (hsI.2.trans htT)) x.1
    · filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      exact
        (intervalFullSemigroupOperator_continuous_of_bounded
          hts C.hCLsup (hL_bound s hsI.1 (hsI.2.trans htT))
          (hL_slice_meas s)).comp continuous_subtype_val
  have hB_cont : Continuous (fun x : intervalDomainPoint =>
      ∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p (w s)) x.1) := by
    refine intervalIntegral.continuous_of_dominated_interval (μ := volume)
      (F := fun x : intervalDomainPoint => fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p (w s)) x.1)
      (bound := fun s : ℝ => Cg * C.CQsup * (t - s) ^ (-(1 / 2) : ℝ))
      ?_ ?_
      ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
        (Cg * C.CQsup)) ?_
    · intro x
      have hmap : Measurable (fun s : ℝ =>
          (((t, x.1), s) : (ℝ × ℝ) × ℝ)) :=
        measurable_const.prodMk measurable_id
      exact (hB_joint.comp hmap).aestronglyMeasurable
    · intro x
      filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      rw [Real.norm_eq_abs]
      have hb := intervalConjugateKernelOperator_abs_le hts
        (hQ_slice_int s hsI.1 (hsI.2.trans htT))
        (hQ_bound s hsI.1 (hsI.2.trans htT)) x.1
      calc
        |intervalConjugateKernelOperator (t - s)
            (truncatedChemFluxLifted p (w s)) x.1| ≤
            Cg * (t - s) ^ (-(1 / 2) : ℝ) * C.CQsup := by
              simpa [Cg] using hb
        _ = Cg * C.CQsup * (t - s) ^ (-(1 / 2) : ℝ) := by ring
    · filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      exact intervalConjugateKernelOperator_continuous_of_bounded hts
        (hQ_slice_int s hsI.1 (hsI.2.trans htT))
        (hQ_bound s hsI.1 (hsI.2.trans htT))
  have hSg_cont : Continuous (fun x : intervalDomainPoint =>
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1) :=
    (intervalFullSemigroupOperator_continuous_of_bounded
      ht C.hM0.le hLift_bound C.hmeas_preserved.aestronglyMeasurable).comp
      continuous_subtype_val
  change Continuous (fun x : intervalDomainPoint =>
    intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
      (-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p (w s)) x.1) +
      ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (w s)) x.1)
  exact (hSg_cont.add (continuous_const.mul hB_cont)).add hVal_cont

/-- Joint measurability of the faithful truncated Duhamel map. -/
theorem truncatedConjugateDuhamelMap_hasJointMeasurability
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hLift_meas : Measurable (intervalDomainLift u₀))
    {w : ℝ → intervalDomainPoint → ℝ}
    (hwm : HasJointMeasurability w) :
    HasJointMeasurability
      (fun t x => truncatedConjugateDuhamelMap p u₀ w t x) := by
  have hQ_meas : Measurable
      (Function.uncurry (fun s => truncatedChemFluxLifted p (w s))) :=
    truncatedChemFluxLifted_joint_measurable_of_lift_joint hwm
  have hL_meas : Measurable
      (Function.uncurry (fun s => truncatedLogisticLifted p (w s))) :=
    truncatedLogisticLifted_joint_measurable_of_lift_joint hwm
  have hSg_meas : Measurable (fun q : ℝ × ℝ =>
      intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
    intervalFullSemigroupOperator_joint_measurable' hLift_meas
  have hB_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalConjugateKernelOperator (r.1.1 - r.2)
        (truncatedChemFluxLifted p (w r.2)) r.1.2) :=
    intervalConjugateKernelOperator_s_param_joint_measurable hQ_meas
  have hB : Measurable (fun q : ℝ × ℝ =>
      ∫ s in (0 : ℝ)..q.1,
        intervalConjugateKernelOperator (q.1 - s)
          (truncatedChemFluxLifted p (w s)) q.2) :=
    variable_interval_integral_measurable' hB_integrand
  have hL_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalFullSemigroupOperator (r.1.1 - r.2)
        (truncatedLogisticLifted p (w r.2)) r.1.2) :=
    intervalFullSemigroupOperator_s_param_joint_measurable' hL_meas
  have hL : Measurable (fun q : ℝ × ℝ =>
      ∫ s in (0 : ℝ)..q.1,
        intervalFullSemigroupOperator (q.1 - s)
          (truncatedLogisticLifted p (w s)) q.2) :=
    variable_interval_integral_measurable' hL_integrand
  have hinside : Measurable (fun q : ℝ × ℝ =>
      intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
        + (-p.χ₀) * (∫ s in (0 : ℝ)..q.1,
          intervalConjugateKernelOperator (q.1 - s)
            (truncatedChemFluxLifted p (w s)) q.2)
        + ∫ s in (0 : ℝ)..q.1,
          intervalFullSemigroupOperator (q.1 - s)
            (truncatedLogisticLifted p (w s)) q.2) :=
    (hSg_meas.add (measurable_const.mul hB)).add hL
  have hfield :
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomainPoint =>
            truncatedConjugateDuhamelMap p u₀ w q.1 x) q.2) =
      fun q : ℝ × ℝ =>
        if q.2 ∈ Set.Icc (0 : ℝ) 1 then
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
            + (-p.χ₀) * (∫ s in (0 : ℝ)..q.1,
              intervalConjugateKernelOperator (q.1 - s)
                (truncatedChemFluxLifted p (w s)) q.2)
            + ∫ s in (0 : ℝ)..q.1,
              intervalFullSemigroupOperator (q.1 - s)
                (truncatedLogisticLifted p (w s)) q.2
        else 0 := by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [intervalDomainLift, truncatedConjugateDuhamelMap, hy]
    · simp [intervalDomainLift, hy]
  change Measurable (fun q : ℝ × ℝ =>
    intervalDomainLift
      (fun x : intervalDomainPoint =>
        truncatedConjugateDuhamelMap p u₀ w q.1 x) q.2)
  rw [hfield]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
    hinside measurable_const

/-- Assemble full-map contraction from the two named truncated Duhamel
difference estimates. -/
theorem truncatedConjugateDuhamelMap_contraction_of_differenceCertificate
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HD : UniformTruncatedDuhamelDifferenceCertificate p C) :
    ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.R) →
      (∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R) →
      HasContinuousSlices C.T u →
      HasContinuousSlices C.T w →
      HasJointMeasurability u →
      HasJointMeasurability w →
      (∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        |truncatedConjugateDuhamelMap p u₀ u t x
          - truncatedConjugateDuhamelMap p u₀ w t x| ≤ C.K * d := by
  intro u w d hub hwb huc hwc hum hwm hd t ht htT x
  have hchem := HD.chemDiff u w d hub hwb huc hwc hum hwm hd t ht htT x
  have hlog := HD.logisticDiff u w d hub hwb huc hwc hum hwm hd t ht htT x
  have hsplit :
      truncatedConjugateDuhamelMap p u₀ u t x -
          truncatedConjugateDuhamelMap p u₀ w t x =
        (-p.χ₀) *
          ((∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p (u s)) x.1) -
            (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p (w s)) x.1)) +
        ((∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (u s)) x.1) -
          (∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (w s)) x.1)) := by
    simp only [truncatedConjugateDuhamelMap]
    ring
  rw [hsplit]
  calc
    |(-p.χ₀) *
          ((∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p (u s)) x.1) -
            (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p (w s)) x.1)) +
        ((∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (u s)) x.1) -
          (∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (w s)) x.1))| ≤
        |(-p.χ₀) *
          ((∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p (u s)) x.1) -
            (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p (w s)) x.1))| +
        |(∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (u s)) x.1) -
          (∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p (w s)) x.1)| := abs_add_le _ _
    _ ≤ |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt C.T) * (C.CQ * d)) +
        C.T * (C.CL * d) := add_le_add hchem hlog
    _ = C.K * d := by
      rw [C.hK_eq]
      ring

/-- Producer for the faithful truncated-map certificate.  Source sup budgets
are realized by the formulas used in the scalar construction; the only
remaining analytic input is the pair of componentwise Duhamel difference
estimates above. -/
def uniformTruncatedConjugateMapCertificate_of_realizedBudgets
    {p : CM2Params} (_hα : 1 ≤ p.α) (_hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀)
    (HS : UniformTruncatedSourceSupBudgetRealization p C)
    (HD : UniformTruncatedDuhamelDifferenceCertificate p C) :
    UniformTruncatedConjugateMapCertificate p C where
  hmapsTo := by
    intro w hwb hwc t ht htT x
    exact truncatedConjugateDuhamelMap_mapsTo_of_realized_budget
      HS hwb hwc ht htT x
  hcont_preserved := by
    intro w hwb hwc hwm
    exact truncatedConjugateDuhamelMap_hasContinuousSlices_of_realized_budget
      HS hwb hwc hwm
  hcontr :=
    truncatedConjugateDuhamelMap_contraction_of_differenceCertificate HD
  hmeas_preserved := by
    intro w hwm
    exact truncatedConjugateDuhamelMap_hasJointMeasurability
      C.hmeas_preserved hwm

end ShenWork.Paper2.BFormPositiveDatumNegPart
