/-
  ShenWork/Paper2/IntervalDomainMConjugateConePreserved.lean

  Cone preservation for the faithful general-`m` conjugate B-form Duhamel map: continuous-slices and
  joint-measurability are preserved.  Stated as standalone top-level lemmas
  (clean local context) to avoid the `isDefEq` blowup of proving them inline
  inside the heavily-`set` core inhabitant.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalDomainMConjugateConePreserved

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateKernelOperator_abs_le)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (intervalConjugateDuhamelMapM chemFluxMLifted)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_continuous_of_bounded
   intervalConjugateKernelOperator_s_param_joint_measurable)
open ShenWork.IntervalMildPicardThreshold
  (intervalFullSemigroupOperator_joint_measurable'
   variable_interval_integral_measurable'
   intervalFullSemigroupOperator_s_param_joint_measurable')

variable {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}

/-- **Continuous-slices preservation** for the conjugate map.  Inputs: the
homogeneous-leg data (`u₀` lift bounded + measurable, horizon), the uniform
window sup bounds `CQ`, `CL`, the per-slice flux integrability/measurability,
and joint measurability of the two source families. -/
theorem intervalConjugateDuhamelMapM_hasContinuousSlices_of_ball
    {T B0 CQ CL : ℝ} (hB0 : 0 ≤ B0) (hCL : 0 ≤ CL)
    (hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ B0)
    (hLift_meas : Measurable (intervalDomainLift u₀))
    {w : ℝ → intervalDomainPoint → ℝ}
    (hQ_meas : Measurable (Function.uncurry (fun s y => chemFluxMLifted p (w s) y)))
    (hL_meas : Measurable (Function.uncurry (fun s y => logisticLifted p (w s) y)))
    (hQ_slice_int : ∀ s, 0 < s → s ≤ T →
      Integrable (chemFluxMLifted p (w s)) (intervalMeasure 1))
    (hL_slice_meas : ∀ s, AEStronglyMeasurable (logisticLifted p (w s)) (intervalMeasure 1))
    (hQ_bound : ∀ s, 0 < s → s ≤ T → ∀ y : ℝ, |chemFluxMLifted p (w s) y| ≤ CQ)
    (hL_bound : ∀ s, 0 < s → s ≤ T → ∀ y : ℝ, |logisticLifted p (w s) y| ≤ CL) :
    HasContinuousSlices T (fun t x => intervalConjugateDuhamelMapM p u₀ w t x) := by
  intro t ht htT
  set Cg := heatGradientLinftyLinftyConstant with hCg
  have hCg_nn : 0 ≤ Cg := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hne_t : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
  have hL_joint :
      Measurable (fun r : (ℝ × ℝ) × ℝ =>
        intervalFullSemigroupOperator (r.1.1 - r.2) (logisticLifted p (w r.2)) r.1.2) :=
    intervalFullSemigroupOperator_s_param_joint_measurable' hL_meas
  have hB_joint :
      Measurable (fun r : (ℝ × ℝ) × ℝ =>
        intervalConjugateKernelOperator (r.1.1 - r.2) (chemFluxMLifted p (w r.2)) r.1.2) :=
    intervalConjugateKernelOperator_s_param_joint_measurable hQ_meas
  have hVal_cont : Continuous (fun x : intervalDomainPoint =>
      ∫ s in (0 : ℝ)..t, intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1) := by
    refine intervalIntegral.continuous_of_dominated_interval (μ := volume)
      (F := fun x : intervalDomainPoint => fun s : ℝ =>
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
      (bound := fun _ : ℝ => CL) ?_ ?_ intervalIntegrable_const ?_
    · intro x
      have hmap : Measurable (fun s : ℝ => (((t, x.1), s) : (ℝ × ℝ) × ℝ)) :=
        measurable_const.prodMk measurable_id
      exact (hL_joint.comp hmap).aestronglyMeasurable
    · intro x
      filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      rw [Real.norm_eq_abs]
      exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        hts hCL (hL_bound s hsI.1 (hsI.2.trans htT)) x.1
    · filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      exact (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
        hts hCL (hL_bound s hsI.1 (hsI.2.trans htT)) (hL_slice_meas s)).comp continuous_subtype_val
  have hB_cont : Continuous (fun x : intervalDomainPoint =>
      ∫ s in (0 : ℝ)..t, intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1) := by
    refine intervalIntegral.continuous_of_dominated_interval (μ := volume)
      (F := fun x : intervalDomainPoint => fun s : ℝ =>
        intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1)
      (bound := fun s : ℝ => Cg * CQ * (t - s) ^ (-(1 / 2) : ℝ)) ?_ ?_
      (((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
        (Cg * CQ))) ?_
    · intro x
      have hmap : Measurable (fun s : ℝ => (((t, x.1), s) : (ℝ × ℝ) × ℝ)) :=
        measurable_const.prodMk measurable_id
      exact (hB_joint.comp hmap).aestronglyMeasurable
    · intro x
      filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      rw [Real.norm_eq_abs]
      have h := intervalConjugateKernelOperator_abs_le hts
        (hQ_slice_int s hsI.1 (hsI.2.trans htT)) (hQ_bound s hsI.1 (hsI.2.trans htT)) x.1
      calc |intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1|
          ≤ Cg * (t - s) ^ (-(1 / 2) : ℝ) * CQ := by rw [hCg]; exact h
        _ = Cg * CQ * (t - s) ^ (-(1 / 2) : ℝ) := by ring
    · filter_upwards [hne_t] with s hsne hsI
      rw [Set.uIoc_of_le ht.le] at hsI
      have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
      exact intervalConjugateKernelOperator_continuous_of_bounded hts
        (hQ_slice_int s hsI.1 (hsI.2.trans htT)) (hQ_bound s hsI.1 (hsI.2.trans htT))
  have hSg_cont : Continuous (fun x : intervalDomainPoint =>
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1) :=
    (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      ht hB0 hLift_bound hLift_meas.aestronglyMeasurable).comp continuous_subtype_val
  exact ((hSg_cont.add (continuous_const.mul hB_cont)).add hVal_cont)

/-- **Joint-measurability preservation** for the conjugate map. -/
theorem intervalConjugateDuhamelMapM_hasJointMeasurability_of_ball
    (hLift_meas : Measurable (intervalDomainLift u₀))
    {w : ℝ → intervalDomainPoint → ℝ}
    (hQ_meas : Measurable (Function.uncurry (fun s y => chemFluxMLifted p (w s) y)))
    (hL_meas : Measurable (Function.uncurry (fun s y => logisticLifted p (w s) y))) :
    HasJointMeasurability (fun t x => intervalConjugateDuhamelMapM p u₀ w t x) := by
  have hSg_meas : Measurable (fun q : ℝ × ℝ =>
      intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
    intervalFullSemigroupOperator_joint_measurable' hLift_meas
  have hB_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalConjugateKernelOperator (r.1.1 - r.2) (chemFluxMLifted p (w r.2)) r.1.2) :=
    intervalConjugateKernelOperator_s_param_joint_measurable hQ_meas
  have hB : Measurable (fun q : ℝ × ℝ =>
      ∫ s in (0 : ℝ)..q.1,
        intervalConjugateKernelOperator (q.1 - s) (chemFluxMLifted p (w s)) q.2) :=
    variable_interval_integral_measurable' hB_integrand
  have hVal_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalFullSemigroupOperator (r.1.1 - r.2) (logisticLifted p (w r.2)) r.1.2) :=
    intervalFullSemigroupOperator_s_param_joint_measurable' hL_meas
  have hVal : Measurable (fun q : ℝ × ℝ =>
      ∫ s in (0 : ℝ)..q.1,
        intervalFullSemigroupOperator (q.1 - s) (logisticLifted p (w s)) q.2) :=
    variable_interval_integral_measurable' hVal_integrand
  have hinside : Measurable (fun q : ℝ × ℝ =>
      intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
        + (-p.χ₀) * (∫ s in (0 : ℝ)..q.1,
          intervalConjugateKernelOperator (q.1 - s) (chemFluxMLifted p (w s)) q.2)
        + ∫ s in (0 : ℝ)..q.1,
          intervalFullSemigroupOperator (q.1 - s) (logisticLifted p (w s)) q.2) :=
    (hSg_meas.add (measurable_const.mul hB)).add hVal
  have hfield :
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomainPoint => intervalConjugateDuhamelMapM p u₀ w q.1 x) q.2) =
        fun q : ℝ × ℝ =>
          if q.2 ∈ Set.Icc (0 : ℝ) 1 then
            intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
              + (-p.χ₀) * (∫ s in (0 : ℝ)..q.1,
                intervalConjugateKernelOperator (q.1 - s) (chemFluxMLifted p (w s)) q.2)
              + ∫ s in (0 : ℝ)..q.1,
                intervalFullSemigroupOperator (q.1 - s) (logisticLifted p (w s)) q.2
          else 0 := by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [intervalDomainLift, intervalConjugateDuhamelMapM, hy]
    · simp [intervalDomainLift, hy]
  change Measurable (fun q : ℝ × ℝ =>
    intervalDomainLift
      (fun x : intervalDomainPoint => intervalConjugateDuhamelMapM p u₀ w q.1 x) q.2)
  rw [hfield]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd) hinside measurable_const

#print axioms intervalConjugateDuhamelMapM_hasContinuousSlices_of_ball
#print axioms intervalConjugateDuhamelMapM_hasJointMeasurability_of_ball

end ShenWork.IntervalDomainMConjugateConePreserved
