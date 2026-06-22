/-
  ShenWork/Paper2/IntervalConjugateLogisticDiffBall.lean

  Logistic value-Duhamel difference bound, factored out of the gradient-route
  threshold `hcontr`.  Kernel-independent (uses only the shared
  `intervalFullSemigroupOperator`), so it discharges the conjugate-Core
  `hlogistic_duhamel_diff_bound` field:

    |∫₀ᵗ S(t−s)L(u s) − ∫₀ᵗ S(t−s)L(w s)| ≤ T·(CL·d),

  where `CL` is the logistic Lipschitz constant on `[−M,M]`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalConjugateLogisticDiffBall

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalMildPicardThreshold (logisticLifted_time_cutoff_measurable')

/-- **Logistic value-Duhamel difference bound on the ball.**
`CL` is supplied as the logistic Lipschitz constant valid on `[−M,M]`. -/
theorem logistic_duhamel_diff_bound_of_ball
    (p : CM2Params) {T M CL d : ℝ} (hT : 0 < T) (hM : 0 < M)
    (hCL_nn : 0 ≤ CL) (hd_nn : 0 ≤ d)
    (hCL_lip : ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
      |u₁ * (p.a - p.b * u₁ ^ p.α) - u₂ * (p.a - p.b * u₂ ^ p.α)| ≤ CL * |u₁ - u₂|)
    {u w : ℝ → intervalDomainPoint → ℝ}
    (hub : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M)
    (hun : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x)
    (hwb : ∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M)
    (hwn : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x)
    (huc : HasContinuousSlices T u) (hwc : HasContinuousSlices T w)
    (hum : HasJointMeasurability u) (hwm : HasJointMeasurability w)
    (hd : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    |(∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
      - (∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)|
      ≤ T * (CL * d) := by
  set C_L_val := M * (p.a + p.b * M ^ p.α) with hCLval
  have hC_L_val_nn : 0 ≤ C_L_val :=
    mul_nonneg hM.le (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM.le _)))
  set r_u : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ T then logisticLifted p (u s) y else 0 with hru
  set r_w : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ T then logisticLifted p (w s) y else 0 with hrw
  have hVu_eq : (∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
      = ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r_u s) x.1 := by
    apply intervalIntegral.integral_congr_ae; apply Filter.Eventually.of_forall
    intro s hs; rw [Set.uIoc_of_le ht.le] at hs
    simp only [r_u, if_pos (And.intro hs.1 (hs.2.trans htT))]
  have hVw_eq : (∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
      = ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r_w s) x.1 := by
    apply intervalIntegral.integral_congr_ae; apply Filter.Eventually.of_forall
    intro s hs; rw [Set.uIoc_of_le ht.le] at hs
    simp only [r_w, if_pos (And.intro hs.1 (hs.2.trans htT))]
  rw [hVu_eq, hVw_eq]
  have hCLd_nn : 0 ≤ CL * d := mul_nonneg hCL_nn hd_nn
  -- per-slice source diff bound
  have hr_diff_bound : ∀ s y, |r_u s y - r_w s y| ≤ CL * d := by
    intro s y; simp only [r_u, r_w]
    split_ifs with h
    · unfold logisticLifted intervalDomainLift
        ShenWork.IntervalDomainExistence.intervalLogisticSource
      by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
      · simp only [dif_pos hy]
        have hu_s := hub s h.1 h.2 ⟨y, hy⟩
        have hw_s := hwb s h.1 h.2 ⟨y, hy⟩
        have hd_s := hd s h.1 h.2 ⟨y, hy⟩
        calc |u s ⟨y, hy⟩ * (p.a - p.b * (u s ⟨y, hy⟩) ^ p.α)
                - w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α)|
            ≤ CL * |u s ⟨y, hy⟩ - w s ⟨y, hy⟩| := hCL_lip _ _ hu_s hw_s
          _ ≤ CL * d := mul_le_mul_of_nonneg_left hd_s hCL_nn
      · simp only [dif_neg hy, sub_self, abs_zero]; exact hCLd_nn
    · simp; exact hCLd_nn
  -- per-slice integrability of cutoff sources
  have hr_u_int : ∀ s, Integrable (r_u s) (intervalMeasure 1) := by
    intro s; simp only [r_u]; split_ifs with h
    · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
        p (hub s h.1 h.2) hM.le (huc s h.1 h.2)
    · exact integrable_zero ℝ ℝ (intervalMeasure 1)
  have hr_w_int : ∀ s, Integrable (r_w s) (intervalMeasure 1) := by
    intro s; simp only [r_w]; split_ifs with h
    · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
        p (hwb s h.1 h.2) hM.le (hwc s h.1 h.2)
    · exact integrable_zero ℝ ℝ (intervalMeasure 1)
  -- per-slice sup bounds
  have hr_u_bdd : ∀ s y, |r_u s y| ≤ C_L_val := by
    intro s y; simp only [r_u]; split_ifs with h
    · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p hM (hub s h.1 h.2) y
    · simp; exact hC_L_val_nn
  have hr_w_bdd : ∀ s y, |r_w s y| ≤ C_L_val := by
    intro s y; simp only [r_w]; split_ifs with h
    · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p hM (hwb s h.1 h.2) y
    · simp; exact hC_L_val_nn
  -- both legs IntervalIntegrable via joint measurability
  have hint_u : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (t - s) (r_u s) x.1) volume 0 t :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht (by
        show Measurable (fun q : ℝ × ℝ => r_u q.1 q.2)
        simp only [r_u]
        exact logisticLifted_time_cutoff_measurable' (T := T) hum)
      hC_L_val_nn hr_u_bdd x.1
  have hint_w : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (t - s) (r_w s) x.1) volume 0 t :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht (by
        show Measurable (fun q : ℝ × ℝ => r_w q.1 q.2)
        simp only [r_w]
        exact logisticLifted_time_cutoff_measurable' (T := T) hwm)
      hC_L_val_nn hr_w_bdd x.1
  rw [← intervalIntegral.integral_sub hint_u hint_w]
  have hptw : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)),
      |intervalFullSemigroupOperator (t - s) (r_u s) x.1
        - intervalFullSemigroupOperator (t - s) (r_w s) x.1| ≤ CL * d := by
    have hne : ∀ᵐ s ∂volume, s ≠ t := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hne] with s hs hs_mem
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs)
    exact ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_diff_Linfty_of_integrable
      hst (hr_u_int s) (hr_w_int s) hC_L_val_nn (hr_u_bdd s) hC_L_val_nn
      (hr_w_bdd s) hCLd_nn (hr_diff_bound s) x.1
  calc |∫ s in (0:ℝ)..t, (intervalFullSemigroupOperator (t - s) (r_u s) x.1
          - intervalFullSemigroupOperator (t - s) (r_w s) x.1)|
      ≤ ∫ s in (0:ℝ)..t, |intervalFullSemigroupOperator (t - s) (r_u s) x.1
          - intervalFullSemigroupOperator (t - s) (r_w s) x.1| :=
        intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0:ℝ)..t, (CL * d) :=
        intervalIntegral.integral_mono_ae_restrict ht.le
          (hint_u.sub hint_w).abs intervalIntegrable_const hptw
    _ = t * (CL * d) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    _ ≤ T * (CL * d) := by gcongr

end ShenWork.IntervalConjugateLogisticDiffBall
