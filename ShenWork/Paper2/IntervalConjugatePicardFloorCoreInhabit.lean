import ShenWork.Paper2.IntervalPositiveFloorConjugateContraction

/-!
# Inhabiting the positive-floor conjugate Picard core

Paper-positive data keep the short-time Picard iterates in a cone bounded away
from zero.  The cone contraction therefore works for all `α,γ > 0`.
-/

open MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 1600000

noncomputable section

namespace ShenWork.IntervalConjugatePicard

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalFullSemigroupOperator_Linfty_bound)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugateChemFluxIntegrable
  (chemFluxLifted_sup_bound_of_ball)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_continuous_of_bounded)
open ShenWork.Paper2
  (PaperPositiveInitialDatum intervalConjugateDuhamelMap_ge_half_floor_of_ball)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz (powerLip powerLip_nonneg)
open ShenWork.IntervalPositiveFloorConjugateContraction
  (intervalConjugateDuhamelMap_diff_bound_of_positive_cone)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.IntervalConjugateBallSupBound
  (conjugateDuhamel_sup_bound_of_ball_univ valueDuhamel_sup_bound_of_ball)
open ShenWork.IntervalMildPicardThreshold
  (intervalFullSemigroupOperator_joint_measurable'
   intervalDomainLift_measurable_of_continuous'
   logisticLifted_joint_measurable')
open ShenWork.IntervalDuhamelIntegrability
  (intervalFullSemigroupOperator_continuous_of_bounded
   chemFluxLifted_integrable_of_continuous)

/-- The positive-floor Picard data exist for every paper-positive initial
datum, with no lower bound `1 ≤ α,γ`. -/
theorem conjugateMildExistenceFloorData_exists
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ D : ConjugateMildExistenceFloorData p u₀, True := by
  classical
  have hadm := PaperPositiveInitialDatum.admissible hu₀
  change BddAbove (Set.range fun x : intervalDomainPoint ↦ |u₀ x|) ∧ Continuous u₀ at hadm
  obtain ⟨hBdd, hu₀_cont⟩ := hadm
  obtain ⟨Braw, hBraw⟩ := hBdd
  set floor : ℝ := paperPositiveFloor hu₀ with hfloor
  have hfloor_pos : 0 < floor := paperPositiveFloor_pos hu₀
  set c : ℝ := floor / 2 with hc
  have hc_pos : 0 < c := by rw [hc]; linarith
  set B0 : ℝ := max (max Braw floor) 1 with hB0
  have hB0_ge_one : (1 : ℝ) ≤ B0 := le_max_right _ _
  have hB0_pos : 0 < B0 := one_pos.trans_le hB0_ge_one
  have hfloor_le_B0 : floor ≤ B0 :=
    (le_max_right Braw floor).trans (le_max_left _ _)
  have hu₀_le_B0 : ∀ x, |u₀ x| ≤ B0 := fun x ↦
    (hBraw (Set.mem_range_self x)).trans
      ((le_max_left Braw floor).trans (le_max_left _ _))
  have hu₀_floor : ∀ x, floor ≤ u₀ x := paperPositiveFloor_le hu₀
  have hu₀_nonneg : ∀ x, 0 ≤ u₀ x := fun x ↦ hfloor_pos.le.trans (hu₀_floor x)
  set M : ℝ := 2 * B0 with hM
  have hM_pos : 0 < M := by rw [hM]; linarith
  have hM_nn : 0 ≤ M := hM_pos.le
  have hB0_le_M : B0 ≤ M := by rw [hM]; linarith
  have hcM : c ≤ M := by rw [hc, hM]; linarith [hfloor_le_B0]
  obtain ⟨CL, hCL_pos, hCL_lip⟩ :=
    ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hM_pos
  have hCL_nn : 0 ≤ CL := hCL_pos.le
  set C_RG : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) with hCRG
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nn _)))
  set CQsup : ℝ := M * C_RG with hCQsup
  have hCQsup_nn : 0 ≤ CQsup := mul_nonneg hM_nn hC_RG_nn
  have hpowLip_nn : 0 ≤ powerLip p.γ c M := powerLip_nonneg p.hγ hc_pos hcM
  set C_RGL : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M)) with hCRGL
  set C_RV : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M)) with hCRV
  have hC_RGL_nn : 0 ≤ C_RGL :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hpowLip_nn))
  have hC_RV_nn : 0 ≤ C_RV :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hpowLip_nn))
  set CQ : ℝ := C_RG + M * C_RGL + M * C_RG * p.β * C_RV with hCQ
  have hCQ_nn : 0 ≤ CQ :=
    add_nonneg (add_nonneg hC_RG_nn (mul_nonneg hM_nn hC_RGL_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg hM_nn hC_RG_nn) p.hβ) hC_RV_nn)
  set CLsup : ℝ := M * (p.a + p.b * M ^ p.α) with hCLsup
  have hCLsup_nn : 0 ≤ CLsup :=
    mul_nonneg hM_nn (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM_nn _)))
  set Cg : ℝ := heatGradientLinftyLinftyConstant with hCg
  have hCg_nn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  set CQmax : ℝ := max CQ CQsup with hCQmax
  have hCQmax_nn : 0 ≤ CQmax := le_max_of_le_left hCQ_nn
  set CLmax : ℝ := max CL CLsup with hCLmax
  have hCLmax_nn : 0 ≤ CLmax := le_max_of_le_left hCL_nn
  set A : ℝ := |p.χ₀| * (Cg * 2 * CQmax) + 1 with hA
  set Bc : ℝ := CLmax + 1 with hBc
  have hA_nn : 0 ≤ A := by
    rw [hA]
    have := mul_nonneg (abs_nonneg p.χ₀)
      (mul_nonneg (mul_nonneg hCg_nn (by norm_num : (0 : ℝ) ≤ 2)) hCQmax_nn)
    linarith
  have hBc_nn : 0 ≤ Bc := by rw [hBc]; linarith
  set δ : ℝ := min 1 (min c B0) with hδ
  have hδ_pos : 0 < δ := lt_min one_pos (lt_min hc_pos hB0_pos)
  obtain ⟨T, hT_pos, hAT⟩ :=
    exists_small_contraction_time_target hA_nn hBc_nn hδ_pos
  have hsqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hbudget_mono : ∀ q l : ℝ, 0 ≤ q → 0 ≤ l → q ≤ CQmax → l ≤ CLmax →
      |p.χ₀| * (Cg * (2 * Real.sqrt T) * q) + T * l ≤
        A * Real.sqrt T + Bc * T := by
    intro q l hq _hl hqle hlle
    have hstep : Cg * (2 * Real.sqrt T) * q ≤ Cg * 2 * CQmax * Real.sqrt T := by
      have hcg2 : 0 ≤ Cg * 2 := by positivity
      nlinarith [mul_nonneg hcg2 hsqrt_nn, hqle, hq, hCg_nn]
    have h1 : |p.χ₀| * (Cg * (2 * Real.sqrt T) * q) ≤
        |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T := by
      calc
        |p.χ₀| * (Cg * (2 * Real.sqrt T) * q) ≤
            |p.χ₀| * (Cg * 2 * CQmax * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
        _ = _ := by ring
    have h2 : T * l ≤ T * CLmax := mul_le_mul_of_nonneg_left hlle hT_pos.le
    rw [hA, hBc]
    nlinarith
  have hK_lt : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) + T * CL < 1 := by
    have hb := hbudget_mono CQ CL hCQ_nn hCL_nn (le_max_left _ _) (le_max_left _ _)
    exact lt_of_le_of_lt hb (hAT.trans_le (min_le_left _ _))
  have hfloor_small : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup ≤
      floor / 2 := by
    have hb := hbudget_mono CQsup CLsup hCQsup_nn hCLsup_nn
      (le_max_right _ _) (le_max_right _ _)
    have hδbound := le_of_lt (hb.trans_lt hAT)
    exact hδbound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmapsto_budget : B0 +
      (|p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup) ≤ M := by
    have hb := hbudget_mono CQsup CLsup hCQsup_nn hCLsup_nn
      (le_max_right _ _) (le_max_right _ _)
    have hcorr : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup ≤ B0 :=
      (le_of_lt (hb.trans_lt hAT)).trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [hM]
    linarith
  have hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ B0 := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact hu₀_le_B0 ⟨y, hy⟩
    · simp; exact hB0_pos.le
  have hLift_nn : ∀ y, 0 ≤ intervalDomainLift u₀ y := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact hu₀_nonneg ⟨y, hy⟩
    · simp
  have hLift_meas : Measurable (intervalDomainLift u₀) :=
    intervalDomainLift_measurable_of_continuous' hu₀_cont
  have hflux_sup_w : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, c ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ τ, 0 < τ → τ ≤ T → ∀ y, |chemFluxLifted p (w τ) y| ≤ CQsup := by
    intro w hwb hwf hwc τ hτ hτT y
    have hwn : ∀ x, 0 ≤ w τ x := fun x ↦ hc_pos.le.trans (hwf τ hτ hτT x)
    have hb := chemFluxLifted_sup_bound_of_ball p hM_nn (hwb τ hτ hτT) hwn
      (hwc τ hτ hτT) y
    simpa [hCQsup, hCRG] using hb
  have hlog_sup_w : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      ∀ τ, 0 < τ → τ ≤ T → ∀ y, |logisticLifted p (w τ) y| ≤ CLsup := by
    intro w hwb τ hτ hτT y
    exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
      p hM_pos (hwb τ hτ hτT) y
  have hPhiB_le : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, c ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x, |intervalConjugateDuhamelMap p u₀ w t x| ≤ M := by
    intro w hwb hwf hwc t ht htT x
    have hwn : ∀ τ, 0 < τ → τ ≤ T → ∀ z, 0 ≤ w τ z := by
      intro τ hτ hτT z
      exact hc_pos.le.trans (hwf τ hτ hτT z)
    have hH := intervalFullSemigroupOperator_Linfty_bound ht hB0_pos.le hLift_bound x.1
    have hB : |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)| ≤
        |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) := by
      rw [abs_mul, abs_neg]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hCg]
      exact conjugateDuhamel_sup_bound_of_ball_univ p hM_nn hCQsup_nn hwb hwn hwc
        (hflux_sup_w w hwb hwf hwc) ht htT x
    have hL := valueDuhamel_sup_bound_of_ball p hM_pos hCLsup_nn hwb
      (hlog_sup_w w hwb) ht htT x
    change |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
      (-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1) +
      ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1| ≤ M
    calc
      _ ≤ (|intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| +
          |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)|) +
          |∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ B0 + (|p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup) := by
        linarith
      _ ≤ M := hmapsto_budget
  have hPhi_floor : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, c ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ intervalConjugateDuhamelMap p u₀ w t x := by
    intro w hwb hwf hwc t ht htT x
    have hwn : ∀ τ, 0 < τ → τ ≤ T → ∀ z, 0 ≤ w τ z := by
      intro τ hτ hτT z
      exact hc_pos.le.trans (hwf τ hτ hτT z)
    have hfloor_le := intervalConjugateDuhamelMap_ge_half_floor_of_ball
      hu₀ hCQsup_nn hCLsup_nn hfloor_small ht htT x
      (conjugateDuhamel_sup_bound_of_ball_univ p hM_nn hCQsup_nn hwb hwn hwc
        (hflux_sup_w w hwb hwf hwc) ht htT x)
      (valueDuhamel_sup_bound_of_ball p hM_pos hCLsup_nn hwb
        (hlog_sup_w w hwb) ht htT x)
    simpa [c, floor] using hfloor_le
  have hcont_preserved_pf : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
      HasContinuousSlices T w → HasJointMeasurability w →
      HasContinuousSlices T (fun t x ↦ intervalConjugateDuhamelMap p u₀ w t x) := by
    intro w hwb hwf hwc hwm
    have hwn : ∀ τ, 0 < τ → τ ≤ T → ∀ z, 0 ≤ w τ z := by
      intro τ hτ hτT z
      exact hc_pos.le.trans (hwf τ hτ hτT z)
    have hQ_meas : Measurable (Function.uncurry (fun s y ↦ chemFluxLifted p (w s) y)) := by
      simpa [Function.uncurry] using
        ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := w) hwm
    have hL_meas : Measurable (Function.uncurry (fun s y ↦ logisticLifted p (w s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' hwm
    have hL_slice_meas : ∀ s,
        AEStronglyMeasurable (logisticLifted p (w s)) (intervalMeasure 1) := fun s ↦
      (hL_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact ShenWork.IntervalConjugateConePreserved.intervalConjugateDuhamelMap_hasContinuousSlices_of_ball
      hB0_pos.le hCQsup_nn hCLsup_nn hLift_bound hLift_meas hQ_meas hL_meas
      (fun s hs hsT ↦ chemFluxLifted_integrable_of_continuous p (hwb s hs hsT) hM_nn
        (hwc s hs hsT) (hwn s hs hsT))
      hL_slice_meas (hflux_sup_w w hwb hwf hwc) (hlog_sup_w w hwb)
  have hmeas_preserved_pf : ∀ w, HasJointMeasurability w →
      HasJointMeasurability (fun t x ↦ intervalConjugateDuhamelMap p u₀ w t x) := by
    intro w hwm
    have hQ_meas : Measurable (Function.uncurry (fun s y ↦ chemFluxLifted p (w s) y)) := by
      simpa [Function.uncurry] using
        ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := w) hwm
    have hL_meas : Measurable (Function.uncurry (fun s y ↦ logisticLifted p (w s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' hwm
    exact ShenWork.IntervalConjugateConePreserved.intervalConjugateDuhamelMap_hasJointMeasurability_of_ball
      hLift_meas hQ_meas hL_meas
  let D : ConjugateMildExistenceFloorData p u₀ := {
    T := T, M := M, c := c
    K := |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) + T * CL
    C₀ := 2 * M
    hT := hT_pos, hM := hM_pos, hc := hc_pos
    hK := hK_lt
    hK_nn := by
      exact add_nonneg
        (mul_nonneg (abs_nonneg _)
          (mul_nonneg (mul_nonneg hCg_nn (mul_nonneg (by norm_num) hsqrt_nn)) hCQ_nn))
        (mul_nonneg hT_pos.le hCL_nn)
    hC₀ := by linarith
    hbase_ball := by
      intro t ht _ x
      simp only [conjugatePicardIter]
      exact (intervalFullSemigroupOperator_Linfty_bound ht hB0_pos.le hLift_bound x.1).trans
        hB0_le_M
    hbase_floor := by
      intro t ht _ x
      have hbase := intervalFullSemigroupOperator_ge_paperPositiveFloor hu₀ ht x.1
      simp only [conjugatePicardIter]
      rw [hc]
      linarith
    hbase_cont := by
      intro t ht _
      simp only [conjugatePicardIter]
      exact (intervalFullSemigroupOperator_continuous_of_bounded ht hB0_pos.le
        hLift_bound hLift_meas.aestronglyMeasurable).comp continuous_subtype_val
    hmapsTo := hPhiB_le
    hmapsTo_floor := hPhi_floor
    hcont_preserved := hcont_preserved_pf
    hcontract := by
      intro u w d hub huf hwb hwf huc hwc hum hwm hd t ht htT x
      have hb := intervalConjugateDuhamelMap_diff_bound_of_positive_cone
        p (u₀ := u₀) (T := T) (M := M) (c := c) (CQ := CQ) (CL := CL)
        hT_pos hM_pos hc_pos hcM
        (by rw [hCQ, hCRG, hCRGL, hCRV]) hCL_nn hCL_lip
        hub huf hwb hwf huc hwc hum hwm hd ht htT x
      simpa [hCg] using hb
    hbase_diff := by
      intro t ht htT x
      have hiter0_ball : ∀ τ, 0 < τ → τ ≤ T → ∀ z,
          |conjugatePicardIter p u₀ 0 τ z| ≤ M := by
        intro τ hτ _ z
        simp only [conjugatePicardIter]
        exact (intervalFullSemigroupOperator_Linfty_bound hτ hB0_pos.le hLift_bound z.1).trans
          hB0_le_M
      have hiter0_floor : ∀ τ, 0 < τ → τ ≤ T → ∀ z,
          c ≤ conjugatePicardIter p u₀ 0 τ z := by
        intro τ hτ _ z
        have hb := intervalFullSemigroupOperator_ge_paperPositiveFloor hu₀ hτ z.1
        simp only [conjugatePicardIter]
        rw [hc]
        linarith
      have hiter0_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0) := by
        intro τ hτ _
        simp only [conjugatePicardIter]
        exact (intervalFullSemigroupOperator_continuous_of_bounded hτ hB0_pos.le
          hLift_bound hLift_meas.aestronglyMeasurable).comp continuous_subtype_val
      have h1 : |conjugatePicardIter p u₀ 1 t x| ≤ M := by
        simp only [conjugatePicardIter]
        exact hPhiB_le _ hiter0_ball hiter0_floor hiter0_cont t ht htT x
      have h0 := hiter0_ball t ht htT x
      calc
        |conjugatePicardIter p u₀ 1 t x - conjugatePicardIter p u₀ 0 t x| ≤
            |conjugatePicardIter p u₀ 1 t x| + |conjugatePicardIter p u₀ 0 t x| := abs_sub _ _
        _ ≤ M + M := add_le_add h1 h0
        _ = 2 * M := by ring
    hbase_meas := by
      have hSg_meas : Measurable (fun q : ℝ × ℝ ↦
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
        intervalFullSemigroupOperator_joint_measurable' hLift_meas
      change Measurable (fun q : ℝ × ℝ ↦
        intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      have heq : (fun q : ℝ × ℝ ↦
          intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) =
          fun q ↦ if q.2 ∈ Set.Icc (0 : ℝ) 1 then
            intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2 else 0 := by
        funext q
        by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1 <;>
          simp [conjugatePicardIter, intervalDomainLift, hy]
      rw [heq]
      exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
        hSg_meas measurable_const
    hmeas_preserved := hmeas_preserved_pf
  }
  exact ⟨D, trivial⟩

theorem conjugateMildSolutionData_exists_all_positive_exponents
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ D : ConjugateMildExistenceFloorData p u₀,
      Nonempty (ConjugateMildSolutionData p u₀) := by
  obtain ⟨D, _⟩ := conjugateMildExistenceFloorData_exists p hu₀
  exact ⟨D, ⟨conjugateMildSolutionData_of_floorData D⟩⟩

#print axioms conjugateMildExistenceFloorData_exists
#print axioms conjugateMildSolutionData_exists_all_positive_exponents

end ShenWork.IntervalConjugatePicard

end
