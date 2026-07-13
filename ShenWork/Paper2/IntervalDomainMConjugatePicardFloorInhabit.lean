import ShenWork.PDE.PositiveFloorPicard
import ShenWork.Paper2.IntervalDomainMConjugateMapBounds
import ShenWork.Paper2.IntervalDomainMConjugateConePreserved
import ShenWork.Paper2.IntervalConjugateBallSupBound

/-!
# Positive-floor Picard data for the faithful general-`m` equation

This file instantiates the map-independent positive-floor Picard theorem with
the published flux `u^m v_x / (1+v)^beta`.  The lifespan is selected before
the datum is introduced and therefore depends only on the fixed strip bounds.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.PDE.PositiveFloorPicard
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalFullSemigroupOperator_Linfty_bound
   intervalFullSemigroupOperator_lower_bound)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted intervalConjugateDuhamelMapM IntervalConjugateMildSolutionM
   chemFluxMLifted_abs_le_of_pos_slice chemFluxMLifted_uncurry_measurable
   chemFluxMLifted_integrable_of_pos_slice)
open ShenWork.Paper2.IntervalDomainMConjugateMapBounds
open ShenWork.IntervalDomainMConjugateConePreserved
open ShenWork.IntervalConjugateBallSupBound (valueDuhamel_sup_bound_of_ball)
open ShenWork.IntervalMildPicardThreshold
  (intervalFullSemigroupOperator_joint_measurable'
   intervalDomainLift_measurable_of_continuous'
   logisticLifted_joint_measurable')
open ShenWork.IntervalDuhamelIntegrability
  (intervalFullSemigroupOperator_continuous_of_bounded)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-- Homogeneous starting trajectory for the faithful general-`m` Picard
iteration. -/
def conjugateMBase (u₀ : intervalDomainPoint → ℝ) : Trajectory :=
  fun t x ↦ intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1

/-- Faithful general-`m` nonlinear Picard operator. -/
def conjugateMPhi (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    Trajectory → Trajectory :=
  fun w t x ↦ intervalConjugateDuhamelMapM p u₀ w t x

/-- A genuine mild solution record for the faithful general-`m` B-form map. -/
structure ConjugateMildSolutionDataM (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  hT : 0 < T
  M : ℝ
  hM : 0 < M
  c : ℝ
  hc : 0 < c
  u : Trajectory
  hmild : IntervalConjugateMildSolutionM p T u₀ u
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
  hfloor : ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ u t x
  hcont : HasContinuousSlices T u
  hmeas : HasJointMeasurability u

/-- Uniform positive-strip Picard construction for the published general-`m`
flux.  No lower bounds `1 ≤ m,α,γ` are used. -/
theorem positiveFloorPicardDataM_exists_uniform
    (p : CM2Params) (Braw floor : ℝ) (hfloor_pos : 0 < floor) :
    ∃ T : ℝ, 0 < T ∧
      ∀ u₀ : intervalDomainPoint → ℝ,
        Continuous u₀ →
        (∀ x, |u₀ x| ≤ Braw) →
        (∀ x, floor ≤ u₀ x) →
        ∃ D : PositiveFloorPicardData (conjugateMBase u₀) (conjugateMPhi p u₀),
          D.T = T := by
  classical
  set c : ℝ := floor / 2 with hc
  have hc_pos : 0 < c := by rw [hc]; linarith
  set B0 : ℝ := max (max Braw floor) 1 with hB0
  have hB0_ge_one : (1 : ℝ) ≤ B0 := le_max_right _ _
  have hB0_pos : 0 < B0 := one_pos.trans_le hB0_ge_one
  have hfloor_le_B0 : floor ≤ B0 :=
    (le_max_right Braw floor).trans (le_max_left _ _)
  set M : ℝ := 2 * B0 with hM
  have hM_pos : 0 < M := by rw [hM]; linarith
  have hM_nn : 0 ≤ M := hM_pos.le
  have hB0_le_M : B0 ≤ M := by rw [hM]; linarith
  have hcM : c ≤ M := by rw [hc, hM]; linarith [hfloor_le_B0]
  obtain ⟨CL, hCL_pos, hCL_lip⟩ :=
    ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hM_pos
  have hCL_nn : 0 ≤ CL := hCL_pos.le
  set CQsup : ℝ := chemFluxMSupConstant p M with hCQsup
  have hCQsup_nn : 0 ≤ CQsup := chemFluxMSupConstant_nonneg p hM_nn
  set CQlip : ℝ := chemFluxMLipschitzConstant p c M with hCQlip
  have hCQlip_nn : 0 ≤ CQlip :=
    chemFluxMLipschitzConstant_nonneg p hc_pos hcM
  set CLsup : ℝ := M * (p.a + p.b * M ^ p.α) with hCLsup
  have hCLsup_nn : 0 ≤ CLsup :=
    mul_nonneg hM_nn
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM_nn _)))
  set Cg : ℝ := heatGradientLinftyLinftyConstant with hCg
  have hCg_nn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  set CQmax : ℝ := max CQlip CQsup with hCQmax
  have hCQmax_nn : 0 ≤ CQmax := le_max_of_le_left hCQlip_nn
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
  refine ⟨T, hT_pos, ?_⟩
  intro u₀ hu₀_cont hBraw hu₀_floor
  have hu₀_le_B0 : ∀ x, |u₀ x| ≤ B0 := fun x ↦
    (hBraw x).trans ((le_max_left Braw floor).trans (le_max_left _ _))
  have hu₀_nonneg : ∀ x, 0 ≤ u₀ x := fun x ↦
    hfloor_pos.le.trans (hu₀_floor x)
  have hsqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hbudget_mono : ∀ q l : ℝ, 0 ≤ q → 0 ≤ l → q ≤ CQmax → l ≤ CLmax →
      |p.χ₀| * (Cg * (2 * Real.sqrt T) * q) + T * l ≤
        A * Real.sqrt T + Bc * T := by
    intro q l hq _hl hqle hlle
    have hstep : Cg * (2 * Real.sqrt T) * q ≤
        Cg * 2 * CQmax * Real.sqrt T := by
      have hcg2 : 0 ≤ Cg * 2 := by positivity
      nlinarith [mul_nonneg hcg2 hsqrt_nn, hqle, hq, hCg_nn]
    have h1 : |p.χ₀| * (Cg * (2 * Real.sqrt T) * q) ≤
        |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T := by
      calc
        |p.χ₀| * (Cg * (2 * Real.sqrt T) * q) ≤
            |p.χ₀| * (Cg * 2 * CQmax * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
        _ = _ := by ring
    have h2 : T * l ≤ T * CLmax :=
      mul_le_mul_of_nonneg_left hlle hT_pos.le
    rw [hA, hBc]
    nlinarith
  have hK_lt : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQlip) + T * CL < 1 := by
    have hb := hbudget_mono CQlip CL hCQlip_nn hCL_nn
      (le_max_left _ _) (le_max_left _ _)
    exact lt_of_le_of_lt hb (hAT.trans_le (min_le_left _ _))
  have hfloor_small :
      |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup ≤ floor / 2 := by
    have hb := hbudget_mono CQsup CLsup hCQsup_nn hCLsup_nn
      (le_max_right _ _) (le_max_right _ _)
    have hδbound := le_of_lt (hb.trans_lt hAT)
    exact hδbound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmapsto_budget : B0 +
      (|p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup) ≤ M := by
    have hb := hbudget_mono CQsup CLsup hCQsup_nn hCLsup_nn
      (le_max_right _ _) (le_max_right _ _)
    have hcorr : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup ≤ B0 :=
      (le_of_lt (hb.trans_lt hAT)).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    rw [hM]
    linarith
  have hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ B0 := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact hu₀_le_B0 ⟨y, hy⟩
    · simpa using hB0_pos.le
  have hLift_meas : Measurable (intervalDomainLift u₀) :=
    intervalDomainLift_measurable_of_continuous' hu₀_cont
  have hsemigroup_floor : ∀ t, 0 < t → ∀ y,
      floor ≤ intervalFullSemigroupOperator t (intervalDomainLift u₀) y := by
    intro t ht y
    exact intervalFullSemigroupOperator_lower_bound ht hfloor_pos.le hfloor_le_B0
      hLift_meas.aestronglyMeasurable
      (fun z hz ↦ by
        simpa [intervalDomainLift, hz] using hu₀_floor ⟨z, hz⟩)
      hLift_bound y
  have hflux_sup_w : ∀ (w : Trajectory),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, c ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ τ, 0 < τ → τ ≤ T → ∀ y,
        |chemFluxMLifted p (w τ) y| ≤ CQsup := by
    intro w hwb hwf hwc τ hτ hτT y
    simpa [hCQsup, chemFluxMSupConstant] using
      chemFluxMLifted_abs_le_of_pos_slice p hc_pos hcM
        (hwb τ hτ hτT) (hwf τ hτ hτT) (hwc τ hτ hτT) y
  have hlog_sup_w : ∀ (w : Trajectory),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      ∀ τ, 0 < τ → τ ≤ T → ∀ y,
        |logisticLifted p (w τ) y| ≤ CLsup := by
    intro w hwb τ hτ hτT y
    exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
      p hM_pos (hwb τ hτ hτT) y
  have hPhiB_le : ∀ (w : Trajectory),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, c ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x, |conjugateMPhi p u₀ w t x| ≤ M := by
    intro w hwb hwf hwc t ht htT x
    have hH := intervalFullSemigroupOperator_Linfty_bound
      ht hB0_pos.le hLift_bound x.1
    have hB : |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1)| ≤
        |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) := by
      rw [abs_mul, abs_neg]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hCg]
      exact conjugateMDuhamel_sup_bound_of_positive_cone_univ
        p hc_pos hcM hCQsup_nn hwb hwf hwc
        (hflux_sup_w w hwb hwf hwc) ht htT x
    have hL := valueDuhamel_sup_bound_of_ball p hM_pos hCLsup_nn hwb
      (hlog_sup_w w hwb) ht htT x
    change |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
      (-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1) +
      ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1| ≤ M
    calc
      _ ≤ (|intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| +
          |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1)|) +
          |∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ B0 + (|p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup) := by
        linarith
      _ ≤ M := hmapsto_budget
  have hPhi_floor : ∀ (w : Trajectory),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, c ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ conjugateMPhi p u₀ w t x := by
    intro w hwb hwf hwc t ht htT x
    have hB := conjugateMDuhamel_sup_bound_of_positive_cone_univ
      p hc_pos hcM hCQsup_nn hwb hwf hwc
      (hflux_sup_w w hwb hwf hwc) ht htT x
    have hL := valueDuhamel_sup_bound_of_ball p hM_pos hCLsup_nn hwb
      (hlog_sup_w w hwb) ht htT x
    let corr := (-p.χ₀) * (∫ s in (0 : ℝ)..t,
      intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1) +
      ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1
    have hcorr : |corr| ≤
        |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup := by
      dsimp [corr]
      calc
        _ ≤ |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (w s)) x.1)| +
            |∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s)
                (logisticLifted p (w s)) x.1| := abs_add_le _ _
        _ ≤ _ := add_le_add
          (by simpa [abs_mul, hCg] using
            mul_le_mul_of_nonneg_left hB (abs_nonneg p.χ₀)) hL
    have hcorr_lower :
        -( |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup) ≤ corr :=
      neg_le_of_abs_le hcorr
    have hPhi : conjugateMPhi p u₀ w t x =
        intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 + corr := by
      simp only [conjugateMPhi, intervalConjugateDuhamelMapM]
      dsimp [corr]
      ring
    rw [hPhi]
    rw [hc]
    linarith [hsemigroup_floor t ht x.1, hfloor_small]
  have hcont_preserved_pf : ∀ (w : Trajectory),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
      HasContinuousSlices T w → HasJointMeasurability w →
      HasContinuousSlices T (conjugateMPhi p u₀ w) := by
    intro w hwb hwf hwc hwm
    have hQ_meas : Measurable
        (Function.uncurry (fun s y ↦ chemFluxMLifted p (w s) y)) := by
      simpa [Function.uncurry] using
        chemFluxMLifted_uncurry_measurable (p := p) (u := w) hwm
    have hL_meas : Measurable
        (Function.uncurry (fun s y ↦ logisticLifted p (w s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' hwm
    have hL_slice_meas : ∀ s,
        AEStronglyMeasurable (logisticLifted p (w s)) (intervalMeasure 1) :=
      fun s ↦
        (hL_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact intervalConjugateDuhamelMapM_hasContinuousSlices_of_ball
      hB0_pos.le hCLsup_nn hLift_bound hLift_meas hQ_meas hL_meas
      (fun s hs hsT ↦ chemFluxMLifted_integrable_of_pos_slice p hc_pos hcM
        (hwb s hs hsT) (hwf s hs hsT) (hwc s hs hsT))
      hL_slice_meas (hflux_sup_w w hwb hwf hwc) (hlog_sup_w w hwb)
  have hmeas_preserved_pf : ∀ w, HasJointMeasurability w →
      HasJointMeasurability (conjugateMPhi p u₀ w) := by
    intro w hwm
    have hQ_meas : Measurable
        (Function.uncurry (fun s y ↦ chemFluxMLifted p (w s) y)) := by
      simpa [Function.uncurry] using
        chemFluxMLifted_uncurry_measurable (p := p) (u := w) hwm
    have hL_meas : Measurable
        (Function.uncurry (fun s y ↦ logisticLifted p (w s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' hwm
    exact intervalConjugateDuhamelMapM_hasJointMeasurability_of_ball
      hLift_meas hQ_meas hL_meas
  let D : PositiveFloorPicardData (conjugateMBase u₀) (conjugateMPhi p u₀) := {
    T := T, M := M, c := c
    K := |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQlip) + T * CL
    C₀ := 2 * M
    hT := hT_pos, hM := hM_pos, hc := hc_pos
    hK := hK_lt
    hK_nn := by
      exact add_nonneg
        (mul_nonneg (abs_nonneg _)
          (mul_nonneg
            (mul_nonneg hCg_nn (mul_nonneg (by norm_num) hsqrt_nn)) hCQlip_nn))
        (mul_nonneg hT_pos.le hCL_nn)
    hC₀ := by linarith
    hbase_ball := by
      intro t ht _ x
      exact (intervalFullSemigroupOperator_Linfty_bound
        ht hB0_pos.le hLift_bound x.1).trans hB0_le_M
    hbase_floor := by
      intro t ht _ x
      dsimp [conjugateMBase]
      rw [hc]
      linarith [hsemigroup_floor t ht x.1]
    hbase_cont := by
      intro t ht _
      exact (intervalFullSemigroupOperator_continuous_of_bounded ht hB0_pos.le
        hLift_bound hLift_meas.aestronglyMeasurable).comp continuous_subtype_val
    hbase_meas := by
      have hSg_meas : Measurable (fun q : ℝ × ℝ ↦
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
        intervalFullSemigroupOperator_joint_measurable' hLift_meas
      change Measurable (fun q : ℝ × ℝ ↦
        intervalDomainLift (conjugateMBase u₀ q.1) q.2)
      have heq : (fun q : ℝ × ℝ ↦
          intervalDomainLift (conjugateMBase u₀ q.1) q.2) =
          fun q ↦ if q.2 ∈ Set.Icc (0 : ℝ) 1 then
            intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2 else 0 := by
        funext q
        by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1 <;>
          simp [conjugateMBase, intervalDomainLift, hy]
      rw [heq]
      exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
        hSg_meas measurable_const
    hmapsTo := hPhiB_le
    hmapsTo_floor := hPhi_floor
    hcont_preserved := hcont_preserved_pf
    hmeas_preserved := hmeas_preserved_pf
    hcontract := by
      intro u w d hub huf hwb hwf huc hwc hum hwm hd t ht htT x
      simpa [conjugateMPhi, hCg, hCQlip] using
        intervalConjugateDuhamelMapM_diff_bound_of_positive_cone
          p (u₀ := u₀) hT_pos hc_pos hcM hCL_nn hCL_lip
          hub huf hwb hwf huc hwc hum hwm hd ht htT x
    hbase_diff := by
      intro t ht htT x
      change |conjugateMPhi p u₀ (conjugateMBase u₀) t x -
        conjugateMBase u₀ t x| ≤ 2 * M
      have h0 := (intervalFullSemigroupOperator_Linfty_bound
        ht hB0_pos.le hLift_bound x.1).trans hB0_le_M
      have h0' : |conjugateMBase u₀ t x| ≤ M := by
        simpa [conjugateMBase] using h0
      have h1 : |conjugateMPhi p u₀ (conjugateMBase u₀) t x| ≤ M := by
        exact hPhiB_le _
          (fun τ hτ _ z ↦ (intervalFullSemigroupOperator_Linfty_bound
            hτ hB0_pos.le hLift_bound z.1).trans hB0_le_M)
          (fun τ hτ _ z ↦ by
            rw [hc]
            linarith [hsemigroup_floor τ hτ z.1])
          (fun τ hτ _ ↦
            (intervalFullSemigroupOperator_continuous_of_bounded hτ hB0_pos.le
              hLift_bound hLift_meas.aestronglyMeasurable).comp
                continuous_subtype_val)
          t ht htT x
      calc
        |conjugateMPhi p u₀ (conjugateMBase u₀) t x -
            conjugateMBase u₀ t x| ≤
            |conjugateMPhi p u₀ (conjugateMBase u₀) t x| +
              |conjugateMBase u₀ t x| := abs_sub _ _
        _ ≤ M + M := add_le_add h1 h0'
        _ = 2 * M := by ring
  }
  exact ⟨D, rfl⟩

/-- Package the generic fixed point as the faithful general-`m` mild solution
record. -/
def conjugateMildSolutionDataM_of_picardData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : PositiveFloorPicardData (conjugateMBase u₀) (conjugateMPhi p u₀)) :
    ConjugateMildSolutionDataM p u₀ := by
  let F := fixedPointData D
  exact {
    T := F.T, hT := F.hT, M := F.M, hM := F.hM, c := F.c, hc := F.hc
    u := F.u
    hmild := by
      intro t ht htT x
      simpa [conjugateMPhi] using F.hfixed t ht htT x
    hbound := F.hbound
    hfloor := F.hfloor
    hcont := F.hcont
    hmeas := F.hmeas }

/-- Every paper-positive datum for the faithful domain has a genuine
general-`m` mild solution. -/
theorem conjugateMildSolutionDataM_exists_paperPositive
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    Nonempty (ConjugateMildSolutionDataM p u₀) := by
  obtain ⟨Braw, hBraw⟩ := hu₀.admissible.1
  let floor : ℝ := hu₀.floor.choose
  have hfloor_pos : 0 < floor := hu₀.floor.choose_spec.1
  have hfloor_le : ∀ x, floor ≤ u₀ x := hu₀.floor.choose_spec.2
  obtain ⟨T, _hT, hfactory⟩ :=
    positiveFloorPicardDataM_exists_uniform p Braw floor hfloor_pos
  obtain ⟨D, _hDT⟩ := hfactory u₀ hu₀.admissible.2
    (fun x ↦ hBraw (Set.mem_range_self x)) hfloor_le
  exact ⟨conjugateMildSolutionDataM_of_picardData D⟩

#print axioms positiveFloorPicardDataM_exists_uniform
#print axioms conjugateMildSolutionDataM_of_picardData
#print axioms conjugateMildSolutionDataM_exists_paperPositive

end ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
