/-
  ShenWork/Paper2/IntervalConjugatePicardCoreInhabit.lean

  Inhabitation of `ConjugateMildExistenceCore p u₀` for a paper-positive initial
  datum.  All structure fields are discharged from the landed analytic atoms:
    * `hmapsTo`            ← intervalConjugateDuhamelMap_mapsTo_of_banked
    * `hmapsTo_nn/_pos`    ← intervalConjugateDuhamelMap_ge_half_floor_of_ball
    * `hcont_preserved`    ← intervalConjugateKernelOperator_continuous_of_bounded
                              + intervalFullSemigroupOperator_continuous_of_bounded
    * `hmeas_preserved`    ← intervalConjugateKernelOperator_s_param_joint_measurable
                              + variable_interval_integral_measurable'
    * `hflux_*`            ← conjugateChemFlux_duhamel_intervalIntegrable_of_ball (+diff)
    * `hflux_diff_bound`   ← chemFluxLifted_diff_bound_of_ball_slice
    * `hlogistic_..._bound`← logistic_duhamel_diff_bound_of_ball
    * base fields          ← heat-semigroup sup / nonneg / continuity / measurability
  The horizon `T` is shrunk by `exists_small_contraction_time_target` so that the
  contraction constant `K < 1` and the floor smallness hold simultaneously.

  STATUS: 26/30 Core fields fully discharged (axiom-clean).  The remaining 4
  obligations are the OFF-WINDOW (`s ∉ (0,T]`) branches of the four raw-flux
  fields `hflux_diff_bound`, `hflux_diff_integrable`,
  `hflux_kernel_integrable_left/right`.  These fields are typed `∀ s`
  (unconditional) in `ConjugateMildExistenceCore`, inherited from the
  `∀ s` feeders of the already-proven `contraction_from_banked`; but
  `chemFluxLifted p (u s)` is only bounded/integrable when `u s` is a bounded
  continuous slice, which the ball trajectory provides only on `(0,T]`.  The
  Those four Core fields are now restricted to `∀ s, 0 < s → s ≤ T → ...`,
  matching the integration window `(0,T]`, so the on-window proofs discharge
  them directly with no off-window case remaining.
-/
import ShenWork.Paper2.IntervalConjugatePicardCoreDischarge
import ShenWork.Paper2.IntervalConjugateHmapsToPos
import ShenWork.Paper2.IntervalConjugateCoreHmapsTo
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.Paper2.IntervalConjugateFluxDiffBall
import ShenWork.Paper2.IntervalConjugateLogisticDiffBall
import ShenWork.Paper2.IntervalConjugateBallSupBound
import ShenWork.Paper2.IntervalConjugateConePreserved
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 1600000

noncomputable section

namespace ShenWork.IntervalConjugatePicard

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel
   intervalFullSemigroupOperator_Linfty_bound)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugatePicardBounds (intervalConjugateDuhamelMap_mapsTo_of_banked)
open ShenWork.IntervalConjugateChemFluxIntegrable
  (chemFluxLifted_sup_bound_of_ball conjugateChemFlux_duhamel_intervalIntegrable_of_ball
   conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_continuous_of_bounded
   intervalConjugateKernelOperator_s_param_joint_measurable)
open ShenWork.Paper2 (intervalConjugateDuhamelMap_ge_half_floor_of_ball)
open ShenWork.IntervalConjugateFluxDiffBall (chemFluxLifted_diff_bound_of_ball_slice)
open ShenWork.IntervalConjugateLogisticDiffBall (logistic_duhamel_diff_bound_of_ball)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.IntervalConjugateBallSupBound
  (conjugateDuhamel_sup_bound_of_ball conjugateDuhamel_sup_bound_of_ball_univ
   valueDuhamel_sup_bound_of_ball)
open ShenWork.IntervalMildPicardThreshold
  (intervalFullSemigroupOperator_joint_measurable'
   variable_interval_integral_measurable'
   intervalFullSemigroupOperator_s_param_joint_measurable'
   intervalDomainLift_measurable_of_continuous'
   logisticLifted_joint_measurable')
open ShenWork.IntervalDuhamelIntegrability
  (intervalFullSemigroupOperator_continuous_of_bounded
   logisticLifted_integrable_of_continuous
   chemFluxLifted_integrable_of_continuous)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

/-- The conjugate Picard core is inhabited for every paper-positive datum
(under the paper standing assumptions `1 ≤ α`, `1 ≤ γ`), for a sufficiently
small horizon. -/
theorem conjugateMildExistenceCore_exists
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ T : ℝ, Nonempty (ConjugateMildExistenceCore p u₀) ∧ 0 < T := by
  classical
  -- datum data: continuity + boundedness + positive floor
  have hadm := PaperPositiveInitialDatum.admissible hu₀
  change BddAbove (Set.range fun x : intervalDomainPoint => |u₀ x|)
      ∧ Continuous u₀ at hadm
  obtain ⟨hBdd, hu₀_cont⟩ := hadm
  obtain ⟨Braw, hBraw⟩ := hBdd
  set floor : ℝ := paperPositiveFloor hu₀ with hfloor
  have hfloor_pos : 0 < floor := paperPositiveFloor_pos hu₀
  -- a clean sup bound `B0 ≥ |u₀|`, `B0 ≥ floor`, `B0 ≥ 1`
  set B0 : ℝ := max (max Braw floor) 1 with hB0
  have hB0_ge_one : (1 : ℝ) ≤ B0 := le_max_right _ _
  have hB0_pos : 0 < B0 := lt_of_lt_of_le one_pos hB0_ge_one
  have hu₀_le_B0 : ∀ x, |u₀ x| ≤ B0 := fun x =>
    le_trans (hBraw (Set.mem_range_self x))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hu₀_nonneg : ∀ x, 0 ≤ u₀ x := fun x =>
    le_trans hfloor_pos.le (paperPositiveFloor_le hu₀ x)
  -- ball radius
  set M : ℝ := 2 * B0 with hM
  have hM_pos : 0 < M := by rw [hM]; linarith
  have hM_nn : 0 ≤ M := hM_pos.le
  have hB0_le_M : B0 ≤ M := by rw [hM]; linarith
  -- logistic Lipschitz constant on [-M,M]
  obtain ⟨CL, hCL_pos, hCL_lip⟩ :=
    ShenWork.IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_bounded
      p hα_ge hM_pos
  have hCL_nn : 0 ≤ CL := hCL_pos.le
  -- uniform flux sup constant from the ball bound:  CQsup = M·C_RG
  set C_RG : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)) with hCRG
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nn _)))
  set CQsup : ℝ := M * C_RG with hCQsup
  have hCQsup_nn : 0 ≤ CQsup := mul_nonneg hM_nn hC_RG_nn
  -- flux Lipschitz constant (the Core CQ field)
  set C_RGL : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
    * (2 * (p.ν * (p.γ * M ^ (p.γ - 1)))) with hCRGL
  set C_RV : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
    * (2 * (p.ν * (p.γ * M ^ (p.γ - 1)))) with hCRV
  have hC_RGL_nn : 0 ≤ C_RGL :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le
        (mul_nonneg p.hγ.le (Real.rpow_nonneg hM_nn _))))
  have hC_RV_nn : 0 ≤ C_RV :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le
        (mul_nonneg p.hγ.le (Real.rpow_nonneg hM_nn _))))
  set CQ : ℝ := C_RG + M * C_RGL + M * C_RG * p.β * C_RV with hCQ
  have hCQ_nn : 0 ≤ CQ :=
    add_nonneg (add_nonneg hC_RG_nn (mul_nonneg hM_nn hC_RGL_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg hM_nn hC_RG_nn) p.hβ) hC_RV_nn)
  -- logistic sup constant (for the floor/mapsTo budget)
  set CLsup : ℝ := M * (p.a + p.b * M ^ p.α) with hCLsup
  have hCLsup_nn : 0 ≤ CLsup :=
    mul_nonneg hM_nn (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM_nn _)))
  -- abbreviation for the heat-gradient constant
  set Cg : ℝ := heatGradientLinftyLinftyConstant with hCg
  have hCg_nn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  -- combined budget constants: pick one (A,B) dominating ALL needs
  set CQmax : ℝ := max CQ CQsup with hCQmax
  have hCQmax_nn : 0 ≤ CQmax := le_max_of_le_left hCQ_nn
  set CLmax : ℝ := max CL CLsup with hCLmax
  have hCLmax_nn : 0 ≤ CLmax := le_max_of_le_left hCL_nn
  set A : ℝ := |p.χ₀| * (Cg * 2 * CQmax) + 1 with hA
  set Bc : ℝ := CLmax + 1 with hBc
  have hA_nn : 0 ≤ A := by
    rw [hA]; have := mul_nonneg (abs_nonneg p.χ₀)
      (mul_nonneg (mul_nonneg hCg_nn (by norm_num : (0:ℝ) ≤ 2)) hCQmax_nn); linarith
  have hBc_nn : 0 ≤ Bc := by rw [hBc]; linarith
  -- target: smaller than 1, floor/2 and B0 (=M/2)
  set δ : ℝ := min 1 (min (floor / 2) B0) with hδ
  have hδ_pos : 0 < δ := lt_min one_pos (lt_min (by linarith) hB0_pos)
  obtain ⟨T, hT_pos, hAT⟩ := exists_small_contraction_time_target hA_nn hBc_nn hδ_pos
  -- The Core's `hK_eq` form: |χ₀|·Cg·(2√T)·CQ + T·CL.
  -- Show it is < 1 (hence ≤ 1, but Core asks K < 1).
  have h2sqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  -- monotone helper: any chem-coeff ≤ CQmax, log-coeff ≤ CLmax gives
  --   |χ₀|·Cg·2√T·c + T·l ≤ A·√T + Bc·T  (when c ≤ CQmax, l ≤ CLmax)
  have hbudget_mono : ∀ c l : ℝ, 0 ≤ c → 0 ≤ l → c ≤ CQmax → l ≤ CLmax →
      |p.χ₀| * (Cg * (2 * Real.sqrt T) * c) + T * l ≤ A * Real.sqrt T + Bc * T := by
    intro c l hc hl hcle hlle
    have h1 : |p.χ₀| * (Cg * (2 * Real.sqrt T) * c) ≤ |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T := by
      have hstep : Cg * (2 * Real.sqrt T) * c ≤ Cg * 2 * CQmax * Real.sqrt T := by
        have hcg2 : 0 ≤ Cg * 2 := by positivity
        nlinarith [mul_nonneg hcg2 h2sqrt_nn, hcle, hc, hCg_nn]
      calc |p.χ₀| * (Cg * (2 * Real.sqrt T) * c)
          ≤ |p.χ₀| * (Cg * 2 * CQmax * Real.sqrt T) :=
            mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
        _ = |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T := by ring
    have h2 : T * l ≤ T * CLmax := mul_le_mul_of_nonneg_left hlle hT_pos.le
    calc |p.χ₀| * (Cg * (2 * Real.sqrt T) * c) + T * l
        ≤ |p.χ₀| * (Cg * 2 * CQmax) * Real.sqrt T + T * CLmax := by linarith
      _ ≤ A * Real.sqrt T + Bc * T := by
          rw [hA, hBc]; nlinarith [h2sqrt_nn, hT_pos.le, hCLmax_nn]
  -- K = the hK_eq form with CQ, CL.
  have hK_lt_one : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) + T * CL < 1 := by
    have hb := hbudget_mono CQ CL hCQ_nn hCL_nn (le_max_left _ _) (le_max_left _ _)
    have := lt_of_le_of_lt hb hAT
    exact lt_of_lt_of_le this (le_trans (min_le_left _ _) le_rfl)
  have hfloor_small : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup ≤ floor / 2 := by
    have hb := hbudget_mono CQsup CLsup hCQsup_nn hCLsup_nn (le_max_right _ _) (le_max_right _ _)
    have := le_of_lt (lt_of_le_of_lt hb hAT)
    exact le_trans this (le_trans (min_le_right _ _) (min_le_left _ _))
  -- the budget for the maps-to (≤M) bound:  B0 + correction ≤ M = 2·B0
  have hmapsto_budget : B0 + (|p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup) ≤ M := by
    have hcorr : |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) + T * CLsup ≤ B0 := by
      have hb := hbudget_mono CQsup CLsup hCQsup_nn hCLsup_nn (le_max_right _ _) (le_max_right _ _)
      have := le_of_lt (lt_of_le_of_lt hb hAT)
      exact le_trans this (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [hM]; linarith
  -- lift bound + measurability for the base heat iterate
  have hLift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ B0 := by
    intro y; unfold intervalDomainLift; split_ifs with hy
    · exact hu₀_le_B0 ⟨y, hy⟩
    · simp; exact hB0_pos.le
  have hLift_nn : ∀ y, 0 ≤ intervalDomainLift u₀ y := by
    intro y; unfold intervalDomainLift; split_ifs with hy
    · exact hu₀_nonneg ⟨y, hy⟩
    · simp
  have hLift_meas : Measurable (intervalDomainLift u₀) :=
    intervalDomainLift_measurable_of_continuous' hu₀_cont
  -- per-w sup bounds (chem flux uniform CQsup; logistic uniform CLsup)
  have hflux_sup_w : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ τ, 0 < τ → τ ≤ T → ∀ y, |chemFluxLifted p (w τ) y| ≤ CQsup := by
    intro w hwb hwn hwc τ hτ hτT y
    have := chemFluxLifted_sup_bound_of_ball p hM_nn (hwb τ hτ hτT) (hwn τ hτ hτT)
      (hwc τ hτ hτT) y
    simpa [hCQsup, hCRG] using this
  have hlog_sup_w : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      ∀ τ, 0 < τ → τ ≤ T → ∀ y, |logisticLifted p (w τ) y| ≤ CLsup := by
    intro w hwb τ hτ hτT y
    exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
      p hM_pos (hwb τ hτ hτT) y
  -- factored: the conjugate map preserves the `M`-ball (avoids inline defeq blowup)
  have hPhiB_le : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M) →
      (∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ w τ x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMap p u₀ w t x| ≤ M := by
    intro w hwb hwn hwc t ht htT x
    have hsplit : intervalConjugateDuhamelMap p u₀ w t x
        = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
          + (-p.χ₀) * (∫ s in (0:ℝ)..t,
              intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
          + ∫ s in (0:ℝ)..t,
              intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1 := rfl
    have hH : |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| ≤ B0 :=
      intervalFullSemigroupOperator_Linfty_bound ht hB0_pos.le hLift_bound x.1
    have hB : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)|
        ≤ |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQsup) := by
      rw [abs_mul, abs_neg]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hCg]
      exact conjugateDuhamel_sup_bound_of_ball_univ p hM_nn hCQsup_nn hwb hwn hwc
        (hflux_sup_w w hwb hwn hwc) ht htT x
    have hL : |∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1|
        ≤ T * CLsup :=
      valueDuhamel_sup_bound_of_ball p hM_pos hCLsup_nn hwb (hlog_sup_w w hwb) ht htT x
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add (le_trans (abs_add_le _ _) (add_le_add hH hB)) hL) ?_
    have := hmapsto_budget; rw [hCg] at this ⊢; linarith
  have hmapsTo_nn_pf :
      ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        0 ≤ intervalConjugateDuhamelMap p u₀ w t x
      := by
      intro w hwb hwn hwc t ht htT x
      have hfloor_le := intervalConjugateDuhamelMap_ge_half_floor_of_ball
        hu₀ hCQsup_nn hCLsup_nn
        hfloor_small ht htT x
        (conjugateDuhamel_sup_bound_of_ball_univ p hM_nn hCQsup_nn hwb hwn hwc
          (hflux_sup_w w hwb hwn hwc) ht htT x)
        (valueDuhamel_sup_bound_of_ball p hM_pos hCLsup_nn hwb (hlog_sup_w w hwb) ht htT x)
      have : (0:ℝ) ≤ floor / 2 := by linarith [hfloor_pos]
      simp only [hfloor] at hfloor_le
      linarith
  have hmapsTo_pos_pf :
      ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        0 < intervalConjugateDuhamelMap p u₀ w t x
      := by
      intro w hwb hwn hwc t ht htT x
      have hfloor_le := intervalConjugateDuhamelMap_ge_half_floor_of_ball
        hu₀ hCQsup_nn hCLsup_nn
        hfloor_small ht htT x
        (conjugateDuhamel_sup_bound_of_ball_univ p hM_nn hCQsup_nn hwb hwn hwc
          (hflux_sup_w w hwb hwn hwc) ht htT x)
        (valueDuhamel_sup_bound_of_ball p hM_pos hCLsup_nn hwb (hlog_sup_w w hwb) ht htT x)
      simp only [hfloor] at hfloor_le
      linarith [hfloor_pos]
  have hcont_preserved_pf :
      ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      HasJointMeasurability w →
      HasContinuousSlices T (fun t x => intervalConjugateDuhamelMap p u₀ w t x) := by
    intro w hwb hwn hwc hwm
    have hQ_meas : Measurable (Function.uncurry (fun s y => chemFluxLifted p (w s) y)) := by
      simpa [Function.uncurry] using
        ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := w) hwm
    have hL_meas : Measurable (Function.uncurry (fun s y => logisticLifted p (w s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' hwm
    have hL_slice_meas : ∀ s,
        AEStronglyMeasurable (logisticLifted p (w s)) (intervalMeasure 1) := fun s =>
      (hL_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact ShenWork.IntervalConjugateConePreserved.intervalConjugateDuhamelMap_hasContinuousSlices_of_ball
      hB0_pos.le hCQsup_nn hCLsup_nn hLift_bound hLift_meas hQ_meas hL_meas
      (fun s hs hsT => chemFluxLifted_integrable_of_continuous p (hwb s hs hsT) hM_nn
        (hwc s hs hsT) (hwn s hs hsT))
      hL_slice_meas (hflux_sup_w w hwb hwn hwc) (hlog_sup_w w hwb)
  have hbase_diff_pf :
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ 1 t x - conjugatePicardIter p u₀ 0 t x| ≤ 2 * M
      := by
      intro t ht htT x
      -- iter 0 = S(t)u₀ (ball element), iter 1 = Φᴮ(iter 0)
      have hiter0_ball : ∀ τ, 0 < τ → τ ≤ T → ∀ z, |conjugatePicardIter p u₀ 0 τ z| ≤ M := by
        intro τ hτ _ z
        simp only [conjugatePicardIter]
        exact intervalFullSemigroupOperator_Linfty_bound hτ hM_nn
          (fun y => le_trans (hLift_bound y) hB0_le_M) z.1
      have hiter0_nn : ∀ τ, 0 < τ → τ ≤ T → ∀ z, 0 ≤ conjugatePicardIter p u₀ 0 τ z := by
        intro τ hτ _ z
        simp only [conjugatePicardIter]
        exact ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg
          hτ hLift_nn z.1
      have hiter0_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0) := by
        intro τ hτ _
        simp only [conjugatePicardIter]
        exact (intervalFullSemigroupOperator_continuous_of_bounded hτ hB0_pos.le
          hLift_bound hLift_meas.aestronglyMeasurable).comp continuous_subtype_val
      -- |iter1| ≤ M = Φᴮ applied to the iter-0 ball element
      have hiter1_le : |conjugatePicardIter p u₀ 1 t x| ≤ M := by
        simp only [conjugatePicardIter]
        exact hPhiB_le (conjugatePicardIter p u₀ 0) hiter0_ball hiter0_nn hiter0_cont t ht htT x
      have hiter0_le : |conjugatePicardIter p u₀ 0 t x| ≤ M := hiter0_ball t ht htT x
      calc |conjugatePicardIter p u₀ 1 t x - conjugatePicardIter p u₀ 0 t x|
          ≤ |conjugatePicardIter p u₀ 1 t x| + |conjugatePicardIter p u₀ 0 t x| := abs_sub _ _
        _ ≤ M + M := add_le_add hiter1_le hiter0_le
        _ = 2 * M := by ring
  have hmeas_preserved_pf :
      ∀ w, HasJointMeasurability w →
      HasJointMeasurability (fun t x => intervalConjugateDuhamelMap p u₀ w t x) := by
    intro w hwm
    have hQ_meas : Measurable (Function.uncurry (fun s y => chemFluxLifted p (w s) y)) := by
      simpa [Function.uncurry] using
        ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := w) hwm
    have hL_meas : Measurable (Function.uncurry (fun s y => logisticLifted p (w s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' hwm
    exact ShenWork.IntervalConjugateConePreserved.intervalConjugateDuhamelMap_hasJointMeasurability_of_ball
      hLift_meas hQ_meas hL_meas
  refine ⟨T, ⟨?_⟩, hT_pos⟩
  exact {
    T := T, M := M, K := |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) + T * CL
    C₀ := 2 * M, CQ := CQ, CL := CL
    hT := hT_pos, hM := hM_pos
    hK := hK_lt_one
    hK_nn := by
      have h1 : 0 ≤ |p.χ₀| * (Cg * (2 * Real.sqrt T) * CQ) :=
        mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg hCg_nn (by positivity)) hCQ_nn)
      have h2 : 0 ≤ T * CL := mul_nonneg hT_pos.le hCL_nn
      linarith
    hC₀ := by linarith
    hCQ := hCQ_nn, hCL := hCL_nn
    hK_eq := by rw [hCg]
    hbase_ball := by
      intro t ht _htT x
      simp only [conjugatePicardIter]
      refine intervalFullSemigroupOperator_Linfty_bound ht hM_nn (fun y => ?_) x.1
      exact le_trans (hLift_bound y) hB0_le_M
    hbase_nonneg := by
      intro t ht _htT x
      simp only [conjugatePicardIter]
      exact ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg
        ht hLift_nn x.1
    hbase_cont := by
      intro t ht _htT
      simp only [conjugatePicardIter]
      have : Continuous (fun x : intervalDomainPoint =>
          intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1) :=
        (intervalFullSemigroupOperator_continuous_of_bounded ht hB0_pos.le
          hLift_bound hLift_meas.aestronglyMeasurable).comp continuous_subtype_val
      exact this
    hmapsTo := by
      intro w hwb hwn hwc t ht htT x
      exact hPhiB_le w hwb hwn hwc t ht htT x
    hmapsTo_nn := hmapsTo_nn_pf
    hmapsTo_pos := hmapsTo_pos_pf
    hcont_preserved := hcont_preserved_pf
    hbase_diff := hbase_diff_pf
    hbase_meas := by
      have hSg_meas : Measurable (fun q : ℝ × ℝ =>
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
        intervalFullSemigroupOperator_joint_measurable' hLift_meas
      have hfield :
          (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) =
            fun q : ℝ × ℝ =>
              if q.2 ∈ Set.Icc (0 : ℝ) 1 then
                intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
              else 0 := by
        funext q
        by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
        · simp [conjugatePicardIter, intervalDomainLift, hy]
        · simp [conjugatePicardIter, intervalDomainLift, hy]
      change Measurable (fun q : ℝ × ℝ =>
        intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      rw [hfield]
      exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
        hSg_meas measurable_const
    hmeas_preserved := hmeas_preserved_pf
    hflux_diff_bound := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd s hs_pos hs_le y
      have hs : 0 < s ∧ s ≤ T := ⟨hs_pos, hs_le⟩
      have hd_nn : 0 ≤ d :=
        le_trans (abs_nonneg _) (hd T hT_pos le_rfl ⟨0, by constructor <;> norm_num⟩)
      have hbnd := chemFluxLifted_diff_bound_of_ball_slice p hγ_ge hM_pos hd_nn
        (hub s hs.1 hs.2) (hun s hs.1 hs.2) (huc s hs.1 hs.2)
        (hwb s hs.1 hs.2) (hwn s hs.1 hs.2) (hwc s hs.1 hs.2)
        (fun x => hd s hs.1 hs.2 x) y
      calc |chemFluxLifted p (u s) y - chemFluxLifted p (w s) y|
          ≤ (C_RG + M * C_RGL + M * C_RG * p.β * C_RV) * d := by
            simpa [hCRG, hCRGL, hCRV] using hbnd
        _ = CQ * d := by rw [hCQ]
    hflux_diff_integrable := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd s hs_pos hs_le
      have h : 0 < s ∧ s ≤ T := ⟨hs_pos, hs_le⟩
      exact (chemFluxLifted_integrable_of_continuous p (hub s h.1 h.2) hM_nn
        (huc s h.1 h.2) (hun s h.1 h.2)).sub
        (chemFluxLifted_integrable_of_continuous p (hwb s h.1 h.2) hM_nn
          (hwc s h.1 h.2) (hwn s h.1 h.2))
    hflux_kernel_integrable_left := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd t ht htT x s hs_pos hs_le
      have hs : 0 < s ∧ s ≤ T := ⟨hs_pos, hs_le⟩
      have hKint : Integrable
          (fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y)
          (intervalMeasure 1) := by
        by_cases hts : 0 < t - s
        · simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
          exact (ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_snd
            hts x.1).integrableOn_Icc
        · have hkz : (fun y : ℝ =>
              deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y)
              = fun _ => (0 : ℝ) := by
            funext y
            have hk : (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y')
                = fun _ : ℝ => (0 : ℝ) := by
              funext y'
              simp only [intervalNeumannFullKernel]
              rw [show (fun k : ℤ =>
                  heatKernel (t - s) (x.1 - y' + 2 * (k : ℝ))
                  + heatKernel (t - s) (x.1 + y' + 2 * (k : ℝ)))
                  = fun _ : ℤ => (0 : ℝ) from by
                funext k
                rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
                  ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
                  add_zero]]
              exact tsum_zero
            rw [hk, deriv_const]
          rw [hkz]; simp
      have hQbdd : ∀ y, |chemFluxLifted p (u s) y| ≤ CQsup :=
        hflux_sup_w u hub hun huc s hs.1 hs.2
      have hQint : Integrable (chemFluxLifted p (u s)) (intervalMeasure 1) :=
        chemFluxLifted_integrable_of_continuous p (hub s hs.1 hs.2) hM_nn
          (huc s hs.1 hs.2) (hun s hs.1 hs.2)
      exact hKint.mul_bdd hQint.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hQbdd y)
    hflux_kernel_integrable_right := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd t ht htT x s hs_pos hs_le
      have hs : 0 < s ∧ s ≤ T := ⟨hs_pos, hs_le⟩
      have hKint : Integrable
          (fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y)
          (intervalMeasure 1) := by
        by_cases hts : 0 < t - s
        · simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
          exact (ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_snd
            hts x.1).integrableOn_Icc
        · have hkz : (fun y : ℝ =>
              deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y)
              = fun _ => (0 : ℝ) := by
            funext y
            have hk : (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y')
                = fun _ : ℝ => (0 : ℝ) := by
              funext y'
              simp only [intervalNeumannFullKernel]
              rw [show (fun k : ℤ =>
                  heatKernel (t - s) (x.1 - y' + 2 * (k : ℝ))
                  + heatKernel (t - s) (x.1 + y' + 2 * (k : ℝ)))
                  = fun _ : ℤ => (0 : ℝ) from by
                funext k
                rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
                  ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
                  add_zero]]
              exact tsum_zero
            rw [hk, deriv_const]
          rw [hkz]; simp
      have hQbdd : ∀ y, |chemFluxLifted p (w s) y| ≤ CQsup :=
        hflux_sup_w w hwb hwn hwc s hs.1 hs.2
      have hQint : Integrable (chemFluxLifted p (w s)) (intervalMeasure 1) :=
        chemFluxLifted_integrable_of_continuous p (hwb s hs.1 hs.2) hM_nn
          (hwc s hs.1 hs.2) (hwn s hs.1 hs.2)
      exact hKint.mul_bdd hQint.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hQbdd y)
    hflux_duhamel_integrable_left := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd t ht htT x
      exact conjugateChemFlux_duhamel_intervalIntegrable_of_ball
        p hM_nn hCQsup_nn hub hun huc hum (hflux_sup_w u hub hun huc) ht htT x
    hflux_duhamel_integrable_right := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd t ht htT x
      exact conjugateChemFlux_duhamel_intervalIntegrable_of_ball
        p hM_nn hCQsup_nn hwb hwn hwc hwm (hflux_sup_w w hwb hwn hwc) ht htT x
    hflux_duhamel_diff_integrable := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd t ht htT x
      have hQdbound : ∀ τ, 0 < τ → τ ≤ T → ∀ y,
          |chemFluxLifted p (u τ) y - chemFluxLifted p (w τ) y| ≤ 2 * CQsup := by
        intro τ hτ hτT y
        calc |chemFluxLifted p (u τ) y - chemFluxLifted p (w τ) y|
            ≤ |chemFluxLifted p (u τ) y| + |chemFluxLifted p (w τ) y| := abs_sub _ _
          _ ≤ CQsup + CQsup :=
            add_le_add (hflux_sup_w u hub hun huc τ hτ hτT y)
              (hflux_sup_w w hwb hwn hwc τ hτ hτT y)
          _ = 2 * CQsup := by ring
      exact conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball
        p hM_nn (by linarith [hCQsup_nn] : (0:ℝ) ≤ 2 * CQsup)
        hub hun hwb hwn huc hwc hum hwm hQdbound ht htT x
    hlogistic_duhamel_diff_bound := by
      intro u w d hub hun hwb hwn huc hwc hum hwm hd t ht htT x
      have hd_nn : 0 ≤ d :=
        le_trans (abs_nonneg _) (hd T hT_pos le_rfl ⟨0, by constructor <;> norm_num⟩)
      exact logistic_duhamel_diff_bound_of_ball p hT_pos hM_pos hCL_nn hd_nn hCL_lip
        hub hun hwb hwn huc hwc hum hwm hd ht htT x
  }

end ShenWork.IntervalConjugatePicard
