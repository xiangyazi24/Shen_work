import ShenWork.Paper2.IntervalUniformTruncatedMapCertificateProducer
import ShenWork.Paper2.IntervalTruncatedLogisticLipschitz
import ShenWork.Paper2.IntervalTruncatedWindowedSourceMeasurable
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalConjugateFluxDiffBall
import ShenWork.Paper2.IntervalConjugatePicardBounds

open Filter Topology Set MeasureTheory

/-!
# The `mapCertificate` datum — `UniformTruncatedConjugateMapCertificateData` producer

The 4th χ₀<0 assembly input.  This file assembles the `∀M,u₀,C` family datum from
the committed per-`C` producer `uniformTruncatedConjugateMapCertificate_of_realizedBudgets`.

## Route decision (a vs b) — resolved by reading the component theorems

The certificate has four fields; they split as follows against the core
`UniformConjugateMildExistenceCore` (whose `CQ/CLsup/CQsup` are FREE scalar fields
constrained only by nonnegativity):

* `hmeas_preserved` — **route (a)**: provable for ANY `C` directly from the core's
  own carried field `C.hmeas_preserved` (no budget needed).
* `hmapsTo`, `hcont_preserved` — **NOT route (a)**: the component theorems
  `truncatedConjugateDuhamelMap_mapsTo_of_realized_budget` and
  `…_hasContinuousSlices_of_realized_budget` both **consume** `HS`
  (`UniformTruncatedSourceSupBudgetRealization`) and rewrite `H.hCQsup_eq` — i.e. they
  need `C.CQsup` to **equal** the concrete source-sup formula `R·(‖grad‖₂·2ν R^γ)`.
  For an arbitrary `C` this is false (`CQsup` is free), and **no core field pins it**:
  route (b)'s "core-validity field" does not exist in the current struct.  The HS
  docstring says as much — "the scalar structure does not currently retain them."
* `hcontr` — needs `HD` (`UniformTruncatedDuhamelDifferenceCertificate`: the truncated
  flux/logistic Lipschitz differences).  **No in-repo producer of `HD` exists.**

Hence neither pure route closes the unconditional `∀C` datum.  What IS sound is the
reduction below: given per-core suppliers of `HS` and `HD`, the datum follows.  The two
suppliers are the exact remaining obligations, named precisely (see the residual note).
-/

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.Paper2
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

/-- The faithful truncated logistic Duhamel leg is Lipschitz with the constant
stored in the uniform core. -/
theorem truncatedLogisticDuhamel_diff_bound_of_uniformCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HS : UniformTruncatedSourceSupBudgetRealization p C)
    {u w : ℝ → intervalDomainPoint → ℝ} {d : ℝ}
    (hub : ∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.R)
    (hwb : ∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R)
    (_huc : HasContinuousSlices C.T u) (_hwc : HasContinuousSlices C.T w)
    (hum : HasJointMeasurability u) (hwm : HasJointMeasurability w)
    (hd : ∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ C.T) (x : intervalDomainPoint) :
    |(∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (u s)) x.1) -
      (∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (w s)) x.1)| ≤
      C.T * (C.CL * d) := by
  let x0 : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
  have hd_nn : 0 ≤ d :=
    (abs_nonneg (u C.T x0 - w C.T x0)).trans (hd C.T C.hT le_rfl x0)
  let r_u : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ C.T then truncatedLogisticLifted p (u s) y else 0
  let r_w : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ C.T then truncatedLogisticLifted p (w s) y else 0
  have hru_bound : ∀ s y, |r_u s y| ≤ C.CLsup := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ C.T
    · simpa [r_u, hs] using
        truncatedLogisticLifted_bound_of_realized_budget HS
          (hub s hs.1 hs.2) y
    · simp [r_u, hs, C.hCLsup]
  have hrw_bound : ∀ s y, |r_w s y| ≤ C.CLsup := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ C.T
    · simpa [r_w, hs] using
        truncatedLogisticLifted_bound_of_realized_budget HS
          (hwb s hs.1 hs.2) y
    · simp [r_w, hs, C.hCLsup]
  have hru_joint : Measurable (fun q : ℝ × ℝ => r_u q.1 q.2) := by
    have hbase := ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedLogisticLifted_joint_measurable_of_lift_joint
      (p := p) hum
    simp only [r_u]
    exact Measurable.ite
      (((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
        ((isClosed_Iic.preimage continuous_fst).measurableSet))
      hbase measurable_const
  have hrw_joint : Measurable (fun q : ℝ × ℝ => r_w q.1 q.2) := by
    have hbase := ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedLogisticLifted_joint_measurable_of_lift_joint
      (p := p) hwm
    simp only [r_w]
    exact Measurable.ite
      (((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
        ((isClosed_Iic.preimage continuous_fst).measurableSet))
      hbase measurable_const
  have hru_int : ∀ s, Integrable (r_u s) (intervalMeasure 1) := by
    intro s
    apply Integrable.of_bound
      ((hru_joint.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      C.CLsup
    filter_upwards [] with y
    simpa [Real.norm_eq_abs] using hru_bound s y
  have hrw_int : ∀ s, Integrable (r_w s) (intervalMeasure 1) := by
    intro s
    apply Integrable.of_bound
      ((hrw_joint.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      C.CLsup
    filter_upwards [] with y
    simpa [Real.norm_eq_abs] using hrw_bound s y
  have hr_diff_bound : ∀ s y, |r_u s y - r_w s y| ≤ C.CL * d := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ C.T
    · have hu_lift : |intervalDomainLift (u s) y| ≤ C.R := by
        unfold intervalDomainLift
        split_ifs with hy
        · exact hub s hs.1 hs.2 ⟨y, hy⟩
        · simpa using C.hR.le
      have hw_lift : |intervalDomainLift (w s) y| ≤ C.R := by
        unfold intervalDomainLift
        split_ifs with hy
        · exact hwb s hs.1 hs.2 ⟨y, hy⟩
        · simpa using C.hR.le
      have hd_lift :
          |intervalDomainLift (u s) y - intervalDomainLift (w s) y| ≤ d := by
        unfold intervalDomainLift
        split_ifs with hy
        · exact hd s hs.1 hs.2 ⟨y, hy⟩
        · simpa using hd_nn
      simpa [r_u, r_w, hs, truncatedLogisticLifted] using
        (C.hCL_lip _ _ hu_lift hw_lift).trans
          (mul_le_mul_of_nonneg_left hd_lift C.hCL)
    · simp [r_u, r_w, hs, mul_nonneg C.hCL hd_nn]
  have hVu_eq :
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (truncatedLogisticLifted p (u s)) x.1) =
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r_u s) x.1 := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le ht.le] at hs
      simp [r_u, hs.1, hs.2.trans htT]
  have hVw_eq :
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (truncatedLogisticLifted p (w s)) x.1) =
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r_w s) x.1 := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le ht.le] at hs
      simp [r_w, hs.1, hs.2.trans htT]
  have hint_u : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (t - s) (r_u s) x.1)
      volume 0 t :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
        (f := r_u) ht (by simpa [Function.uncurry] using hru_joint)
        C.hCLsup hru_bound x.1
  have hint_w : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (t - s) (r_w s) x.1)
      volume 0 t :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
        (f := r_w) ht (by simpa [Function.uncurry] using hrw_joint)
        C.hCLsup hrw_bound x.1
  rw [hVu_eq, hVw_eq, ← intervalIntegral.integral_sub hint_u hint_w]
  have hptw : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)),
      |intervalFullSemigroupOperator (t - s) (r_u s) x.1 -
        intervalFullSemigroupOperator (t - s) (r_w s) x.1| ≤ C.CL * d := by
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hne] with s hsne hsI
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hsI.2 hsne)
    exact ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_diff_Linfty_of_integrable
        hst (hru_int s) (hrw_int s) C.hCLsup (hru_bound s)
        C.hCLsup (hrw_bound s) (mul_nonneg C.hCL hd_nn)
        (hr_diff_bound s) x.1
  calc
    |∫ s in (0 : ℝ)..t,
        (intervalFullSemigroupOperator (t - s) (r_u s) x.1 -
          intervalFullSemigroupOperator (t - s) (r_w s) x.1)|
        ≤ ∫ s in (0 : ℝ)..t,
            |intervalFullSemigroupOperator (t - s) (r_u s) x.1 -
              intervalFullSemigroupOperator (t - s) (r_w s) x.1| :=
          intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ _s in (0 : ℝ)..t, C.CL * d :=
      intervalIntegral.integral_mono_ae_restrict ht.le
        (hint_u.sub hint_w).abs intervalIntegrable_const hptw
    _ = t * (C.CL * d) := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    _ ≤ C.T * (C.CL * d) :=
      mul_le_mul_of_nonneg_right htT (mul_nonneg C.hCL hd_nn)

/-- The faithful positive-part chemotaxis Duhamel leg is Lipschitz with the
source constant stored in the uniform core. -/
theorem truncatedChemDuhamel_diff_bound_of_uniformCore
    {p : CM2Params} (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HS : UniformTruncatedSourceSupBudgetRealization p C)
    {u w : ℝ → intervalDomainPoint → ℝ} {d : ℝ}
    (hub : ∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x| ≤ C.R)
    (hwb : ∀ t, 0 < t → t ≤ C.T → ∀ x, |w t x| ≤ C.R)
    (huc : HasContinuousSlices C.T u) (hwc : HasContinuousSlices C.T w)
    (hum : HasJointMeasurability u) (hwm : HasJointMeasurability w)
    (hd : ∀ t, 0 < t → t ≤ C.T → ∀ x, |u t x - w t x| ≤ d)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ C.T) (x : intervalDomainPoint) :
    |(-p.χ₀) *
      ((∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s)
            (truncatedChemFluxLifted p (u s)) x.1) -
        (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s)
            (truncatedChemFluxLifted p (w s)) x.1))| ≤
      |p.χ₀| *
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt C.T) * (C.CQ * d)) := by
  let x0 : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
  have hd_nn : 0 ≤ d :=
    (abs_nonneg (u C.T x0 - w C.T x0)).trans (hd C.T C.hT le_rfl x0)
  let up : ℝ → intervalDomainPoint → ℝ := positivePartTrajectory u
  let wp : ℝ → intervalDomainPoint → ℝ := positivePartTrajectory w
  have hubp : ∀ s, 0 < s → s ≤ C.T → ∀ z, |up s z| ≤ C.R := by
    simpa [up] using positivePartTrajectory_ball hub
  have hwbp : ∀ s, 0 < s → s ≤ C.T → ∀ z, |wp s z| ≤ C.R := by
    simpa [wp] using positivePartTrajectory_ball hwb
  have hunp : ∀ s, 0 < s → s ≤ C.T → ∀ z, 0 ≤ up s z := by
    simpa [up] using (positivePartTrajectory_nonneg u :
      ∀ s, 0 < s → s ≤ C.T → ∀ z, 0 ≤ positivePartTrajectory u s z)
  have hwnp : ∀ s, 0 < s → s ≤ C.T → ∀ z, 0 ≤ wp s z := by
    simpa [wp] using (positivePartTrajectory_nonneg w :
      ∀ s, 0 < s → s ≤ C.T → ∀ z, 0 ≤ positivePartTrajectory w s z)
  have hucp : HasContinuousSlices C.T up := by
    simpa [up] using positivePartTrajectory_continuous huc
  have hwcp : HasContinuousSlices C.T wp := by
    simpa [wp] using positivePartTrajectory_continuous hwc
  have hump : HasJointMeasurability up := by
    simpa [up] using positivePartTrajectory_measurable hum
  have hwmp : HasJointMeasurability wp := by
    simpa [wp] using positivePartTrajectory_measurable hwm
  have hdp : ∀ s, 0 < s → s ≤ C.T → ∀ z, |up s z - wp s z| ≤ d := by
    simpa [up, wp] using positivePartTrajectory_diff hd
  have hQdiff : ∀ s, 0 < s → s ≤ C.T → ∀ y,
      |chemFluxLifted p (up s) y - chemFluxLifted p (wp s) y| ≤ C.CQ * d := by
    intro s hs hsT y
    have hraw :=
      ShenWork.IntervalConjugateFluxDiffBall.chemFluxLifted_diff_bound_of_ball_slice
        p hγ C.hR hd_nn
        (hubp s hs hsT) (hunp s hs hsT) (hucp s hs hsT)
        (hwbp s hs hsT) (hwnp s hs hsT) (hwcp s hs hsT)
        (hdp s hs hsT) y
    simpa [C.hCQ_eq] using hraw
  have hQintdiff : ∀ s, 0 < s → s ≤ C.T →
      Integrable (fun y => chemFluxLifted p (up s) y - chemFluxLifted p (wp s) y)
        (intervalMeasure 1) := by
    intro s hs hsT
    exact
      (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hubp s hs hsT) C.hR.le (hucp s hs hsT) (hunp s hs hsT)).sub
      (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hwbp s hs hsT) C.hR.le (hwcp s hs hsT) (hwnp s hs hsT))
  have hQsup_u : ∀ s, 0 < s → s ≤ C.T → ∀ y,
      |chemFluxLifted p (up s) y| ≤ C.CQsup := by
    intro s hs hsT y
    have h := truncatedChemFluxLifted_bound_of_realized_budget HS
      (hub s hs hsT) (huc s hs hsT) y
    simpa [up, positivePartTrajectory,
      truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice] using h
  have hQsup_w : ∀ s, 0 < s → s ≤ C.T → ∀ y,
      |chemFluxLifted p (wp s) y| ≤ C.CQsup := by
    intro s hs hsT y
    have h := truncatedChemFluxLifted_bound_of_realized_budget HS
      (hwb s hs hsT) (hwc s hs hsT) y
    simpa [wp, positivePartTrajectory,
      truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice] using h
  have hBu : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (up s)) x.1) volume 0 t :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateChemFlux_duhamel_intervalIntegrable_of_ball
        p C.hR.le C.hCQsup hubp hunp hucp hump hQsup_u ht htT x
  have hBw : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (wp s)) x.1) volume 0 t :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateChemFlux_duhamel_intervalIntegrable_of_ball
        p C.hR.le C.hCQsup hwbp hwnp hwcp hwmp hQsup_w ht htT x
  have hBdiff : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxLifted p (up s) y - chemFluxLifted p (wp s) y) x.1)
      volume 0 t :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball
        p C.hR.le (mul_nonneg C.hCQ hd_nn)
        hubp hunp hwbp hwnp hucp hwcp hump hwmp hQdiff ht htT x
  have hKint : ∀ s, Integrable
      (fun y : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y)
      (intervalMeasure 1) := by
    intro s
    by_cases hts : 0 < t - s
    · simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
      exact
        (ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_snd
          hts x.1).integrableOn_Icc
    · have hk : (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') =
          fun _ : ℝ => 0 := by
        funext y'
        simp only [intervalNeumannFullKernel]
        rw [show (fun k : ℤ =>
            heatKernel (t - s) (x.1 - y' + 2 * (k : ℝ)) +
              heatKernel (t - s) (x.1 + y' + 2 * (k : ℝ))) =
            fun _ : ℤ => 0 from by
          funext k
          rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
            ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
            add_zero]]
        exact tsum_zero
      simp [hk]
  have hKQu : ∀ s, 0 < s → s ≤ C.T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y *
          chemFluxLifted p (up s) y) (intervalMeasure 1) := by
    intro s hs hsT
    have hQint :=
      ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hubp s hs hsT) C.hR.le (hucp s hs hsT) (hunp s hs hsT)
    exact (hKint s).mul_bdd hQint.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hQsup_u s hs hsT y)
  have hKQw : ∀ s, 0 < s → s ≤ C.T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') y *
          chemFluxLifted p (wp s) y) (intervalMeasure 1) := by
    intro s hs hsT
    have hQint :=
      ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hwbp s hs hsT) C.hR.le (hwcp s hs hsT) (hwnp s hs hsT)
    exact (hKint s).mul_bdd hQint.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hQsup_w s hs hsT y)
  simp_rw [truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
  change |(-p.χ₀) *
    ((∫ s in (0 : ℝ)..t, intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (up s)) x.1) -
      (∫ s in (0 : ℝ)..t, intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (wp s)) x.1))| ≤ _
  rw [← intervalIntegral.integral_sub hBu hBw]
  exact ShenWork.IntervalConjugatePicardBounds.conjugateChemFluxDuhamel_diff_sup_bound
    p ht htT (mul_nonneg C.hCQ hd_nn) hQdiff hQintdiff x.1 hKQu hKQw hBdiff

/-- The three source-budget formulas retained by the strengthened uniform core. -/
def uniformTruncatedSourceSupBudgetRealization_of_uniformCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    UniformTruncatedSourceSupBudgetRealization p C where
  hCQsup_eq := C.hCQsup_eq
  hCLsup_eq := C.hCLsup_eq
  hCQ_eq := C.hCQ_eq

/-- Both faithful truncated Duhamel difference bounds, reconstructed from the
realization fields retained by the uniform core. -/
def uniformTruncatedDuhamelDifferenceCertificate_of_uniformCore
    {p : CM2Params} (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    UniformTruncatedDuhamelDifferenceCertificate p C where
  chemDiff := by
    intro u w d hub hwb huc hwc hum hwm hd t ht htT x
    exact truncatedChemDuhamel_diff_bound_of_uniformCore hγ
      (uniformTruncatedSourceSupBudgetRealization_of_uniformCore C)
      hub hwb huc hwc hum hwm hd ht htT x
  logisticDiff := by
    intro u w d hub hwb huc hwc hum hwm hd t ht htT x
    exact truncatedLogisticDuhamel_diff_bound_of_uniformCore
      (uniformTruncatedSourceSupBudgetRealization_of_uniformCore C)
      hub hwb huc hwc hum hwm hd ht htT x

/-- **`mapCertificate` datum, reduced to its two genuine per-core inputs.**

Given, for every core `C`, the source-sup budget realization `HS` (the
`CQsup/CLsup/CQ = formula` equalities the scalar core does not retain) and the
Duhamel difference certificate `HD` (the truncated flux/logistic Lipschitz
differences), the full `∀M,u₀,C` map-certificate datum follows.  `hmeas_preserved`
needs neither — it comes straight from `C.hmeas_preserved`. -/
theorem uniformTruncatedConjugateMapCertificateData_of_realizations
    {p : CM2Params} (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (HS : ∀ {u₀ : intervalDomainPoint → ℝ}
        (C : UniformConjugateMildExistenceCore p u₀),
        UniformTruncatedSourceSupBudgetRealization p C)
    (HD : ∀ {u₀ : intervalDomainPoint → ℝ}
        (C : UniformConjugateMildExistenceCore p u₀),
        UniformTruncatedDuhamelDifferenceCertificate p C) :
    UniformTruncatedConjugateMapCertificateData p := by
  intro M hM u₀ hu₀ hbound C
  exact uniformTruncatedConjugateMapCertificate_of_realizedBudgets hα hγ C (HS C) (HD C)

/-- Unconditional faithful truncated-map certificate used by the χ₀<0
assembly.  All scalar realizations and both component Lipschitz estimates are
projections of the strengthened uniform core. -/
theorem uniformTruncatedConjugateMapCertificateData_producer
    {p : CM2Params} (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    UniformTruncatedConjugateMapCertificateData p := by
  exact uniformTruncatedConjugateMapCertificateData_of_realizations hα hγ
    (fun C => uniformTruncatedSourceSupBudgetRealization_of_uniformCore C)
    (fun C => uniformTruncatedDuhamelDifferenceCertificate_of_uniformCore hγ C)

end ShenWork.Paper2.BFormPositiveDatumNegPart
