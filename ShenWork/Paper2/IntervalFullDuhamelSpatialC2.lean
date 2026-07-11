/-
  Second spatial differentiation of a full Neumann-semigroup Duhamel leg.

  The source is only required to be bounded at early times.  On the late half
  of the time interval a spatial Holder modulus supplies the cancellative,
  integrable Hessian estimate.
-/
import ShenWork.Paper2.ChemMildInterchange
import ShenWork.Paper2.IntervalFullKernelSecondDerivInteriorHolder
import ShenWork.Paper2.IntervalFullSemigroupSecondDerivContinuous

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator weightedHeatHessConst)

/-- The interior cancellative Hessian estimate extends to the two endpoints.
The semigroup Hessian is continuous on `[0,1]` for bounded measurable data,
and `(0,1)` is dense there. -/
theorem intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
    {r theta : ℝ} (hr : 0 < r)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    {F : ℝ → ℝ} (hF_int : Integrable F (intervalMeasure 1))
    {CQ HQ : ℝ} (hF_bound : ∀ y, |F y| ≤ CQ) (hHQ : 0 ≤ HQ)
    (hF_holder : ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |F a - F b| ≤ HQ * |a - b| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (fun y ↦ deriv
      (fun z ↦ intervalFullSemigroupOperator r F z) y) x| ≤
      weightedHeatHessConst theta * r ^ (-1 + theta / 2 : ℝ) * HQ := by
  have hcont :=
    (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_continuousOn_Icc_of_bounded
      hr hF_int hF_bound).abs
  have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have hxcl : x ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [hcl]
    exact hx
  refine le_on_closure (s := Set.Ioo (0 : ℝ) 1)
    (f := fun y ↦ |deriv (fun w ↦ deriv
      (fun z ↦ intervalFullSemigroupOperator r F z) w) y|)
    (g := fun _ ↦ weightedHeatHessConst theta *
      r ^ (-1 + theta / 2 : ℝ) * HQ) ?_ ?_ continuousOn_const hxcl
  · intro y hy
    exact ShenWork.IntervalNeumannFullKernel.neumannHeatSecondDeriv_interiorCtheta_to_Linfty
      hr htheta0 htheta1 hF_int.aestronglyMeasurable hF_bound hHQ hF_holder hy
  · simpa [hcl] using hcont

/-- For a bounded measurable source family, the time-integrated first spatial
derivative of the full Neumann semigroup is continuous on `[0,1]`. -/
theorem intervalFullDuhamel_firstDeriv_continuousOn_Icc_of_bounded
    {t CQ : ℝ} (ht : 0 < t) (hCQ : 0 ≤ CQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) x)
      (Set.Icc (0 : ℝ) 1) := by
  set Cgrad : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant with hCgrad
  set bound : ℝ → ℝ := fun s ↦
    Cgrad * (t - s) ^ (-(1 / 2) : ℝ) * CQ with hbound
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    rw [hbound]
    exact
      ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
        Cgrad).mul_const CQ
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hmeas : ∀ x, AEStronglyMeasurable
      (fun s ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro x
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound x
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  intro x hx
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := bound) ?hF_meas ?h_bound hbound_int ?h_cont
  case hF_meas =>
    exact Filter.Eventually.of_forall hmeas
  case h_bound =>
    filter_upwards [self_mem_nhdsWithin] with y _hy
    filter_upwards [hne] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    rw [Real.norm_eq_abs, hbound, hCgrad]
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
      hlag (hF_int s).aestronglyMeasurable (hF_bound s) y
  case h_cont =>
    filter_upwards [hne] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    exact
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_continuous_of_bounded
        hlag (hF_int s).aestronglyMeasurable (hF_bound s)).continuousWithinAt

/-- The time integral of the first spatial derivative of a full-semigroup
Duhamel leg is differentiable when the source is uniformly Holder only on the
late half of the time interval. -/
theorem intervalFullDuhamel_deriv_hasDerivAt_of_late_holder
    {t theta CQ HQ : ℝ} (ht : 0 < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |F s a - F s b| ≤ HQ * |a - b| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y)
      (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      x := by
  set Cmix : ℝ := 5 * Real.sqrt 2 / 2 with hCmix
  set Cearly : ℝ := Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ with hCearly
  set Clate : ℝ := weightedHeatHessConst theta * HQ with hClate
  set bound : ℝ → ℝ := fun s ↦
    Cearly + Clate * (t - s) ^ (-1 + theta / 2 : ℝ) with hbound
  have ht2 : 0 < t / 2 := by positivity
  have hCmix_nn : 0 ≤ Cmix := by rw [hCmix]; positivity
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hCmix_nn (Real.rpow_nonneg ht2.le _)) hCQ
  have hClate_nn : 0 ≤ Clate := by
    rw [hClate]
    exact mul_nonneg
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    rw [hbound]
    have hc : IntervalIntegrable (fun _ : ℝ ↦ Cearly) volume 0 t :=
      intervalIntegrable_const
    exact hc.add
      ((ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Clate)
  let P : ℝ → ℝ → ℝ := fun y s ↦
    deriv (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y
  let P' : ℝ → ℝ → ℝ := fun y s ↦
    deriv (fun w ↦ deriv
      (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) w) y
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hP_meas : ∀ y, AEStronglyMeasurable (P y)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro y
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound y
  have hP'_meas : AEStronglyMeasurable (P' x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    exact intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound x
  have hgrad_bound_int : IntervalIntegrable
      (fun s : ℝ ↦
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          CQ * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
    rw [show (fun s : ℝ ↦
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            CQ * (t - s) ^ (-(1 / 2 : ℝ))) =
        (fun s : ℝ ↦
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant * CQ) *
            (t - s) ^ (-(1 / 2 : ℝ))) by
      funext s
      ring]
    exact (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul _
  have hfirst_int : ∀ y, IntervalIntegrable (P y) volume 0 t := by
    intro y
    exact ShenWork.IntervalNeumannFullKernel.intervalFullCoupledDuhamel_grad_integrand_intervalIntegrable
      ht hF_int hCQ hF_bound y (hP_meas y) hgrad_bound_int
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hDiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun y ↦ P y s) (P' y s) y := by
    filter_upwards [hne] with s hst hs y hy
    rw [Set.uIoc_of_le ht.le] at hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t :=
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hlag : 0 < t - s := sub_pos.mpr hsIoo.2
    have hraw :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
        hlag (hF_int s).aestronglyMeasurable (hF_bound s) y
    simpa [P, P'] using hraw.congr_deriv hraw.deriv.symm
  have hBound : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, ‖P' y s‖ ≤ bound s := by
    filter_upwards [hne] with s hst hs y hy
    rw [Set.uIoc_of_le ht.le] at hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t :=
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hlag : 0 < t - s := sub_pos.mpr hsIoo.2
    rw [Real.norm_eq_abs]
    rcases le_or_gt s (t / 2) with hearly | hlate
    · have hlag_ge : t / 2 ≤ t - s := by linarith
      have hp : (t - s) ^ (-(1 : ℝ)) ≤ (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht2 hlag_ge (by norm_num)
      have hraw :=
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
          hlag (hF_int s).aestronglyMeasurable (hF_bound s) y
      have hearly_bound : |P' y s| ≤ Cearly := by
        dsimp [P']
        refine hraw.trans ?_
        rw [hCearly, hCmix]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp hCmix_nn) hCQ
      rw [hbound]
      exact hearly_bound.trans (le_add_of_nonneg_right
        (mul_nonneg hClate_nn (Real.rpow_nonneg hlag.le _)))
    · have hraw :=
        ShenWork.IntervalNeumannFullKernel.neumannHeatSecondDeriv_interiorCtheta_to_Linfty
          hlag htheta0 htheta1 (hF_int s).aestronglyMeasurable
            (hF_bound s) hHQ (hF_holder s hlate hsIoo.2)
            hy
      have hlate_bound : |P' y s| ≤
          Clate * (t - s) ^ (-1 + theta / 2 : ℝ) := by
        dsimp [P']
        rw [hClate]
        convert hraw using 1 <;> ring
      rw [hbound]
      exact hlate_bound.trans (le_add_of_nonneg_left hCearly_nn)
  have hmeas_evt : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (P y) (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    Filter.Eventually.of_forall hP_meas
  have hresult := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := t)
    (F := P) (F' := P') (x₀ := x)
    (s := Set.Ioo (0 : ℝ) 1) (bound := bound)
    (hs := isOpen_Ioo.mem_nhds hx)
    (hF_meas := hmeas_evt) (hF_int := hfirst_int x)
    (hF'_meas := hP'_meas) (h_bound := hBound)
    (bound_integrable := hbound_int) (h_diff := hDiff)
  exact hresult.2

/-- The integrated Hessian in the preceding theorem is continuous on the
open physical interval. -/
theorem intervalFullDuhamel_secondDeriv_continuousOn_of_late_holder
    {t theta CQ HQ : ℝ} (ht : 0 < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |F s a - F s b| ≤ HQ * |a - b| ^ theta) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      (Set.Ioo (0 : ℝ) 1) := by
  set Cmix : ℝ := 5 * Real.sqrt 2 / 2 with hCmix
  set Cearly : ℝ := Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ with hCearly
  set Clate : ℝ := weightedHeatHessConst theta * HQ with hClate
  set bound : ℝ → ℝ := fun s ↦
    Cearly + Clate * (t - s) ^ (-1 + theta / 2 : ℝ) with hbound
  have ht2 : 0 < t / 2 := by positivity
  have hCmix_nn : 0 ≤ Cmix := by rw [hCmix]; positivity
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hCmix_nn (Real.rpow_nonneg ht2.le _)) hCQ
  have hClate_nn : 0 ≤ Clate := by
    rw [hClate]
    exact mul_nonneg
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    rw [hbound]
    have hc : IntervalIntegrable (fun _ : ℝ ↦ Cearly) volume 0 t :=
      intervalIntegrable_const
    exact hc.add
      ((ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Clate)
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hmeas : ∀ x, AEStronglyMeasurable
      (fun s ↦ deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro x
    exact intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound x
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (fun y ↦ deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤
          bound s := by
    intro s hs x hx
    have hlag : 0 < t - s := sub_pos.mpr hs.2
    rcases le_or_gt s (t / 2) with hearly | hlate
    · have hlag_ge : t / 2 ≤ t - s := by linarith
      have hp : (t - s) ^ (-(1 : ℝ)) ≤ (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht2 hlag_ge (by norm_num)
      have hraw :=
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
          hlag (hF_int s).aestronglyMeasurable (hF_bound s) x
      have hearly_bound : |deriv (fun y ↦ deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤
          Cearly := by
        refine hraw.trans ?_
        rw [hCearly, hCmix]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp hCmix_nn) hCQ
      rw [hbound]
      exact hearly_bound.trans (le_add_of_nonneg_right
        (mul_nonneg hClate_nn (Real.rpow_nonneg hlag.le _)))
    · have hraw :=
        ShenWork.IntervalNeumannFullKernel.neumannHeatSecondDeriv_interiorCtheta_to_Linfty
          hlag htheta0 htheta1 (hF_int s).aestronglyMeasurable
            (hF_bound s) hHQ (hF_holder s hlate hs.2) hx
      have hlate_bound : |deriv (fun y ↦ deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤
          Clate * (t - s) ^ (-1 + theta / 2 : ℝ) := by
        rw [hClate]
        convert hraw using 1 <;> ring
      rw [hbound]
      exact hlate_bound.trans (le_add_of_nonneg_left hCearly_nn)
  intro x hx
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := bound) ?hF_meas ?h_bound hbound_int ?h_cont
  case hF_meas =>
    exact Filter.Eventually.of_forall hmeas
  case h_bound =>
    filter_upwards [self_mem_nhdsWithin] with y hy
    filter_upwards [hne] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [Real.norm_eq_abs]
    exact hpoint s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩ y hy
  case h_cont =>
    filter_upwards [hne] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    exact ((ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_continuousOn_Icc_of_bounded
      hlag (hF_int s) (hF_bound s)).mono Set.Ioo_subset_Icc_self) x hx

/-- The integrated Hessian is continuous up to both endpoints.  The only new
ingredient beyond the open-interval theorem is closure of its pointwise
dominating estimate from `Ioo` to `Icc`. -/
theorem intervalFullDuhamel_secondDeriv_continuousOn_Icc_of_late_holder
    {t theta CQ HQ : ℝ} (ht : 0 < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |F s a - F s b| ≤ HQ * |a - b| ^ theta) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      (Set.Icc (0 : ℝ) 1) := by
  set Cmix : ℝ := 5 * Real.sqrt 2 / 2 with hCmix
  set Cearly : ℝ := Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ with hCearly
  set Clate : ℝ := weightedHeatHessConst theta * HQ with hClate
  set bound : ℝ → ℝ := fun s ↦
    Cearly + Clate * (t - s) ^ (-1 + theta / 2 : ℝ) with hbound
  have ht2 : 0 < t / 2 := by positivity
  have hCmix_nn : 0 ≤ Cmix := by rw [hCmix]; positivity
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hCmix_nn (Real.rpow_nonneg ht2.le _)) hCQ
  have hClate_nn : 0 ≤ Clate := by
    rw [hClate]
    exact mul_nonneg
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    rw [hbound]
    have hc : IntervalIntegrable (fun _ : ℝ ↦ Cearly) volume 0 t :=
      intervalIntegrable_const
    exact hc.add
      ((ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Clate)
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hmeas : ∀ x, AEStronglyMeasurable
      (fun s ↦ deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro x
    exact intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound x
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun y ↦ deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤
          bound s := by
    intro s hs x hx
    have hlag : 0 < t - s := sub_pos.mpr hs.2
    rcases le_or_gt s (t / 2) with hearly | hlate
    · have hlag_ge : t / 2 ≤ t - s := by linarith
      have hp : (t - s) ^ (-(1 : ℝ)) ≤ (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht2 hlag_ge (by norm_num)
      have hraw :=
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
          hlag (hF_int s).aestronglyMeasurable (hF_bound s) x
      have hearly_bound : |deriv (fun y ↦ deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤
          Cearly := by
        refine hraw.trans ?_
        rw [hCearly, hCmix]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp hCmix_nn) hCQ
      rw [hbound]
      exact hearly_bound.trans (le_add_of_nonneg_right
        (mul_nonneg hClate_nn (Real.rpow_nonneg hlag.le _)))
    · have hraw :=
        intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
          hlag htheta0 htheta1 (hF_int s) (hF_bound s) hHQ
            (hF_holder s hlate hs.2) hx
      have hlate_bound : |deriv (fun y ↦ deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤
          Clate * (t - s) ^ (-1 + theta / 2 : ℝ) := by
        rw [hClate]
        convert hraw using 1 <;> ring
      rw [hbound]
      exact hlate_bound.trans (le_add_of_nonneg_left hCearly_nn)
  intro x hx
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := bound) ?hF_meas ?h_bound hbound_int ?h_cont
  case hF_meas =>
    exact Filter.Eventually.of_forall hmeas
  case h_bound =>
    filter_upwards [self_mem_nhdsWithin] with y hy
    filter_upwards [hne] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [Real.norm_eq_abs]
    exact hpoint s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩ y hy
  case h_cont =>
    filter_upwards [hne] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    exact
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_continuousOn_Icc_of_bounded
        hlag (hF_int s) (hF_bound s)) x hx

end ShenWork.Paper2
