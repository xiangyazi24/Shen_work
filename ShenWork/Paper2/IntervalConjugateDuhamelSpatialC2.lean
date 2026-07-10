/-
  Second spatial differentiation of the faithful conjugate Duhamel leg.

  The second-derivative time integrand is made measurable by applying the
  measurable difference-quotient surrogate twice to the jointly measurable
  conjugate-operator field.  Its integrable bound uses the half-step split on
  the early time interval and flux IBP plus interior Holder cancellation on
  the late interval.
-/
import ShenWork.Paper2.IntervalConjugateSemigroupSecondDeriv
import ShenWork.Paper2.IntervalConjugateDuhamelSpatialC1
import ShenWork.PDE.IntervalParamDerivMeasurable

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel (weightedHeatHessConst)

/-- Fixed-space measurability of the second spatial derivative of a lagged
conjugate-operator family.  No joint measurability of the source derivative is
assumed: two measurable difference-quotient surrogates recover the two actual
spatial derivatives almost everywhere. -/
theorem intervalConjugateKernelOperator_s_dependent_secondDeriv_aestronglyMeasurable_x
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    {CQ : ℝ} (hF_bound : ∀ s y, |F s y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsecond : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      DifferentiableAt ℝ
        (fun z => deriv
          (fun w => intervalConjugateKernelOperator (t - s) (F s) w) z) x) :
    AEStronglyMeasurable
      (fun s => deriv (fun z => deriv
        (fun w => intervalConjugateKernelOperator (t - s) (F s) w) z) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  let G : ℝ × ℝ → ℝ := fun q =>
    intervalConjugateKernelOperator (t - q.1) (F q.1) q.2
  have hGmeas : Measurable G := by
    have hraw :=
      ShenWork.IntervalConjugateKernelJointMeas.intervalConjugateKernelOperator_s_param_joint_measurable
        hF_meas
    have hmap : Measurable (fun q : ℝ × ℝ => ((t, q.2), q.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk measurable_fst
    simpa [G] using hraw.comp hmap
  let D1 : ℝ × ℝ → ℝ := ShenWork.ParamDeriv.diffQuotLimsup G
  let D2 : ℝ × ℝ → ℝ := ShenWork.ParamDeriv.diffQuotLimsup D1
  have hD1meas : Measurable D1 := by
    simpa [D1] using ShenWork.ParamDeriv.measurable_diffQuotLimsup hGmeas
  have hD2meas : Measurable D2 := by
    simpa [D2] using ShenWork.ParamDeriv.measurable_diffQuotLimsup hD1meas
  have hD2x_meas : Measurable (fun s => D2 (s, x)) :=
    hD2meas.comp (measurable_id.prodMk measurable_const)
  refine hD2x_meas.aestronglyMeasurable.congr ?_
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hne] with s hst hs
  rw [Set.uIoc_of_le ht.le] at hs
  have hsIoo : s ∈ Set.Ioo (0 : ℝ) t :=
    ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
  have hlag : 0 < t - s := sub_pos.mpr hsIoo.2
  have hD1eq : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      D1 (s, z) = deriv
        (fun w => intervalConjugateKernelOperator (t - s) (F s) w) z := by
    intro z hz
    have hhas :=
      ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_hasDerivAt
        hlag (hF_int s) (hF_bound s) z
    have hhas' := hhas.congr_deriv hhas.deriv.symm
    simpa [D1, G] using
      ShenWork.ParamDeriv.diffQuotLimsup_eq_of_hasDerivAt hhas'
  have hev : (fun z => D1 (s, z)) =ᶠ[nhds x]
      fun z => deriv
        (fun w => intervalConjugateKernelOperator (t - s) (F s) w) z := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    exact hD1eq z hz
  have hD1has : HasDerivAt (fun z => D1 (s, z))
      (deriv (fun z => deriv
        (fun w => intervalConjugateKernelOperator (t - s) (F s) w) z) x) x :=
    (hsecond s hsIoo).hasDerivAt.congr_of_eventuallyEq hev
  have hsur := ShenWork.ParamDeriv.diffQuotLimsup_eq_of_hasDerivAt hD1has
  simpa [D2] using hsur

/-- The time integral of the first spatial derivative of a conjugate Duhamel
leg is differentiable.  The early half uses only bounded source data; the late
half uses an integrable Holder bound for the actual weak source derivative. -/
theorem intervalConjugateDuhamel_deriv_hasDerivAt_of_late_deriv_holder
    {t theta CQ CQd HQd : ℝ} (ht : 0 < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hCQ : 0 ≤ CQ) (hHQd : 0 ≤ HQd)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t, Continuous (F s))
    (hF_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (F s) (deriv (F s) z) z)
    (hF_deriv_int : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      IntervalIntegrable (deriv (F s)) volume 0 1)
    (hF0 : ∀ s, F s 0 = 0) (hF1 : ∀ s, F s 1 = 0)
    (hF_deriv_bound : ∀ s, t / 2 < s → s < t →
      ∀ z, |deriv (F s) z| ≤ CQd)
    (hF_deriv_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (F s) a - deriv (F s) b| ≤ HQd * |a - b| ^ theta)
    (hfirst_int : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      IntervalIntegrable
        (fun s => deriv
          (fun z => intervalConjugateKernelOperator (t - s) (F s) z) x)
        volume 0 t)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y => ∫ s in (0 : ℝ)..t, deriv
        (fun z => intervalConjugateKernelOperator (t - s) (F s) z) y)
      (∫ s in (0 : ℝ)..t, deriv (fun y => deriv
        (fun z => intervalConjugateKernelOperator (t - s) (F s) z) y) x) x := by
  set Cmix : ℝ := 5 * Real.sqrt 2 / 2 with hCmix
  set Cgrad : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant with hCgrad
  set Cearly : ℝ := Cmix * (t / 4) ^ (-(1 : ℝ)) *
    (Cgrad * (t / 4) ^ (-(1 / 2) : ℝ) * CQ) with hCearly
  set Clate : ℝ := weightedHeatHessConst theta * HQd with hClate
  set bound : ℝ → ℝ := fun s =>
    Cearly + Clate * (t - s) ^ (-1 + theta / 2 : ℝ) with hbound
  have ht4 : 0 < t / 4 := by positivity
  have hCmix_nn : 0 ≤ Cmix := by rw [hCmix]; positivity
  have hCgrad_nn : 0 ≤ Cgrad := by
    rw [hCgrad]
    exact ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hCmix_nn (Real.rpow_nonneg ht4.le _))
      (mul_nonneg (mul_nonneg hCgrad_nn (Real.rpow_nonneg ht4.le _)) hCQ)
  have hClate_nn : 0 ≤ Clate := by
    rw [hClate]
    exact mul_nonneg
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQd
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    rw [hbound]
    have hc : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    exact hc.add
      ((ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Clate)
  let P : ℝ → ℝ → ℝ := fun y s =>
    deriv (fun z => intervalConjugateKernelOperator (t - s) (F s) z) y
  let P' : ℝ → ℝ → ℝ := fun y s =>
    deriv (fun w => deriv
      (fun z => intervalConjugateKernelOperator (t - s) (F s) z) w) y
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hP_meas : ∀ y, AEStronglyMeasurable (P y)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro y
    exact ShenWork.IntervalNeumannFullKernel.intervalConjugateKernelOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound y
  have hsecond : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ
        (fun w => deriv
          (fun z => intervalConjugateKernelOperator (t - s) (F s) z) w) y := by
    intro s hs y hy
    have hlag : 0 < t - s := sub_pos.mpr hs.2
    rcases le_or_gt s (t / 2) with hearly | hlate
    · exact intervalConjugateKernelOperator_hasDerivAt_deriv_of_split
        hlag (hF_cont s hs) (hF_int s) (hF_bound s) hy
    · exact (intervalConjugateKernelOperator_hasDerivAt_deriv_of_deriv
        hlag (hF_cont s hs).continuousOn (hF_deriv s hs)
          (hF_deriv_int s hs) (hF0 s) (hF1 s)
          (measurable_deriv (F s)).aestronglyMeasurable
          (hF_deriv_bound s hlate hs.2) y).differentiableAt
  have hP'_meas : AEStronglyMeasurable (P' x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    exact intervalConjugateKernelOperator_s_dependent_secondDeriv_aestronglyMeasurable_x
      ht hF_meas hF_int hF_bound hx (fun s hs => hsecond s hs x hx)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hDiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun y => P y s) (P' y s) y := by
    filter_upwards [hne] with s hst hs y hy
    rw [Set.uIoc_of_le ht.le] at hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t :=
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hraw := (hsecond s hsIoo y hy).hasDerivAt
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
    · have hhalf_ge : t / 4 ≤ (t - s) / 2 := by linarith
      have hp1 : ((t - s) / 2) ^ (-(1 : ℝ)) ≤
          (t / 4) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht4 hhalf_ge (by norm_num)
      have hp2 : ((t - s) / 2) ^ (-(1 / 2) : ℝ) ≤
          (t / 4) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ht4 hhalf_ge (by norm_num)
      have hraw := intervalConjugateKernelOperator_secondDeriv_abs_le_of_split
        hlag (hF_cont s hsIoo) (hF_int s) (hF_bound s) hy
      have hinner :
          Cgrad * ((t - s) / 2) ^ (-(1 / 2) : ℝ) * CQ ≤
            Cgrad * (t / 4) ^ (-(1 / 2) : ℝ) * CQ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp2 hCgrad_nn) hCQ
      have hearly_bound : |P' y s| ≤ Cearly := by
        dsimp [P']
        refine hraw.trans ?_
        rw [hCearly, hCmix, hCgrad]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hp1 hCmix_nn) hinner
          (mul_nonneg (mul_nonneg hCgrad_nn
            (Real.rpow_nonneg (by linarith : 0 ≤ (t - s) / 2) _)) hCQ)
          (mul_nonneg hCmix_nn (Real.rpow_nonneg ht4.le _))
      rw [hbound]
      exact hearly_bound.trans (le_add_of_nonneg_right
        (mul_nonneg hClate_nn (Real.rpow_nonneg hlag.le _)))
    · have hraw := intervalConjugateKernelOperator_secondDeriv_abs_le_of_deriv_holder
        hlag htheta0 htheta1 (hF_cont s hsIoo).continuousOn
          (hF_deriv s hsIoo) (hF_deriv_int s hsIoo) (hF0 s) (hF1 s)
          (measurable_deriv (F s)).aestronglyMeasurable
          (hF_deriv_bound s hlate hsIoo.2) hHQd
          (hF_deriv_holder s hlate hsIoo.2) hy
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
    (hF_meas := hmeas_evt) (hF_int := hfirst_int x hx)
    (hF'_meas := hP'_meas) (h_bound := hBound)
    (bound_integrable := hbound_int) (h_diff := hDiff)
  exact hresult.2

end ShenWork.Paper2
