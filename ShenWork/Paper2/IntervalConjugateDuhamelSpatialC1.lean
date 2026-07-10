/-
  Spatial differentiation of the faithful conjugate-kernel Duhamel leg.

  The time interval is split analytically at t/2.  On the early half the lag
  stays uniformly positive and the bounded-data t^{-1} estimate is harmless.
  On the late half the endpoint-zero C^theta cancellation estimate gives the
  integrable rate (t-s)^{-1+theta/2}.
-/
import ShenWork.Paper2.IntervalConjugateKernelCtheta
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.Paper2.ChemMildInterchange

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateDuhamelMap

/-! ## Measurability of the lagged mixed Hessian -/

/-- The mixed full-kernel Hessian lattice is jointly measurable in `(s,y)`. -/
theorem mixedDeriv_intervalNeumannFullKernel_s_dependent_measurable
    (t x₀ : ℝ) :
    Measurable (fun w : ℝ × ℝ =>
      -(∑' k : ℤ,
        deriv (fun u : ℝ => deriv
          (fun z : ℝ => heatKernel (t - w.1) z) u)
          (x₀ - w.2 + 2 * (k : ℝ))) +
      (∑' k : ℤ,
        deriv (fun u : ℝ => deriv
          (fun z : ℝ => heatKernel (t - w.1) z) u)
          (x₀ + w.2 + 2 * (k : ℝ)))) := by
  set g₁ : ℤ → ℝ × ℝ → ℝ := fun k w =>
    deriv (fun u : ℝ => deriv
      (fun z : ℝ => heatKernel (t - w.1) z) u)
      (x₀ - w.2 + 2 * (k : ℝ)) with hg₁
  set g₂ : ℤ → ℝ × ℝ → ℝ := fun k w =>
    deriv (fun u : ℝ => deriv
      (fun z : ℝ => heatKernel (t - w.1) z) u)
      (x₀ + w.2 + 2 * (k : ℝ)) with hg₂
  have hg₁_meas : ∀ k, Measurable (g₁ k) := fun _ =>
    ShenWork.Paper2.measurable_secondDeriv_heatKernel_comp (by fun_prop) t
  have hg₂_meas : ∀ k, Measurable (g₂ k) := fun _ =>
    ShenWork.Paper2.measurable_secondDeriv_heatKernel_comp (by fun_prop) t
  have hsum_aux : ∀ (z : ℝ) (w : ℝ × ℝ),
      Summable (fun k : ℤ =>
        deriv (fun u : ℝ => deriv
          (fun v : ℝ => heatKernel (t - w.1) v) u)
          (z + 2 * (k : ℝ))) := by
    intro z w
    rcases lt_or_ge 0 (t - w.1) with hτ | hτ
    · exact latticeGaussianHessSummable hτ z
    · have hz : (fun k : ℤ =>
          deriv (fun u : ℝ => deriv
            (fun v : ℝ => heatKernel (t - w.1) v) u)
            (z + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
        funext k
        have hzero : (fun v : ℝ => heatKernel (t - w.1) v) =
            fun _ : ℝ => (0 : ℝ) := by
          funext v
          exact heatKernel_of_nonpos hτ v
        have hzero' : (fun u : ℝ => deriv
            (fun v : ℝ => heatKernel (t - w.1) v) u) =
            fun _ : ℝ => (0 : ℝ) := by
          funext u
          rw [hzero, deriv_const]
        rw [hzero', deriv_const]
      rw [hz]
      exact summable_zero
  have hg₁_sum : ∀ w, Summable (fun k : ℤ => g₁ k w) :=
    fun w => hsum_aux (x₀ - w.2) w
  have hg₂_sum : ∀ w, Summable (fun k : ℤ => g₂ k w) :=
    fun w => hsum_aux (x₀ + w.2) w
  exact (measurable_tsum_int_of_summable hg₁_meas hg₁_sum).neg.add
    (measurable_tsum_int_of_summable hg₂_meas hg₂_sum)

/-- The derivative of the lagged conjugate operator is measurable in the time
parameter for a jointly measurable bounded source family. -/
theorem intervalConjugateKernelOperator_s_dependent_deriv_aestronglyMeasurable_x₀
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    {C : ℝ} (hF_bound : ∀ s y, |F s y| ≤ C) (x₀ : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x₀)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  set Kmix : ℝ × ℝ → ℝ := fun w =>
    -(∑' k : ℤ,
      deriv (fun u : ℝ => deriv
        (fun z : ℝ => heatKernel (t - w.1) z) u)
        (x₀ - w.2 + 2 * (k : ℝ))) +
    (∑' k : ℤ,
      deriv (fun u : ℝ => deriv
        (fun z : ℝ => heatKernel (t - w.1) z) u)
        (x₀ + w.2 + 2 * (k : ℝ))) with hKmix
  have hKmix_meas : Measurable Kmix := by
    simpa [Kmix] using
      mixedDeriv_intervalNeumannFullKernel_s_dependent_measurable t x₀
  set D : ℝ → ℝ := fun s =>
    -(∫ y, Kmix (s, y) * F s y ∂(intervalMeasure 1)) with hD
  have hD_meas : AEStronglyMeasurable D
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    have hprod : AEStronglyMeasurable
        (fun w : ℝ × ℝ => Kmix w * F w.1 w.2)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
      hKmix_meas.aestronglyMeasurable.mul hF_ae
    exact (AEStronglyMeasurable.integral_prod_right'
      (μ := volume.restrict (Set.uIoc (0 : ℝ) t))
      (ν := intervalMeasure 1) hprod).neg
  refine hD_meas.congr ?_
  have huIoc : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
    Set.uIoc_of_le ht.le
  have hae_lt : ∀ᵐ s ∂(volume.restrict (Set.uIoc (0 : ℝ) t)), s < t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2 ?_
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne] with s hsne hs
    rw [huIoc] at hs
    exact lt_of_le_of_ne hs.2 hsne
  filter_upwards [hae_lt] with s hst
  have hlag : 0 < t - s := sub_pos.mpr hst
  have hOp := (intervalConjugateKernelOperator_hasDerivAt
    hlag (hF_int s) (hF_bound s) x₀).deriv
  rw [hOp]
  dsimp [D]
  congr 1
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  change Kmix (s, y) * F s y =
    deriv (fun z : ℝ => deriv
      (fun y' : ℝ => intervalNeumannFullKernel (t - s) z y') y) x₀ * F s y
  congr 1
  exact (hasDerivAt_deriv_intervalNeumannFullKernel_snd_fst hlag x₀ y).deriv.symm

/-! ## Spatial differentiation under the Duhamel time integral -/

/-- The faithful conjugate Duhamel leg is differentiable at every interior
spatial point.  Only late-time slices need Holder regularity. -/
theorem intervalConjugateDuhamel_hasDerivAt_fst_of_late_holder
    {t θ CQ HQ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_cont : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1))
    (hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |F s a - F s b| ≤ HQ * |a - b| ^ θ)
    (hF0 : ∀ s, F s 0 = 0) (hF1 : ∀ s, F s 1 = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (F s) x)
      (∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x₀)
      x₀ := by
  set Cmix : ℝ := 5 * Real.sqrt 2 / 2 with hCmix
  set Cearly : ℝ := Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ with hCearly
  set Clate : ℝ := 2 * HQ * weightedHeatHessConst θ with hClate
  set bound : ℝ → ℝ := fun s =>
    Cearly + Clate * (t - s) ^ (-1 + θ / 2 : ℝ) with hbound
  have hCmix_nn : 0 ≤ Cmix := by rw [hCmix]; positivity
  have ht2 : 0 < t / 2 := by positivity
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hCmix_nn (Real.rpow_nonneg ht2.le _)) hCQ
  have hClate_nn : 0 ≤ Clate := by
    rw [hClate]
    exact mul_nonneg (mul_nonneg (by norm_num) hHQ)
      (weightedHeatHessConst_nonneg θ)
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    rw [hbound]
    have hc : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    have hl : IntervalIntegrable
        (fun s : ℝ => Clate * (t - s) ^ (-1 + θ / 2 : ℝ)) volume 0 t :=
      (intervalIntegrable_sub_rpow_hessian (t := t) hθ0).const_mul Clate
    exact hc.add hl
  let Fp : ℝ → ℝ → ℝ := fun x s =>
    intervalConjugateKernelOperator (t - s) (F s) x
  let Fp' : ℝ → ℝ → ℝ := fun x s =>
    deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hFp_meas : ∀ x : ℝ, AEStronglyMeasurable (Fp x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro x
    have h :=
      ShenWork.IntervalConjugateChemFluxIntegrable.intervalConjugateKernelOperator_lag_aestronglyMeasurable
        (t := t) (x := x) hF_meas
    have hu : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t := Set.uIoc_of_le ht.le
    rw [hu]
    exact h.mono_measure
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  have hFp_int : IntervalIntegrable (Fp x₀) volume 0 t := by
    exact ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      ht hCQ hF_meas hF_int hF_bound
  have hFp'_meas : AEStronglyMeasurable (Fp' x₀)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    intervalConjugateKernelOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound x₀
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have huIoc : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
    Set.uIoc_of_le ht.le
  have hDiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun x => Fp x s) (Fp' x s) x := by
    filter_upwards [hne] with s hsne hs x hx
    rw [huIoc] at hs
    have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsne)
    have h := intervalConjugateKernelOperator_hasDerivAt
      hlag (hF_int s) (hF_bound s) x
    simpa [Fp, Fp'] using h.congr_deriv h.deriv.symm
  have hBound : ∀ᵐ s ∂volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, ‖Fp' x s‖ ≤ bound s := by
    filter_upwards [hne] with s hsne hs x hx
    rw [huIoc] at hs
    have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsne)
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hlate_nonneg : 0 ≤ Clate * (t - s) ^ (-1 + θ / 2 : ℝ) :=
      mul_nonneg hClate_nn (Real.rpow_nonneg hlag.le _)
    rw [Real.norm_eq_abs]
    rcases le_or_gt s (t / 2) with hs_early | hs_late
    · have hlag_ge : t / 2 ≤ t - s := by linarith
      have hpow : (t - s) ^ (-(1 : ℝ)) ≤ (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht2 hlag_ge (by norm_num)
      have hraw := intervalConjugateKernelOperator_deriv_abs_le
        hlag (hF_int s) (hF_bound s) x
      have hearly : |Fp' x s| ≤ Cearly := by
        dsimp [Fp']
        refine hraw.trans ?_
        rw [hCearly, hCmix]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hCmix_nn) hCQ
      rw [hbound]
      linarith
    · have hraw := intervalConjugateKernelOperator_deriv_Ctheta_to_Linfty
        hlag hθ0 hθ1 (hF_int s) (hF_bound s)
        (hF_cont s hs_late (lt_of_le_of_ne hs.2 hsne)) hHQ
        (hF_holder s hs_late (lt_of_le_of_ne hs.2 hsne))
        (hF0 s) (hF1 s) hxIcc
      have hlate : |Fp' x s| ≤
          Clate * (t - s) ^ (-1 + θ / 2 : ℝ) := by
        dsimp [Fp']
        rw [hClate]
        simpa [mul_assoc] using hraw
      rw [hbound]
      linarith [hCearly_nn]
  have hmeas_evt : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (Fp x)
        (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    Filter.Eventually.of_forall hFp_meas
  have hresult := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := t)
    (F := Fp) (F' := Fp') (x₀ := x₀)
    (s := Set.Ioo (0 : ℝ) 1) (bound := bound)
    (hs := isOpen_Ioo.mem_nhds hx₀)
    (hF_meas := hmeas_evt) (hF_int := hFp_int)
    (hF'_meas := hFp'_meas) (h_bound := hBound)
    (bound_integrable := hbound_int) (h_diff := hDiff)
  exact hresult.2

/-- The differentiated faithful conjugate Duhamel leg has a uniform spatial
bound.  The same early/late envelope as in the differentiation theorem is
integrated in time; the returned constant is deliberately existential because
downstream bootstraps only need finiteness and nonnegativity. -/
theorem intervalConjugateDuhamel_deriv_integral_uniformBound_of_late_holder
    {t θ CQ HQ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_cont : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1))
    (hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |F s a - F s b| ≤ HQ * |a - b| ^ θ)
    (hF0 : ∀ s, F s 0 = 0) (hF1 : ∀ s, F s 1 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x| ≤ C := by
  set Cmix : ℝ := 5 * Real.sqrt 2 / 2 with hCmix
  set Cearly : ℝ := Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ with hCearly
  set Clate : ℝ := 2 * HQ * weightedHeatHessConst θ with hClate
  set bound : ℝ → ℝ := fun s =>
    Cearly + Clate * (t - s) ^ (-1 + θ / 2 : ℝ) with hbound
  have hCmix_nn : 0 ≤ Cmix := by rw [hCmix]; positivity
  have ht2 : 0 < t / 2 := by positivity
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hCmix_nn (Real.rpow_nonneg ht2.le _)) hCQ
  have hClate_nn : 0 ≤ Clate := by
    rw [hClate]
    exact mul_nonneg (mul_nonneg (by norm_num) hHQ)
      (weightedHeatHessConst_nonneg θ)
  have hbound_int : IntervalIntegrable bound volume 0 t := by
    rw [hbound]
    have hc : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    have hl :=
      (intervalIntegrable_sub_rpow_hessian (t := t) hθ0).const_mul Clate
    exact hc.add hl
  have hpt : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x|
        ≤ bound s := by
    intro s hs x hx
    have hlag : 0 < t - s := sub_pos.mpr hs.2
    have hlate_nonneg : 0 ≤ Clate * (t - s) ^ (-1 + θ / 2 : ℝ) :=
      mul_nonneg hClate_nn (Real.rpow_nonneg hlag.le _)
    rcases le_or_gt s (t / 2) with hs_early | hs_late
    · have hlag_ge : t / 2 ≤ t - s := by linarith
      have hpow : (t - s) ^ (-(1 : ℝ)) ≤ (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht2 hlag_ge (by norm_num)
      have hraw := intervalConjugateKernelOperator_deriv_abs_le
        hlag (hF_int s) (hF_bound s) x
      have hearly :
          |deriv (fun z : ℝ =>
            intervalConjugateKernelOperator (t - s) (F s) z) x| ≤ Cearly := by
        refine hraw.trans ?_
        rw [hCearly, hCmix]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hCmix_nn) hCQ
      rw [hbound]
      linarith
    · have hraw := intervalConjugateKernelOperator_deriv_Ctheta_to_Linfty
        hlag hθ0 hθ1 (hF_int s) (hF_bound s)
        (hF_cont s hs_late hs.2) hHQ (hF_holder s hs_late hs.2)
        (hF0 s) (hF1 s) hx
      have hlate :
          |deriv (fun z : ℝ =>
            intervalConjugateKernelOperator (t - s) (F s) z) x| ≤
            Clate * (t - s) ^ (-1 + θ / 2 : ℝ) := by
        rw [hClate]
        simpa [mul_assoc] using hraw
      rw [hbound]
      linarith [hCearly_nn]
  refine ⟨|∫ s in (0 : ℝ)..t, bound s|, abs_nonneg _, ?_⟩
  intro x hx
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hder_meas : AEStronglyMeasurable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    intervalConjugateKernelOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hF_ae hF_int hF_bound x
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hdom_ae : ∀ᵐ s ∂(volume.restrict (Set.uIoc (0 : ℝ) t)),
      ‖deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x‖
        ≤ bound s := by
    rw [Set.uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with s hst hs
    rw [Real.norm_eq_abs]
    exact hpt s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩ x hx
  have hder_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x)
      volume 0 t := by
    rw [intervalIntegrable_iff] at hbound_int ⊢
    exact Integrable.mono' hbound_int hder_meas hdom_ae
  calc
    |∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x|
        ≤ ∫ s in (0 : ℝ)..t,
            |deriv (fun z : ℝ =>
              intervalConjugateKernelOperator (t - s) (F s) z) x| :=
          intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, bound s :=
      intervalIntegral.integral_mono_on_of_le_Ioo ht.le hder_int.abs hbound_int
        (fun s hs => hpt s hs x hx)
    _ ≤ |∫ s in (0 : ℝ)..t, bound s| := le_abs_self _

end ShenWork.IntervalNeumannFullKernel
