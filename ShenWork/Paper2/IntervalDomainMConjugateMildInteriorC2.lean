/-
  Interior second spatial differentiability of every positive-time slice of
  the faithful conjugate mild solution.

  The chemotaxis branch is supplied by the conjugate-kernel C2 interchange.
  The reaction branch uses a late-time Holder modulus derived from the actual
  positive-time gradient bound and the one-sided logistic Lipschitz theorem.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildPositiveTimeC2
import ShenWork.Paper2.IntervalFullDuhamelSpatialC2
import ShenWork.PDE.IntervalLogisticLipschitz

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap (chemFluxMLifted)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)

/-- Endpoint extension for a derivative identified on `(0,1)`: continuity of
the function and of the candidate derivative on `[0,1]` upgrades the interior
`HasDerivAt` statements to `HasDerivWithinAt` everywhere on the closed
interval. -/
theorem hasDerivWithinAt_Icc_of_interior_hasDerivAt
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf'_cont : ContinuousOn f' (Set.Icc (0 : ℝ) 1))
    (hder : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt f (f' x) (Set.Icc (0 : ℝ) 1) x := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) 1) :=
    fun y hy ↦ (hder y hy).differentiableAt.differentiableWithinAt
  have hderiv_eq : ∀ y ∈ Set.Ioo (0 : ℝ) 1, deriv f y = f' y :=
    fun y hy ↦ (hder y hy).deriv
  have hIoo_right : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by norm_num)
  have hIoo_left : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num)
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0
    have hIccR : Set.Icc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Filter.mem_of_superset hIoo_right Set.Ioo_subset_Icc_self
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Icc (0 : ℝ) 1] (0 : ℝ) :=
      (nhdsWithin_le_iff).mpr hIccR
    have hlim' : Tendsto f' (𝓝[>] (0 : ℝ)) (𝓝 (f' 0)) :=
      (hf'_cont 0 h0Icc).tendsto.mono_left hle
    have heq : (fun y ↦ deriv f y) =ᶠ[𝓝[>] (0 : ℝ)] f' := by
      filter_upwards [hIoo_right] with y hy
      exact hderiv_eq y hy
    have hlim : Tendsto (fun y ↦ deriv f y) (𝓝[>] (0 : ℝ)) (𝓝 (f' 0)) :=
      hlim'.congr' heq.symm
    have hIci := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      ((hf_cont 0 h0Icc).mono Set.Ioo_subset_Icc_self) hIoo_right hlim
    exact hIci.mono (fun _ hy ↦ hy.1)
  · rcases eq_or_ne x 1 with hx1 | hx1
    · subst hx1
      have hIccL : Set.Icc (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
        Filter.mem_of_superset hIoo_left Set.Ioo_subset_Icc_self
      have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[Set.Icc (0 : ℝ) 1] (1 : ℝ) :=
        (nhdsWithin_le_iff).mpr hIccL
      have hlim' : Tendsto f' (𝓝[<] (1 : ℝ)) (𝓝 (f' 1)) :=
        (hf'_cont 1 h1Icc).tendsto.mono_left hle
      have heq : (fun y ↦ deriv f y) =ᶠ[𝓝[<] (1 : ℝ)] f' := by
        filter_upwards [hIoo_left] with y hy
        exact hderiv_eq y hy
      have hlim : Tendsto (fun y ↦ deriv f y) (𝓝[<] (1 : ℝ)) (𝓝 (f' 1)) :=
        hlim'.congr' heq.symm
      have hIic := hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
        ((hf_cont 1 h1Icc).mono Set.Ioo_subset_Icc_self) hIoo_left hlim
      exact hIic.mono (fun _ hy ↦ hy.2)
    · have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
      exact (hder x hxIoo).hasDerivWithinAt

/-- A continuous subtype slice has a continuous zero-extension when restricted
back to the physical closed interval. -/
theorem intervalDomainLift_continuousOn_Icc_of_continuous_slice
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos hy]
    exact congr_arg f (Subtype.ext rfl)
  rw [heq]
  exact hf

/-- On every positive-time strip, the actual logistic source is spatially
Holder on the physical interior.  No assumption `1 ≤ alpha` is needed: the
solution is nonnegative and the one-sided scalar reaction is Lipschitz on
`[0,M]`. -/
theorem conjugateMildM_logisticLifted_positiveTime_holder_uniform
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t, τ ≤ t → t ≤ D.T →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |logisticLifted p (D.u t) x - logisticLifted p (D.u t) y| ≤
          H * |x - y| ^ (1 / 4 : ℝ) := by
  obtain ⟨CU, hCU_nn, hUderiv_bound⟩ :=
    conjugateMildM_intervalDomainLift_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas hτ
  obtain ⟨L, hLpos, hL⟩ :=
    ShenWork.IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_nonneg_bounded
      p D.hM
  set H : ℝ := L * CU with hH
  have hH_nn : 0 ≤ H := by rw [hH]; exact mul_nonneg hLpos.le hCU_nn
  refine ⟨H, hH_nn, ?_⟩
  intro t hτt htT x hx y hy
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  have hUdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ U z := by
    intro z hz
    simpa [U] using
      (conjugateMildM_intervalDomainLift_hasDerivAt_interior
        D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
          ht htT hz).differentiableAt
  have hUd_bound : ∀ z ∈ Set.Ioo (0 : ℝ) 1, ‖deriv U z‖ ≤ CU := by
    intro z hz
    simpa [U, Real.norm_eq_abs] using hUderiv_bound t hτt htT z hz
  have hUlip : |U x - U y| ≤ CU * |x - y| :=
    abs_sub_le_mul_abs_sub_of_deriv_bound_Ioo hUdiff hUd_bound hx hy
  have hxIcc := Set.Ioo_subset_Icc_self hx
  have hyIcc := Set.Ioo_subset_Icc_self hy
  have hUx_nn : 0 ≤ U x := by
    simpa [U, intervalDomainLift, hxIcc] using
      D.hc.le.trans (D.hfloor t ht htT ⟨x, hxIcc⟩)
  have hUy_nn : 0 ≤ U y := by
    simpa [U, intervalDomainLift, hyIcc] using
      D.hc.le.trans (D.hfloor t ht htT ⟨y, hyIcc⟩)
  have hUx_le : U x ≤ D.M := by
    have h := D.hbound t ht htT ⟨x, hxIcc⟩
    simpa [U, intervalDomainLift, hxIcc] using (abs_le.mp h).2
  have hUy_le : U y ≤ D.M := by
    have h := D.hbound t ht htT ⟨y, hyIcc⟩
    simpa [U, intervalDomainLift, hyIcc] using (abs_le.mp h).2
  have hscalar := hL (U x) (U y) hUx_nn hUx_le hUy_nn hUy_le
  have hsrc_x : logisticLifted p (D.u t) x =
      U x * (p.a - p.b * (U x) ^ p.α) := by
    simp [logisticLifted,
      ShenWork.IntervalDomainExistence.intervalLogisticSource,
      U, intervalDomainLift, hxIcc]
  have hsrc_y : logisticLifted p (D.u t) y =
      U y * (p.a - p.b * (U y) ^ p.α) := by
    simp [logisticLifted,
      ShenWork.IntervalDomainExistence.intervalLogisticSource,
      U, intervalDomainLift, hyIcc]
  rw [hsrc_x, hsrc_y]
  calc
    |U x * (p.a - p.b * U x ^ p.α) -
        U y * (p.a - p.b * U y ^ p.α)|
        ≤ L * |U x - U y| := hscalar
    _ ≤ L * (CU * |x - y|) :=
      mul_le_mul_of_nonneg_left hUlip hLpos.le
    _ = H * |x - y| := by rw [hH]; ring
    _ ≤ H * |x - y| ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (unitInterval_abs_sub_le_rpow (by norm_num) (by norm_num) hxIcc hyIcc)
        hH_nn

/-- The first spatial derivative of the actual reaction Duhamel leg is
differentiable at every positive-time interior point. -/
theorem conjugateMildM_logisticDuhamel_deriv_hasDerivAt_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y)
      (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) x)
      x := by
  set CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))
  set F : ℝ → ℝ → ℝ := fun s y ↦
    if 0 < s ∧ s ≤ D.T then logisticLifted p (D.u s) y else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = logisticLifted p (D.u s) := by
    intro s hs0 hsT
    funext y
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s y, |F s y| ≤ CL := by
    intro s y
    simp only [hF]
    split_ifs with hs
    · rw [hCL]
      exact logisticLifted_orderBox_bound D.hM D.hbound s hs.1 hs.2 y
    · simpa using hCL_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := logisticLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
        p (D.hbound s hs.1 hs.2) D.hM.le (D.hcont s hs.1 hs.2)
    · simp
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨HQ, hHQ_nn, hQholder⟩ :=
    conjugateMildM_logisticLifted_positiveTime_holder_uniform
      D hu₀ hu₀_meas ht2
  have hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |F s a - F s b| ≤ HQ * |a - b| ^ (1 / 4 : ℝ) := by
    intro s hs2 hst a ha b hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQholder s (le_of_lt hs2) hsT a ha b hb
  have hcut := intervalFullDuhamel_deriv_hasDerivAt_of_late_holder
    ht (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
      hCL_nn hHQ_nn hF_meas hF_int hF_bound hF_holder hx
  have hfun_eq : ∀ y : ℝ,
      (∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y := by
    intro y
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hder_eq :
      (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) x) =
      ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hev :
      (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) =ᶠ[nhds x]
      (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) :=
    Filter.Eventually.of_forall hfun_eq
  exact (hev.hasDerivAt_iff.mpr hcut).congr_deriv hder_eq.symm

/-- The first and second spatial derivative profiles of the actual reaction
Duhamel leg are continuous on the closed physical interval. -/
theorem conjugateMildM_logisticDuhamel_spatialDerivs_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    (ContinuousOn
        (fun x ↦ ∫ s in (0 : ℝ)..t, deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) z) x)
        (Set.Icc (0 : ℝ) 1)) ∧
      ContinuousOn
        (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
          (fun z ↦ intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) z) y) x)
        (Set.Icc (0 : ℝ) 1) := by
  set CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))
  set F : ℝ → ℝ → ℝ := fun s y ↦
    if 0 < s ∧ s ≤ D.T then logisticLifted p (D.u s) y else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = logisticLifted p (D.u s) := by
    intro s hs0 hsT
    funext y
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s y, |F s y| ≤ CL := by
    intro s y
    simp only [hF]
    split_ifs with hs
    · rw [hCL]
      exact logisticLifted_orderBox_bound D.hM D.hbound s hs.1 hs.2 y
    · simpa using hCL_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := logisticLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
        p (D.hbound s hs.1 hs.2) D.hM.le (D.hcont s hs.1 hs.2)
    · simp
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨HQ, hHQ_nn, hQholder⟩ :=
    conjugateMildM_logisticLifted_positiveTime_holder_uniform
      D hu₀ hu₀_meas ht2
  have hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |F s a - F s b| ≤ HQ * |a - b| ^ (1 / 4 : ℝ) := by
    intro s hs2 hst a ha b hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQholder s (le_of_lt hs2) hsT a ha b hb
  have hcut₁ := intervalFullDuhamel_firstDeriv_continuousOn_Icc_of_bounded
    ht hCL_nn hF_meas hF_int hF_bound
  have hcut₂ := intervalFullDuhamel_secondDeriv_continuousOn_Icc_of_late_holder
    ht (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
      hCL_nn hHQ_nn hF_meas hF_int hF_bound hF_holder
  have heq₁ : ∀ x,
      (∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) x) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) x := by
    intro x
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have heq₂ : ∀ x,
      (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) x) =
      ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x := by
    intro x
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  exact ⟨hcut₁.congr (fun x _hx ↦ heq₁ x),
    hcut₂.congr (fun x _hx ↦ heq₂ x)⟩

/-- Closed-interval continuity of the first derivative profile of the actual
reaction Duhamel leg. -/
theorem conjugateMildM_logisticDuhamel_firstDeriv_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) x)
      (Set.Icc (0 : ℝ) 1) :=
  (conjugateMildM_logisticDuhamel_spatialDerivs_continuousOn_Icc
    D hu₀ hu₀_meas ht htT).1

/-- Closed-interval continuity of the second derivative profile of the actual
reaction Duhamel leg. -/
theorem conjugateMildM_logisticDuhamel_secondDeriv_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) x)
      (Set.Icc (0 : ℝ) 1) :=
  (conjugateMildM_logisticDuhamel_spatialDerivs_continuousOn_Icc
    D hu₀ hu₀_meas ht htT).2

/-- Open-interval corollary of the endpoint-closed reaction Hessian theorem. -/
theorem conjugateMildM_logisticDuhamel_secondDeriv_continuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) x)
      (Set.Ioo (0 : ℝ) 1) :=
  (conjugateMildM_logisticDuhamel_secondDeriv_continuousOn_Icc
    D hu₀ hu₀_meas ht htT).mono Set.Ioo_subset_Icc_self

/-- Every positive-time faithful mild slice has a genuine second spatial
derivative at each interior point. -/
theorem conjugateMildM_intervalDomainLift_deriv_hasDerivAt_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ deriv (intervalDomainLift (D.u t)) y)
      ((∫ z, deriv (fun y ↦ deriv
          (fun w ↦ intervalNeumannFullKernel t w z) y) x *
            intervalDomainLift u₀ z ∂(intervalMeasure 1))
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
            (fun z ↦ intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) y) x)
        + ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
            (fun z ↦ intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) y) x)
      x := by
  let I : ℝ → ℝ := fun y ↦
    deriv (fun z ↦ intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y
  let Cleg : ℝ → ℝ := fun y ↦
    ∫ s in (0 : ℝ)..t, deriv
      (fun z ↦ intervalConjugateKernelOperator (t - s)
        (chemFluxMLifted p (D.u s)) z) y
  let Rleg : ℝ → ℝ := fun y ↦
    ∫ s in (0 : ℝ)..t, deriv
      (fun z ↦ intervalFullSemigroupOperator (t - s)
        (logisticLifted p (D.u s)) z) y
  let rhs : ℝ → ℝ := fun y ↦ I y + (-p.χ₀) * Cleg y + Rleg y
  have hinit :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
      ht hu₀_meas hu₀ x
  have hchem := conjugateMildM_chemDuhamel_deriv_hasDerivAt_interior
    D hu₀ hu₀_meas ht htT hx
  have hreact := conjugateMildM_logisticDuhamel_deriv_hasDerivAt_interior
    D hu₀ hu₀_meas ht htT hx
  have hrhs : HasDerivAt rhs
      ((∫ z, deriv (fun y ↦ deriv
          (fun w ↦ intervalNeumannFullKernel t w z) y) x *
            intervalDomainLift u₀ z ∂(intervalMeasure 1))
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
            (fun z ↦ intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) y) x)
        + ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
            (fun z ↦ intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) y) x) x := by
    dsimp [rhs, I, Cleg, Rleg]
    exact (hinit.add (hchem.const_mul (-p.χ₀))).add hreact
  have hev : (fun y ↦ deriv (intervalDomainLift (D.u t)) y) =ᶠ[nhds x] rhs := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have hwhole := conjugateMildM_intervalDomainLift_hasDerivAt_interior
      D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
        ht htT hy
    have hinit_first :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
        ht hu₀_meas hu₀ y
    dsimp [rhs, I, Cleg, Rleg]
    rw [hwhole.deriv, hinit_first.deriv]
  exact hev.hasDerivAt_iff.mpr hrhs

/-- The genuine second spatial derivative of every positive-time faithful
mild slice is continuous on the open physical interval. -/
theorem conjugateMildM_intervalDomainLift_secondDeriv_continuousOn_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn
      (fun x ↦ deriv (fun y ↦ deriv (intervalDomainLift (D.u t)) y) x)
      (Set.Ioo (0 : ℝ) 1) := by
  let I₂ : ℝ → ℝ := fun x ↦ deriv (fun y ↦ deriv
    (fun z ↦ intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y) x
  let C₂ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
    (fun z ↦ intervalConjugateKernelOperator (t - s)
      (chemFluxMLifted p (D.u s)) z) y) x
  let R₂ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
    (fun z ↦ intervalFullSemigroupOperator (t - s)
      (logisticLifted p (D.u s)) z) y) x
  let rhs : ℝ → ℝ := fun x ↦ I₂ x + (-p.χ₀) * C₂ x + R₂ x
  have hu₀_int : Integrable (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound hu₀_meas hu₀
  have hinit : ContinuousOn I₂ (Set.Ioo (0 : ℝ) 1) := by
    exact
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_continuousOn_Icc_of_bounded
        ht hu₀_int hu₀).mono Set.Ioo_subset_Icc_self
  have hchem : ContinuousOn C₂ (Set.Ioo (0 : ℝ) 1) := by
    exact conjugateMildM_chemDuhamel_secondDeriv_continuousOn
      D hu₀ hu₀_meas ht htT
  have hreact : ContinuousOn R₂ (Set.Ioo (0 : ℝ) 1) := by
    exact conjugateMildM_logisticDuhamel_secondDeriv_continuousOn
      D hu₀ hu₀_meas ht htT
  have hrhs : ContinuousOn rhs (Set.Ioo (0 : ℝ) 1) := by
    dsimp [rhs]
    exact (hinit.add (continuousOn_const.mul hchem)).add hreact
  have heq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (fun y ↦ deriv (intervalDomainLift (D.u t)) y) x = rhs x := by
    intro x hx
    have hwhole := conjugateMildM_intervalDomainLift_deriv_hasDerivAt_interior
      D hu₀ hu₀_meas ht htT hx
    have hinit_deriv :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
        ht hu₀_meas hu₀ x
    dsimp [rhs, I₂, C₂, R₂]
    rw [hwhole.deriv, hinit_deriv.deriv]
  exact hrhs.congr (fun x hx ↦ heq x hx)

/-- Every positive-time faithful mild slice is spatially `C²` on the open
physical interval, with no regularity premise beyond the mild-solution data
and the original bounded measurable datum. -/
theorem conjugateMildM_intervalDomainLift_contDiffOn_two_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Ioo (0 : ℝ) 1) := by
  have hdiff : DifferentiableOn ℝ (intervalDomainLift (D.u t))
      (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    exact (conjugateMildM_intervalDomainLift_hasDerivAt_interior
      D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
        ht htT hx).differentiableAt.differentiableWithinAt
  have hderiv_diff : DifferentiableOn ℝ
      (fun x ↦ deriv (intervalDomainLift (D.u t)) x)
      (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    exact (conjugateMildM_intervalDomainLift_deriv_hasDerivAt_interior
      D hu₀ hu₀_meas ht htT hx).differentiableAt.differentiableWithinAt
  have hsecond_cont :=
    conjugateMildM_intervalDomainLift_secondDeriv_continuousOn_interior
      D hu₀ hu₀_meas ht htT
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨hdiff, ?_, ?_⟩
  · norm_num
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨hderiv_diff, ?_, ?_⟩
  · norm_num
  exact contDiffOn_zero.mpr hsecond_cont

/-- Every positive-time faithful mild slice is spatially `C²` on the closed
physical interval.  The endpoint derivatives are obtained by extending the
two interior differentiation identities through the continuous first- and
second-derivative profiles. -/
theorem conjugateMildM_intervalDomainLift_contDiffOn_two_closed
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1) := by
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  let I₁ : ℝ → ℝ := fun x ↦ deriv
    (fun z ↦ intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
  let C₁ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv
    (fun z ↦ intervalConjugateKernelOperator (t - s)
      (chemFluxMLifted p (D.u s)) z) x
  let R₁ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv
    (fun z ↦ intervalFullSemigroupOperator (t - s)
      (logisticLifted p (D.u s)) z) x
  let D₁ : ℝ → ℝ := fun x ↦ I₁ x + (-p.χ₀) * C₁ x + R₁ x
  let I₂ : ℝ → ℝ := fun x ↦ deriv (fun y ↦ deriv
    (fun z ↦ intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y) x
  let C₂ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
    (fun z ↦ intervalConjugateKernelOperator (t - s)
      (chemFluxMLifted p (D.u s)) z) y) x
  let R₂ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
    (fun z ↦ intervalFullSemigroupOperator (t - s)
      (logisticLifted p (D.u s)) z) y) x
  let D₂ : ℝ → ℝ := fun x ↦ I₂ x + (-p.χ₀) * C₂ x + R₂ x
  have hu₀_int : Integrable (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound hu₀_meas hu₀
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    exact intervalDomainLift_continuousOn_Icc_of_continuous_slice
      (D.hcont t ht htT)
  have hI₁cont : ContinuousOn I₁ (Set.Icc (0 : ℝ) 1) := by
    exact
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_continuous_of_bounded
        ht hu₀_meas hu₀).continuousOn
  have hC₁cont : ContinuousOn C₁ (Set.Icc (0 : ℝ) 1) := by
    exact conjugateMildM_chemDuhamel_firstDeriv_continuousOn_Icc
      D hu₀ hu₀_meas ht htT
  have hR₁cont : ContinuousOn R₁ (Set.Icc (0 : ℝ) 1) := by
    exact conjugateMildM_logisticDuhamel_firstDeriv_continuousOn_Icc
      D hu₀ hu₀_meas ht htT
  have hD₁cont : ContinuousOn D₁ (Set.Icc (0 : ℝ) 1) := by
    dsimp [D₁]
    exact (hI₁cont.add (continuousOn_const.mul hC₁cont)).add hR₁cont
  have hI₂cont : ContinuousOn I₂ (Set.Icc (0 : ℝ) 1) := by
    exact
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_continuousOn_Icc_of_bounded
        ht hu₀_int hu₀
  have hC₂cont : ContinuousOn C₂ (Set.Icc (0 : ℝ) 1) := by
    exact conjugateMildM_chemDuhamel_secondDeriv_continuousOn_Icc
      D hu₀ hu₀_meas ht htT
  have hR₂cont : ContinuousOn R₂ (Set.Icc (0 : ℝ) 1) := by
    exact conjugateMildM_logisticDuhamel_secondDeriv_continuousOn_Icc
      D hu₀ hu₀_meas ht htT
  have hD₂cont : ContinuousOn D₂ (Set.Icc (0 : ℝ) 1) := by
    dsimp [D₂]
    exact (hI₂cont.add (continuousOn_const.mul hC₂cont)).add hR₂cont
  have hUder : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (D₁ x) x := by
    intro x hx
    have hwhole := conjugateMildM_intervalDomainLift_hasDerivAt_interior
      D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
        ht htT hx
    have hinit :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
        ht hu₀_meas hu₀ x
    have hcoef :
        ((∫ y, deriv (fun z : ℝ ↦ intervalNeumannFullKernel t z y) x *
            intervalDomainLift u₀ y ∂(intervalMeasure 1))
          + (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
              (fun z ↦ intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (D.u s)) z) x)
          + ∫ s in (0 : ℝ)..t, deriv
              (fun z ↦ intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) z) x) = D₁ x := by
      dsimp [D₁, I₁, C₁, R₁]
      rw [hinit.deriv]
    exact (show HasDerivAt U _ x from hwhole).congr_deriv hcoef
  have hD₁der : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt D₁ (D₂ x) x := by
    intro x hx
    have hinit :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
        ht hu₀_meas hu₀ x
    have hinit' : HasDerivAt I₁ (I₂ x) x := by
      dsimp [I₁, I₂]
      exact hinit.congr_deriv hinit.deriv.symm
    have hchem : HasDerivAt C₁ (C₂ x) x := by
      exact conjugateMildM_chemDuhamel_deriv_hasDerivAt_interior
        D hu₀ hu₀_meas ht htT hx
    have hreact : HasDerivAt R₁ (R₂ x) x := by
      exact conjugateMildM_logisticDuhamel_deriv_hasDerivAt_interior
        D hu₀ hu₀_meas ht htT hx
    dsimp [D₁, D₂]
    exact (hinit'.add (hchem.const_mul (-p.χ₀))).add hreact
  have hUwithin : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt U (D₁ x) (Set.Icc (0 : ℝ) 1) x := by
    intro x hx
    exact hasDerivWithinAt_Icc_of_interior_hasDerivAt
      hUcont hD₁cont hUder hx
  have hD₁within : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt D₁ (D₂ x) (Set.Icc (0 : ℝ) 1) x := by
    intro x hx
    exact hasDerivWithinAt_Icc_of_interior_hasDerivAt
      hD₁cont hD₂cont hD₁der hx
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
    uniqueDiffOn_Icc (by norm_num)
  have hUdiff : DifferentiableOn ℝ U (Set.Icc (0 : ℝ) 1) :=
    fun x hx ↦ (hUwithin x hx).differentiableWithinAt
  have hD₁diff : DifferentiableOn ℝ D₁ (Set.Icc (0 : ℝ) 1) :=
    fun x hx ↦ (hD₁within x hx).differentiableWithinAt
  have hUdw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      derivWithin U (Set.Icc (0 : ℝ) 1) x = D₁ x := by
    intro x hx
    exact (hUwithin x hx).derivWithin (huniq x hx)
  have hD₁dw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      derivWithin D₁ (Set.Icc (0 : ℝ) 1) x = D₂ x := by
    intro x hx
    exact (hD₁within x hx).derivWithin (huniq x hx)
  have hD₁C1 : ContDiffOn ℝ 1 D₁ (Set.Icc (0 : ℝ) 1) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin huniq]
    refine ⟨hD₁diff, ?_, ?_⟩
    · norm_num
    exact (contDiffOn_zero.mpr hD₂cont).congr hD₁dw
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin huniq]
  refine ⟨hUdiff, ?_, ?_⟩
  · norm_num
  exact hD₁C1.congr hUdw

/-- Genuine one-sided homogeneous Neumann limits for every positive-time
faithful mild slice. -/
theorem conjugateMildM_intervalDomainLift_neumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  let I₁ : ℝ → ℝ := fun x ↦ deriv
    (fun z ↦ intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x
  let C₁ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv
    (fun z ↦ intervalConjugateKernelOperator (t - s)
      (chemFluxMLifted p (D.u s)) z) x
  let R₁ : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..t, deriv
    (fun z ↦ intervalFullSemigroupOperator (t - s)
      (logisticLifted p (D.u s)) z) x
  let D₁ : ℝ → ℝ := fun x ↦ I₁ x + (-p.χ₀) * C₁ x + R₁ x
  have hI₁cont : ContinuousOn I₁ (Set.Icc (0 : ℝ) 1) := by
    exact
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_continuous_of_bounded
        ht hu₀_meas hu₀).continuousOn
  have hC₁cont : ContinuousOn C₁ (Set.Icc (0 : ℝ) 1) := by
    exact conjugateMildM_chemDuhamel_firstDeriv_continuousOn_Icc
      D hu₀ hu₀_meas ht htT
  have hR₁cont : ContinuousOn R₁ (Set.Icc (0 : ℝ) 1) := by
    exact conjugateMildM_logisticDuhamel_firstDeriv_continuousOn_Icc
      D hu₀ hu₀_meas ht htT
  have hD₁cont : ContinuousOn D₁ (Set.Icc (0 : ℝ) 1) := by
    dsimp [D₁]
    exact (hI₁cont.add (continuousOn_const.mul hC₁cont)).add hR₁cont
  have hder_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv U x = D₁ x := by
    intro x hx
    have hwhole := conjugateMildM_intervalDomainLift_hasDerivAt_interior
      D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
        ht htT hx
    have hinit :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
        ht hu₀_meas hu₀ x
    dsimp [U, D₁, I₁, C₁, R₁]
    rw [hwhole.deriv, hinit.deriv]
  have hI₁0 : I₁ 0 = 0 := by
    exact ShenWork.intervalFullSemigroupOperator_deriv_at_zero_eq_zero
      t (intervalDomainLift u₀)
  have hI₁1 : I₁ 1 = 0 := by
    exact ShenWork.intervalFullSemigroupOperator_deriv_at_one_eq_zero
      t (intervalDomainLift u₀)
  have hC₁0 : C₁ 0 = 0 := by
    dsimp [C₁]
    rw [show (fun s ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) 0) = fun _ ↦ 0 from by
      funext s
      exact ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_deriv_at_zero_eq_zero
        (t - s) (chemFluxMLifted p (D.u s))]
    simp
  have hC₁1 : C₁ 1 = 0 := by
    dsimp [C₁]
    rw [show (fun s ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) 1) = fun _ ↦ 0 from by
      funext s
      exact ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_deriv_at_one_eq_zero
        (t - s) (chemFluxMLifted p (D.u s))]
    simp
  have hR₁0 : R₁ 0 = 0 := by
    dsimp [R₁]
    rw [show (fun s ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) 0) = fun _ ↦ 0 from by
      funext s
      exact ShenWork.intervalFullSemigroupOperator_deriv_at_zero_eq_zero
        (t - s) (logisticLifted p (D.u s))]
    simp
  have hR₁1 : R₁ 1 = 0 := by
    dsimp [R₁]
    rw [show (fun s ↦ deriv
        (fun z ↦ intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) 1) = fun _ ↦ 0 from by
      funext s
      exact ShenWork.intervalFullSemigroupOperator_deriv_at_one_eq_zero
        (t - s) (logisticLifted p (D.u s))]
    simp
  have hD₁0 : D₁ 0 = 0 := by
    dsimp [D₁]
    rw [hI₁0, hC₁0, hR₁0]
    ring
  have hD₁1 : D₁ 1 = 0 := by
    dsimp [D₁]
    rw [hI₁1, hC₁1, hR₁1]
    ring
  have hIoo_right : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by norm_num)
  have hIoo_left : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num)
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  constructor
  · have hIccR : Set.Icc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Filter.mem_of_superset hIoo_right Set.Ioo_subset_Icc_self
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Icc (0 : ℝ) 1] (0 : ℝ) :=
      (nhdsWithin_le_iff).mpr hIccR
    have hlim : Tendsto D₁ (𝓝[>] (0 : ℝ)) (𝓝 (D₁ 0)) :=
      (hD₁cont 0 h0Icc).tendsto.mono_left hle
    rw [hD₁0] at hlim
    have heq : (fun x ↦ deriv U x) =ᶠ[𝓝[>] (0 : ℝ)] D₁ := by
      filter_upwards [hIoo_right] with x hx
      exact hder_eq x hx
    exact hlim.congr' heq.symm
  · have hIccL : Set.Icc (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
      Filter.mem_of_superset hIoo_left Set.Ioo_subset_Icc_self
    have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[Set.Icc (0 : ℝ) 1] (1 : ℝ) :=
      (nhdsWithin_le_iff).mpr hIccL
    have hlim : Tendsto D₁ (𝓝[<] (1 : ℝ)) (𝓝 (D₁ 1)) :=
      (hD₁cont 1 h1Icc).tendsto.mono_left hle
    rw [hD₁1] at hlim
    have heq : (fun x ↦ deriv U x) =ᶠ[𝓝[<] (1 : ℝ)] D₁ := by
      filter_upwards [hIoo_left] with x hx
      exact hder_eq x hx
    exact hlim.congr' heq.symm

/-- Closed spatial `C²` together with the endpoint ordinary-derivative values
required by the classical-regularity record. -/
theorem conjugateMildM_intervalDomainLift_closedC2_endpointDerivs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1) ∧
      deriv (intervalDomainLift (D.u t)) 0 = 0 ∧
      deriv (intervalDomainLift (D.u t)) 1 = 0 := by
  exact ⟨conjugateMildM_intervalDomainLift_contDiffOn_two_closed
      D hu₀ hu₀_meas ht htT,
    ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_zero _,
    ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_one _⟩

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_intervalDomainLift_contDiffOn_two_closed
#print axioms ShenWork.Paper2.conjugateMildM_intervalDomainLift_closedC2_endpointDerivs
