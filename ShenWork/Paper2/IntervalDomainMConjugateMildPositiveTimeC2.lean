/-
  Positive-time interior second spatial differentiability of the faithful
  conjugate chemotaxis Duhamel leg.

  Every analytic hypothesis of the generic second-Duhamel interchange is
  discharged from `ConjugateMildSolutionDataM`: boundedness and measurability
  from the order box, first-derivative control from the positive-time C1
  bootstrap, and the late-time derivative Holder modulus from the physical
  resolver ODE.
-/
import ShenWork.Paper2.IntervalConjugateDuhamelSpatialC2
import ShenWork.Paper2.IntervalDomainMConjugateMildPositiveTimeFluxC1eta

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted chemFluxMLifted_abs_le_of_pos_slice
   chemFluxMLifted_uncurry_measurable chemFluxMLifted_integrable_of_pos_slice
   chemFluxMLifted_continuousOn_Icc_of_pos_slice
   chemFluxMLifted_continuous_of_pos_slice
   chemFluxMLifted_endpoint_zero chemFluxMLifted_endpoint_one)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)

/-- The first spatial derivative of the actual chemotaxis Duhamel leg is
differentiable at every positive-time interior point, and its second spatial
derivative time integrand is interval-integrable. -/
theorem conjugateMildM_chemDuhamel_deriv_hasDerivAt_and_secondDeriv_intervalIntegrable_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (IntervalIntegrable
        (fun s ↦ deriv (fun y ↦ deriv
          (fun z ↦ intervalConjugateKernelOperator (t - s)
            (chemFluxMLifted p (D.u s)) z) y) x)
        volume 0 t) ∧
      HasDerivAt
        (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
          (fun z ↦ intervalConjugateKernelOperator (t - s)
            (chemFluxMLifted p (D.u s)) z) y)
        (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
          (fun z ↦ intervalConjugateKernelOperator (t - s)
            (chemFluxMLifted p (D.u s)) z) y) x)
        x := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set CQ : ℝ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set F : ℝ → ℝ → ℝ := fun s z ↦
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) z else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxMLifted p (D.u s) := by
    intro s hs0 hsT
    funext z
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s z, |F s z| ≤ CQ := by
    intro s z
    simp only [hF]
    split_ifs with hs
    · rw [hCQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) z
    · simpa using hCQ_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨HQ, hHQ_nn, hQholder⟩ :=
    conjugateMildM_chemFlux_positiveTime_holder D hu₀ hu₀_meas
      (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num) ht2
  obtain ⟨CQd, hCQd_nn, hQderiv_bound⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas ht2
  obtain ⟨eta, HQd, heta0, heta1, hHQd_nn, hQderiv_holder⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_holder_uniform
      D hu₀ hu₀_meas ht2
  have hF_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t, Continuous (F s) := by
    intro s hs
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact chemFluxMLifted_continuous_of_pos_slice p D.hc hcM
      (D.hbound s hs.1 hsT) (D.hfloor s hs.1 hsT) (D.hcont s hs.1 hsT)
  have hF_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (F s) (deriv (F s) z) z := by
    intro s hs z hz
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact (conjugateMildM_chemFlux_differentiableAt_interior
      D hu₀ hu₀_meas hs.1 hsT hz).hasDerivAt
  have hF_deriv_int : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      IntervalIntegrable (deriv (F s)) volume 0 1 := by
    intro s hs
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact conjugateMildM_chemFlux_deriv_intervalIntegrable
      D hu₀ hu₀_meas hs.1 hsT
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_zero
        p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_one
        p (D.u s)
    · rfl
  have hF_deriv_bound : ∀ s, t / 2 < s → s < t →
      ∀ z, |deriv (F s) z| ≤ CQd := by
    intro s hs2 hst z
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
    · exact hQderiv_bound s (le_of_lt hs2) hsT z hz
    · rw [chemFluxMLifted_deriv_eq_zero_off_Ioo p (D.u s) hz, abs_zero]
      exact hCQd_nn
  have hF_deriv_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (F s) a - deriv (F s) b| ≤ HQd * |a - b| ^ eta := by
    intro s hs2 hst a ha b hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQderiv_holder s (le_of_lt hs2) hsT a ha b hb
  have hF_cont_late : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs2 hst
    exact (hF_cont s ⟨lt_trans ht2 hs2, hst⟩).continuousOn
  have hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |F s a - F s b| ≤ HQ * |a - b| ^ (1 / 4 : ℝ) := by
    intro s hs2 hst a b ha hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQholder s ⟨le_of_lt hs2, hsT⟩ a b ha hb
  have hfirst_int : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      IntervalIntegrable
        (fun s ↦ deriv
          (fun w ↦ intervalConjugateKernelOperator (t - s) (F s) w) z)
        volume 0 t := by
    intro z hz
    exact ShenWork.IntervalNeumannFullKernel.intervalConjugateDuhamel_deriv_intervalIntegrable_of_late_holder
      ht (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
        hCQ_nn hHQ_nn hF_meas hF_int hF_bound hF_cont_late hF_holder hF0 hF1
        z (Set.Ioo_subset_Icc_self hz)
  have hcut :=
    intervalConjugateDuhamel_deriv_hasDerivAt_and_secondDeriv_intervalIntegrable_of_late_deriv_holder
    ht heta0 heta1 hCQ_nn hHQd_nn hF_meas hF_int hF_bound hF_cont
      hF_deriv hF_deriv_int hF0 hF1 hF_deriv_bound hF_deriv_holder
      hfirst_int hx
  have hfun_eq : ∀ y : ℝ,
      (∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s) (F s) z) y := by
    intro y
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hder_eq :
      (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x) =
      ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s) (F s) z) y) x := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hev :
      (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) =ᶠ[nhds x]
      (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s) (F s) z) y) :=
    Filter.Eventually.of_forall hfun_eq
  have hsecond_int : IntervalIntegrable
      (fun s ↦ deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x)
      volume 0 t := by
    refine hcut.1.congr (fun s hs ↦ ?_)
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  exact ⟨hsecond_int, (hev.hasDerivAt_iff.mpr hcut.2).congr_deriv hder_eq.symm⟩

/-- The second spatial derivative integrand of the actual chemotaxis
Duhamel leg is integrable in time at each interior spatial point. -/
theorem conjugateMildM_chemDuhamel_secondDeriv_intervalIntegrable_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s ↦ deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x)
      volume 0 t :=
  (conjugateMildM_chemDuhamel_deriv_hasDerivAt_and_secondDeriv_intervalIntegrable_interior
    D hu₀ hu₀_meas ht htT hx).1

/-- The second spatial derivative integrand of the actual chemotaxis Duhamel
leg is integrable in time at every point of the closed physical interval.
At the endpoints this uses the reflected closed-point Hessian bounds, not an
ordinary derivative of the zero-extended flux. -/
theorem conjugateMildM_chemDuhamel_secondDeriv_intervalIntegrable_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s ↦ deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x)
      volume 0 t := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set CQ : ℝ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set F : ℝ → ℝ → ℝ := fun s z ↦
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) z else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxMLifted p (D.u s) := by
    intro s hs0 hsT
    funext z
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s z, |F s z| ≤ CQ := by
    intro s z
    simp only [hF]
    split_ifs with hs
    · rw [hCQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) z
    · simpa using hCQ_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨CQd, hCQd_nn, hQderiv_bound⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas ht2
  obtain ⟨eta, HQd, heta0, heta1, hHQd_nn, hQderiv_holder⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_holder_uniform
      D hu₀ hu₀_meas ht2
  have hF_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t, Continuous (F s) := by
    intro s hs
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact chemFluxMLifted_continuous_of_pos_slice p D.hc hcM
      (D.hbound s hs.1 hsT) (D.hfloor s hs.1 hsT) (D.hcont s hs.1 hsT)
  have hF_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (F s) (deriv (F s) z) z := by
    intro s hs z hz
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact (conjugateMildM_chemFlux_differentiableAt_interior
      D hu₀ hu₀_meas hs.1 hsT hz).hasDerivAt
  have hF_deriv_int : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      IntervalIntegrable (deriv (F s)) volume 0 1 := by
    intro s hs
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact conjugateMildM_chemFlux_deriv_intervalIntegrable
      D hu₀ hu₀_meas hs.1 hsT
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_zero
        p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_one
        p (D.u s)
    · rfl
  have hF_deriv_bound : ∀ s, t / 2 < s → s < t →
      ∀ z, |deriv (F s) z| ≤ CQd := by
    intro s hs2 hst z
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
    · exact hQderiv_bound s (le_of_lt hs2) hsT z hz
    · rw [chemFluxMLifted_deriv_eq_zero_off_Ioo p (D.u s) hz, abs_zero]
      exact hCQd_nn
  have hF_deriv_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (F s) a - deriv (F s) b| ≤ HQd * |a - b| ^ eta := by
    intro s hs2 hst a ha b hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQderiv_holder s (le_of_lt hs2) hsT a ha b hb
  have hcut :=
    intervalConjugateDuhamel_secondDeriv_intervalIntegrable_Icc_of_late_deriv_holder
      ht heta0 heta1 hCQ_nn hHQd_nn hF_meas hF_int hF_bound hF_cont
        hF_deriv hF_deriv_int hF0 hF1 hF_deriv_bound hF_deriv_holder hx
  refine hcut.congr (fun s hs ↦ ?_)
  rw [Set.uIoc_of_le ht.le] at hs
  rw [hF_eq hs.1 (hs.2.trans htT)]

/-- The first spatial derivative of the actual chemotaxis Duhamel leg is
differentiable at every positive-time interior point. -/
theorem conjugateMildM_chemDuhamel_deriv_hasDerivAt_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y)
      (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x)
      x :=
  (conjugateMildM_chemDuhamel_deriv_hasDerivAt_and_secondDeriv_intervalIntegrable_interior
    D hu₀ hu₀_meas ht htT hx).2

/-- The first and second spatial derivative profiles of the actual
chemotaxis Duhamel leg are continuous on the closed physical interval. -/
theorem conjugateMildM_chemDuhamel_spatialDerivs_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    (ContinuousOn
        (fun x ↦ ∫ s in (0 : ℝ)..t, deriv
          (fun z ↦ intervalConjugateKernelOperator (t - s)
            (chemFluxMLifted p (D.u s)) z) x)
        (Set.Icc (0 : ℝ) 1)) ∧
      ContinuousOn
        (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
          (fun z ↦ intervalConjugateKernelOperator (t - s)
            (chemFluxMLifted p (D.u s)) z) y) x)
        (Set.Icc (0 : ℝ) 1) := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set CQ : ℝ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set F : ℝ → ℝ → ℝ := fun s z ↦
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) z else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxMLifted p (D.u s) := by
    intro s hs0 hsT
    funext z
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s z, |F s z| ≤ CQ := by
    intro s z
    simp only [hF]
    split_ifs with hs
    · rw [hCQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) z
    · simpa using hCQ_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨CQd, hCQd_nn, hQderiv_bound⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas ht2
  obtain ⟨eta, HQd, heta0, heta1, hHQd_nn, hQderiv_holder⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_holder_uniform
      D hu₀ hu₀_meas ht2
  have hF_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t, Continuous (F s) := by
    intro s hs
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact chemFluxMLifted_continuous_of_pos_slice p D.hc hcM
      (D.hbound s hs.1 hsT) (D.hfloor s hs.1 hsT) (D.hcont s hs.1 hsT)
  have hF_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (F s) (deriv (F s) z) z := by
    intro s hs z hz
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact (conjugateMildM_chemFlux_differentiableAt_interior
      D hu₀ hu₀_meas hs.1 hsT hz).hasDerivAt
  have hF_deriv_int : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      IntervalIntegrable (deriv (F s)) volume 0 1 := by
    intro s hs
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    rw [hF_eq hs.1 hsT]
    exact conjugateMildM_chemFlux_deriv_intervalIntegrable
      D hu₀ hu₀_meas hs.1 hsT
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_zero
        p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_one
        p (D.u s)
    · rfl
  have hF_deriv_bound : ∀ s, t / 2 < s → s < t →
      ∀ z, |deriv (F s) z| ≤ CQd := by
    intro s hs2 hst z
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
    · exact hQderiv_bound s (le_of_lt hs2) hsT z hz
    · rw [chemFluxMLifted_deriv_eq_zero_off_Ioo p (D.u s) hz, abs_zero]
      exact hCQd_nn
  have hF_deriv_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (F s) a - deriv (F s) b| ≤ HQd * |a - b| ^ eta := by
    intro s hs2 hst a ha b hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQderiv_holder s (le_of_lt hs2) hsT a ha b hb
  have hcut₁ := intervalConjugateDuhamel_firstDeriv_continuousOn_Icc_of_late_deriv_bound
    ht hCQ_nn hCQd_nn hF_meas hF_int hF_bound hF_cont hF_deriv
      hF_deriv_int hF0 hF1 hF_deriv_bound
  have hcut₂ := intervalConjugateDuhamel_secondDeriv_continuousOn_Icc_of_late_deriv_holder
    ht heta0 heta1 hCQ_nn hHQd_nn hF_meas hF_int hF_bound hF_cont
      hF_deriv hF_deriv_int hF0 hF1 hF_deriv_bound hF_deriv_holder
  have heq₁ : ∀ x,
      (∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) x) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s) (F s) z) x := by
    intro x
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have heq₂ : ∀ x,
      (∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x) =
      ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s) (F s) z) y) x := by
    intro x
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  exact ⟨hcut₁.congr (fun x _hx ↦ heq₁ x),
    hcut₂.congr (fun x _hx ↦ heq₂ x)⟩

/-- Closed-interval continuity of the first derivative profile of the actual
chemotaxis Duhamel leg. -/
theorem conjugateMildM_chemDuhamel_firstDeriv_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) x)
      (Set.Icc (0 : ℝ) 1) :=
  (conjugateMildM_chemDuhamel_spatialDerivs_continuousOn_Icc
    D hu₀ hu₀_meas ht htT).1

/-- Closed-interval continuity of the second derivative profile of the actual
chemotaxis Duhamel leg. -/
theorem conjugateMildM_chemDuhamel_secondDeriv_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x)
      (Set.Icc (0 : ℝ) 1) :=
  (conjugateMildM_chemDuhamel_spatialDerivs_continuousOn_Icc
    D hu₀ hu₀_meas ht htT).2

/-- Open-interval corollary of the endpoint-closed chemotaxis Hessian theorem. -/
theorem conjugateMildM_chemDuhamel_secondDeriv_continuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContinuousOn
      (fun x ↦ ∫ s in (0 : ℝ)..t, deriv (fun y ↦ deriv
        (fun z ↦ intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x)
      (Set.Ioo (0 : ℝ) 1) :=
  (conjugateMildM_chemDuhamel_secondDeriv_continuousOn_Icc
    D hu₀ hu₀_meas ht htT).mono Set.Ioo_subset_Icc_self

section AxiomAudit

#print axioms conjugateMildM_chemDuhamel_secondDeriv_intervalIntegrable_interior
#print axioms conjugateMildM_chemDuhamel_secondDeriv_intervalIntegrable_Icc
#print axioms conjugateMildM_chemDuhamel_deriv_hasDerivAt_interior

end AxiomAudit

end ShenWork.Paper2
