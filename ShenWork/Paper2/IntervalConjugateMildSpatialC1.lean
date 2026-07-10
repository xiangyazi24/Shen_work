/-
  Positive-time interior spatial differentiability of the faithful
  conjugate-kernel mild solution.

  The chemotaxis leg uses the late-time Holder cancellation proved in
  `IntervalConjugateDuhamelSpatialC1`.  The initial and reaction legs use the
  ordinary Neumann heat-kernel spatial Leibniz rules.  Time cutoffs extend the
  order-box source bounds to all real times without changing any integral over
  `(0,t]`.
-/
import ShenWork.Paper2.IntervalConjugateDuhamelSpatialC1
import ShenWork.Paper2.IntervalConjugateMildCthetaFlux
import ShenWork.Paper2.IntervalDuhamelSpatialLeibniz
import ShenWork.PDE.IntervalCoupledDuhamelT6SliceAgreement

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateDuhamelMap)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)

/-! ## The faithful chemotaxis leg -/

/-- The actual chemotaxis Duhamel leg of a faithful conjugate mild solution is
spatially differentiable at every positive time and every interior point. -/
theorem conjugateMild_chemDuhamel_hasDerivAt_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ t x : ℝ} (hθ0 : 0 < θ) (hθhalf : θ < (1 / 2 : ℝ))
    (ht : 0 < t) (htT : t ≤ D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun z : ℝ => ∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (D.u s)) z)
      (∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ =>
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (D.u s)) z) x)
      x := by
  set CQ : ℝ := D.M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg D.hM.le
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg p.hν.le
          (Real.rpow_nonneg D.hM.le _))))
  set F : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxLifted p (D.u s) y else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxLifted p (D.u s) := by
    intro s hs0 hsT
    funext y
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s y, |F s y| ≤ CQ := by
    intro s y
    simp only [hF]
    split_ifs with hs
    · rw [hCQ]
      exact ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
        p D.hM.le (D.hbound s hs.1 hs.2) (D.hnonneg s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) y
    · simpa using hCQ_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase :=
      ShenWork.Paper2.chemFluxLifted_uncurry_measurable
        (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (D.hbound s hs.1 hs.2) D.hM.le (D.hcont s hs.1 hs.2)
          (D.hnonneg s hs.1 hs.2)
    · simp
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨HQ, hHQ_nn, hQholder⟩ :=
    conjugateMild_chemFlux_positiveTime_holder D hu₀ hu₀_meas
      hθ0 hθhalf ht2
  have hF_cont : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs2 hst
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuous_of_continuous
      p (D.hcont s hs0 hsT) (D.hnonneg s hs0 hsT)).continuousOn
  have hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |F s a - F s b| ≤ HQ * |a - b| ^ θ := by
    intro s hs2 hst a b ha hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQholder s ⟨le_of_lt hs2, hsT⟩ a b ha hb
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact ShenWork.IntervalCoupledRegularityBootstrap.chemFluxLifted_endpoint_zero
        p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact ShenWork.IntervalCoupledRegularityBootstrap.chemFluxLifted_endpoint_one
        p (D.u s)
    · rfl
  have hcut :=
    ShenWork.IntervalNeumannFullKernel.intervalConjugateDuhamel_hasDerivAt_fst_of_late_holder
      ht hθ0 (by linarith : θ < 1) hCQ_nn hHQ_nn hF_meas hF_int hF_bound
        hF_cont hF_holder hF0 hF1 hx
  have hfun_eq : ∀ z : ℝ,
      (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (D.u s)) z) =
      ∫ s in (0 : ℝ)..t, intervalConjugateKernelOperator (t - s) (F s) z := by
    intro z
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hder_eq :
      (∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ =>
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (D.u s)) z) x) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hev :
      (fun z : ℝ => ∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (D.u s)) z)
        =ᶠ[𝓝 x]
      (fun z : ℝ => ∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (F s) z) :=
    Filter.Eventually.of_forall hfun_eq
  exact (hev.hasDerivAt_iff.mpr hcut).congr_deriv hder_eq.symm

/-! ## The reaction leg -/

/-- The reaction Duhamel leg of the faithful mild solution is spatially
differentiable at every positive time. -/
theorem conjugateMild_logisticDuhamel_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    HasDerivAt
      (fun z : ℝ => ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) z)
      (∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) z) x)
      x := by
  set CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))
  set F : ℝ → ℝ → ℝ := fun s y =>
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
    have hbase :=
      logisticLifted_uncurry_measurable (p := p) (u := D.u) D.hmeas
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
  have hcut :=
    ShenWork.IntervalDuhamelSpatialLeibniz.intervalFullDuhamel_hasDerivAt_fst
      ht hF_meas hF_int hCL_nn hF_bound x
  have hfun_eq : ∀ z : ℝ,
      (∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) z) =
      ∫ s in (0 : ℝ)..t, intervalFullSemigroupOperator (t - s) (F s) z := by
    intro z
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hder_eq :
      (∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) z) x) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hev :
      (fun z : ℝ => ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) z)
        =ᶠ[𝓝 x]
      (fun z : ℝ => ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (F s) z) :=
    Filter.Eventually.of_forall hfun_eq
  exact (hev.hasDerivAt_iff.mpr hcut).congr_deriv hder_eq.symm

/-! ## The whole mild slice -/

/-- At every positive time, the faithful conjugate mild solution is spatially
differentiable at every interior point, with the derivative obtained by
differentiating each of the three actual mild-equation legs. -/
theorem conjugateMild_intervalDomainLift_hasDerivAt_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ t x : ℝ} (hθ0 : 0 < θ) (hθhalf : θ < (1 / 2 : ℝ))
    (ht : 0 < t) (htT : t ≤ D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (intervalDomainLift (D.u t))
      ((∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
          intervalDomainLift u₀ y ∂(intervalMeasure 1))
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x)
        + ∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) x)
      x := by
  have hinit :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hu₀_meas hu₀ x
  have hchem := conjugateMild_chemDuhamel_hasDerivAt_interior
    D hu₀ hu₀_meas hθ0 hθhalf ht htT hx
  have hreact := conjugateMild_logisticDuhamel_hasDerivAt D ht htT (x := x)
  let rhs : ℝ → ℝ := fun z =>
    intervalFullSemigroupOperator t (intervalDomainLift u₀) z
      + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (D.u s)) z)
      + ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) z
  have hrhs : HasDerivAt rhs
      ((∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
          intervalDomainLift u₀ y ∂(intervalMeasure 1))
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x)
        + ∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) x) x := by
    dsimp [rhs]
    exact (hinit.add (hchem.const_mul (-p.χ₀))).add hreact
  have hev : intervalDomainLift (D.u t) =ᶠ[𝓝 x] rhs := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    have hm := D.hmild t ht htT ⟨z, hzIcc⟩
    simpa [rhs, intervalDomainLift, hzIcc, intervalConjugateDuhamelMap] using hm
  exact hev.hasDerivAt_iff.mpr hrhs

end ShenWork.Paper2
