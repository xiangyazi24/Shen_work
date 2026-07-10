/-
  Positive-time W^{1,infinity} control of the actual chemotaxis flux along the
  faithful conjugate mild solution, followed by the conjugate-kernel IBP
  identity.  The resolver derivative is obtained from the weak elliptic FTC
  bridge, so no source-coefficient decay or classical regularity is assumed.
-/
import ShenWork.Paper2.IntervalConjugateMildSpatialC1
import ShenWork.Paper2.IntervalConjugateKernelIBP
import ShenWork.Paper2.IntervalResolverWeakODEBridge

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)

/-- The actual positive-time chemotaxis flux is differentiable at every
interior point. -/
theorem conjugateMild_chemFlux_differentiableAt_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (chemFluxLifted p (D.u t)) x := by
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  let G : ℝ → ℝ := resolverGradReal p (D.u t)
  let R : ℝ → ℝ :=
    intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u t))
  let W : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) U = D.u t := by
      ext ⟨z, hz⟩
      simp [Set.restrict, U, intervalDomainLift, hz]
      rfl
    rw [heq]
    exact D.hcont t ht htT
  have hU := conjugateMild_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num) ht htT hx
  have hU' : HasDerivAt U (deriv U x) x := by
    simpa [U] using hU.differentiableAt.hasDerivAt
  have hGraw :=
    ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
        p hUcont (fun z hz => by
          simpa [U, intervalDomainLift, hz] using
            D.hnonneg t ht htT ⟨z, hz⟩) hx
  have hG' : HasDerivAt G (deriv G x) x := by
    simpa [G] using hGraw.differentiableAt.hasDerivAt
  have hR' : HasDerivAt R (G x) x := by
    simpa [R, G] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
          p hUcont hx
  have hR_nonneg : 0 ≤ R x := by
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u) D.hnonneg D.hcont ht htT ⟨x,
        Set.Ioo_subset_Icc_self hx⟩
    simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, Set.Ioo_subset_Icc_self hx] using h
  have hW' : HasDerivAt W
      (G x * (-p.β) * (1 + R x) ^ (-p.β - 1)) x := by
    have hbase : HasDerivAt (fun z : ℝ => 1 + R z) (G x) x :=
      hR'.const_add 1
    simpa [W, sub_eq_add_neg] using
      hbase.rpow_const (p := -p.β) (Or.inl (by linarith : 1 + R x ≠ 0))
  have hprod : DifferentiableAt ℝ (fun z => U z * G z * W z) x :=
    (hU'.mul hG').mul hW' |>.differentiableAt
  have hev : chemFluxLifted p (D.u t) =ᶠ[𝓝 x]
      (fun z => U z * G z * W z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hRz_nonneg : 0 ≤ R z := by
      have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (T := D.T) p (u := D.u) D.hnonneg D.hcont ht htT ⟨z, hzIcc⟩
      simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
        intervalDomainLift, hzIcc] using h
    unfold chemFluxLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ 1 + R z)]
  exact hprod.congr_of_eventuallyEq hev

/-- On a fixed positive-time slice, the derivative of the actual chemotaxis
flux is uniformly bounded on the open interval. -/
theorem conjugateMild_chemFlux_deriv_uniformBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (chemFluxLifted p (D.u t)) x| ≤ C := by
  obtain ⟨CU, hCU, hUbound⟩ :=
    conjugateMild_intervalDomainLift_deriv_uniformBound D hu₀ hu₀_meas ht htT
  set G0 : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hG0
  set L0 : ℝ := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p D.M
    with hL0
  set C : ℝ := CU * G0 + D.M * L0 + D.M * G0 * p.β * G0 with hC
  have hG0_nn : 0 ≤ G0 := by
    rw [hG0]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hL0_nn : 0 ≤ L0 := by
    rw [hL0, ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound,
      ShenWork.IntervalResolverWeakBounds.resolverWeakValueBound]
    exact add_nonneg
      (mul_nonneg p.hμ.le
        (mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num)
            (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))))
      (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))
  have hC_nn : 0 ≤ C := by
    rw [hC]
    exact add_nonneg
      (add_nonneg (mul_nonneg hCU hG0_nn) (mul_nonneg D.hM.le hL0_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg D.hM.le hG0_nn) p.hβ) hG0_nn)
  refine ⟨C, hC_nn, ?_⟩
  intro x hx
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  let G : ℝ → ℝ := resolverGradReal p (D.u t)
  let R : ℝ → ℝ :=
    intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u t))
  let W : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
  have hxIcc := Set.Ioo_subset_Icc_self hx
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) U = D.u t := by
      ext ⟨z, hz⟩
      simp [Set.restrict, U, intervalDomainLift, hz]
      rfl
    rw [heq]
    exact D.hcont t ht htT
  have hUraw := conjugateMild_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num) ht htT hx
  have hU' : HasDerivAt U (deriv U x) x := by
    simpa [U] using hUraw.differentiableAt.hasDerivAt
  have hGraw :=
    ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
        p hUcont (fun z hz => by
          simpa [U, intervalDomainLift, hz] using
            D.hnonneg t ht htT ⟨z, hz⟩) hx
  have hG' : HasDerivAt G (deriv G x) x := by
    simpa [G] using hGraw.differentiableAt.hasDerivAt
  have hR' : HasDerivAt R (G x) x := by
    simpa [R, G] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
          p hUcont hx
  have hR_nonneg : 0 ≤ R x := by
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u) D.hnonneg D.hcont ht htT ⟨x, hxIcc⟩
    simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hxIcc] using h
  have hW' : HasDerivAt W
      (G x * (-p.β) * (1 + R x) ^ (-p.β - 1)) x := by
    have hbase : HasDerivAt (fun z : ℝ => 1 + R z) (G x) x :=
      hR'.const_add 1
    simpa [W, sub_eq_add_neg] using
      hbase.rpow_const (p := -p.β) (Or.inl (by linarith : 1 + R x ≠ 0))
  have hprod := (hU'.mul hG').mul hW'
  have hev : chemFluxLifted p (D.u t) =ᶠ[𝓝 x]
      (fun z => U z * G z * W z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hRz_nonneg : 0 ≤ R z := by
      have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (T := D.T) p (u := D.u) D.hnonneg D.hcont ht htT ⟨z, hzIcc⟩
      simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
        intervalDomainLift, hzIcc] using h
    unfold chemFluxLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ 1 + R z)]
  have hflux := hev.hasDerivAt_iff.mpr hprod
  have hU_abs : |U x| ≤ D.M := by
    simpa [U, intervalDomainLift, hxIcc] using D.hbound t ht htT ⟨x, hxIcc⟩
  have hU_deriv : |deriv U x| ≤ CU := by
    simpa [U] using hUbound x hx
  have hG_abs : |G x| ≤ G0 := by
    rw [hG0]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont
        (fun z hz => by
          have h := D.hnonneg t ht htT ⟨z, hz⟩
          simpa [U, intervalDomainLift, hz] using h)
        (fun z hz => by
          have h := D.hbound t ht htT ⟨z, hz⟩
          simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2)
        hxIcc
  have hG_deriv : |deriv G x| ≤ L0 := by
    rw [hL0]
    simpa [G] using
      ShenWork.IntervalResolverWeakBounds.deriv_resolverGradReal_abs_le_of_bounded
        p hUcont
          (fun z hz => by
            have h := D.hnonneg t ht htT ⟨z, hz⟩
            simpa [U, intervalDomainLift, hz] using h)
          (fun z hz => by
            have h := D.hbound t ht htT ⟨z, hz⟩
            simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2)
          hx
  have hW_abs : |W x| ≤ 1 := by
    have hW_nn : 0 ≤ W x := Real.rpow_nonneg (by linarith : 0 ≤ 1 + R x) _
    rw [abs_of_nonneg hW_nn]
    dsimp [W]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
  have hW_deriv_abs :
      |G x * (-p.β) * (1 + R x) ^ (-p.β - 1)| ≤ p.β * G0 := by
    have hpow_nn : 0 ≤ (1 + R x) ^ (-p.β - 1) :=
      Real.rpow_nonneg (by linarith : 0 ≤ 1 + R x) _
    have hpow_le : (1 + R x) ^ (-p.β - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg p.hβ, abs_of_nonneg hpow_nn]
    have hGpβ : |G x| * p.β ≤ G0 * p.β :=
      mul_le_mul_of_nonneg_right hG_abs p.hβ
    calc
      |G x| * p.β * (1 + R x) ^ (-p.β - 1)
          ≤ G0 * p.β * (1 + R x) ^ (-p.β - 1) :=
        mul_le_mul_of_nonneg_right hGpβ hpow_nn
      _ ≤ G0 * p.β * 1 :=
        mul_le_mul_of_nonneg_left hpow_le (mul_nonneg hG0_nn p.hβ)
      _ = p.β * G0 := by ring
  rw [hflux.deriv, hC]
  calc
    |(deriv U x * G x + U x * deriv G x) * W x +
        U x * G x * (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))|
      ≤ |(deriv U x * G x + U x * deriv G x) * W x| +
          |U x * G x * (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| :=
        abs_add_le _ _
    _ ≤ (CU * G0 + D.M * L0) * 1 + D.M * G0 * (p.β * G0) := by
      have hsum : |deriv U x * G x + U x * deriv G x| ≤
          CU * G0 + D.M * L0 := by
        calc
          |deriv U x * G x + U x * deriv G x|
              ≤ |deriv U x * G x| + |U x * deriv G x| := abs_add_le _ _
          _ ≤ CU * G0 + D.M * L0 := by
            rw [abs_mul, abs_mul]
            exact add_le_add
              (mul_le_mul hU_deriv hG_abs (abs_nonneg _) hCU)
              (mul_le_mul hU_abs hG_deriv (abs_nonneg _) D.hM.le)
      have hsum_nn : 0 ≤ CU * G0 + D.M * L0 :=
        add_nonneg (mul_nonneg hCU hG0_nn) (mul_nonneg D.hM.le hL0_nn)
      have hUG_nn : 0 ≤ D.M * G0 := mul_nonneg D.hM.le hG0_nn
      have hfirst :
          |(deriv U x * G x + U x * deriv G x) * W x| ≤
            (CU * G0 + D.M * L0) * 1 := by
        rw [abs_mul]
        exact mul_le_mul hsum hW_abs (abs_nonneg _) hsum_nn
      have hUG : |U x| * |G x| ≤ D.M * G0 :=
        mul_le_mul hU_abs hG_abs (abs_nonneg _) D.hM.le
      have hsecond :
          |U x * G x *
              (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| ≤
            D.M * G0 * (p.β * G0) := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul hUG hW_deriv_abs (abs_nonneg _) hUG_nn
      exact add_le_add hfirst hsecond
    _ = CU * G0 + D.M * L0 + D.M * G0 * p.β * G0 := by ring

/-- The interior derivative of the positive-time chemotaxis flux is interval
integrable; endpoint values of `deriv` are irrelevant to the interval measure. -/
theorem conjugateMild_chemFlux_deriv_intervalIntegrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    IntervalIntegrable (deriv (chemFluxLifted p (D.u t))) volume 0 1 := by
  obtain ⟨C, _hC, hbound⟩ :=
    conjugateMild_chemFlux_deriv_uniformBound D hu₀ hu₀_meas ht htT
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine Integrable.mono' (integrable_const C)
    ((measurable_deriv _).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  filter_upwards [hne] with x hx1 hx
  rw [Real.norm_eq_abs]
  exact hbound x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

/-- On every positive slice, the faithful conjugate operator is the Neumann
semigroup applied to the actual weak spatial derivative of the chemotaxis
flux. -/
theorem conjugateMild_intervalConjugateKernelOperator_eq_semigroup_fluxDeriv
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {s r x : ℝ} (hs : 0 < s) (hsT : s ≤ D.T) (hr : 0 < r) :
    intervalConjugateKernelOperator r (chemFluxLifted p (D.u s)) x =
      intervalFullSemigroupOperator r (deriv (chemFluxLifted p (D.u s))) x := by
  have hQcont : Continuous (chemFluxLifted p (D.u s)) :=
    ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuous_of_continuous
      p (D.hcont s hs hsT) (D.hnonneg s hs hsT)
  exact
    ShenWork.Paper2.IntervalConjugateKernelIBP.intervalConjugateKernelOperator_eq_semigroup_deriv
        hr hQcont.continuousOn
        (fun y hy =>
          (conjugateMild_chemFlux_differentiableAt_interior
            D hu₀ hu₀_meas hs hsT hy).hasDerivAt)
        (conjugateMild_chemFlux_deriv_intervalIntegrable
          D hu₀ hu₀_meas hs hsT)
        (ShenWork.IntervalCoupledRegularityBootstrap.chemFluxLifted_endpoint_zero
          p (D.u s))
        (ShenWork.IntervalCoupledRegularityBootstrap.chemFluxLifted_endpoint_one
          p (D.u s))

end ShenWork.Paper2
