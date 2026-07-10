/-
  Positive-time Holder regularity of the derivative of the faithful
  chemotaxis flux.  The resolver-gradient derivative is handled through the
  physical elliptic ODE, including the fractional-power case at `u = 0`.
-/
import ShenWork.Paper2.IntervalConjugateMildPositiveTimeC1
import ShenWork.Paper2.IntervalPositiveRpowHolder

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)

/-- The weak resolver ODE identifies the actual derivative of the resolver
gradient without any source-coefficient decay assumption. -/
theorem conjugateMild_resolverGrad_deriv_eq_physical
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z : ℝ => resolverGradReal p (D.u t) z) x =
      p.μ * intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p (D.u t)) x -
        p.ν * (intervalDomainLift (D.u t) x) ^ p.γ := by
  have hxIcc := Set.Ioo_subset_Icc_self hx
  have hUcont : ContinuousOn (intervalDomainLift (D.u t))
      (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
        (intervalDomainLift (D.u t)) = D.u t := by
      ext ⟨z, hz⟩
      simp [Set.restrict, intervalDomainLift, hz]
      rfl
    rw [heq]
    exact D.hcont t ht htT
  have hnonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (D.u t) z := by
    intro z hz
    simpa [intervalDomainLift, hz] using D.hnonneg t ht htT ⟨z, hz⟩
  have hraw :=
    ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
      p hUcont hnonneg hx
  have hUx : 0 ≤ D.u t ⟨x, hxIcc⟩ := D.hnonneg t ht htT ⟨x, hxIcc⟩
  rw [hraw.deriv]
  simp [ShenWork.IntervalResolverWeakBounds.resolverLapPhysical,
    ShenWork.IntervalResolverWeakBounds.resolverPositiveSourceLifted,
    intervalDomainLift, hxIcc, positivePart_eq_self_of_nonneg hUx]

/-- Product/chain-rule formula for the actual faithful chemotaxis flux
derivative at an interior positive-time point. -/
theorem conjugateMild_chemFlux_deriv_eq_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    let U : ℝ → ℝ := intervalDomainLift (D.u t)
    let G : ℝ → ℝ := resolverGradReal p (D.u t)
    let R : ℝ → ℝ :=
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u t))
    let W : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
    deriv (chemFluxLifted p (D.u t)) x =
      (deriv U x * G x + U x * deriv G x) * W x +
        U x * G x *
          (G x * (-p.β) * (1 + R x) ^ (-p.β - 1)) := by
  dsimp only
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
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      ht htT hx
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
  have hev : chemFluxLifted p (D.u t) =ᶠ[nhds x]
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
  simpa [U, G, R, W] using (hev.hasDerivAt_iff.mpr hprod).deriv

/-- On every positive-time strip, the derivative of the actual chemotaxis
flux has one spatial power-Holder modulus.  The exponent is chosen below both
`1` and the source power `gamma`, so this remains valid when `0 < gamma < 1`
and the solution vanishes. -/
theorem conjugateMild_chemFlux_deriv_positiveTime_holder_uniform
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ eta H : ℝ, 0 < eta ∧ eta < 1 ∧ 0 ≤ H ∧
      ∀ t, τ ≤ t → t ≤ D.T →
        ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
          |deriv (chemFluxLifted p (D.u t)) x -
            deriv (chemFluxLifted p (D.u t)) y| ≤ H * |x - y| ^ eta := by
  set eta : ℝ := min (1 / 4 : ℝ) (p.γ / 2) with heta
  have heta0 : 0 < eta := by
    rw [heta, lt_min_iff]
    exact ⟨by norm_num, by linarith [p.hγ]⟩
  have heta_quarter : eta ≤ (1 / 4 : ℝ) := by
    rw [heta]
    exact min_le_left _ _
  have heta1 : eta < 1 := lt_of_le_of_lt heta_quarter (by norm_num)
  have heta1le : eta ≤ 1 := heta1.le
  have hetagamma : eta ≤ p.γ := by
    calc eta ≤ p.γ / 2 := by rw [heta]; exact min_le_right _ _
      _ ≤ p.γ := by linarith [p.hγ]
  obtain ⟨CU, hCU_nn, hUderiv_bound⟩ :=
    conjugateMild_intervalDomainLift_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas hτ
  obtain ⟨HU, hHU_nn, hUderiv_holder⟩ :=
    conjugateMild_intervalDomainLift_deriv_positiveTime_holder_uniform
      D hu₀ hu₀_meas hτ heta0 heta1
  set G0 : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hG0
  set L0 : ℝ := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p D.M
    with hL0
  set HPow : ℝ :=
    CU ^ p.γ + p.γ * D.M ^ (p.γ - 1) * CU with hHPow
  set HGd : ℝ := p.μ * G0 + p.ν * HPow with hHGd
  set HW : ℝ := p.β * G0 with hHW
  set HV : ℝ := (p.β + 1) * G0 with hHV
  set HWd : ℝ := p.β * (L0 + G0 * HV) with hHWd
  set BA : ℝ := CU * G0 + D.M * L0 with hBA
  set HA : ℝ :=
    (HU * G0 + CU * L0) + (CU * L0 + D.M * HGd) with hHA
  set H : ℝ :=
    (HA + BA * HW) + (BA * HW + (D.M * G0) * HWd) with hH
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
  have hHPow_nn : 0 ≤ HPow := by
    rw [hHPow]
    exact add_nonneg (Real.rpow_nonneg hCU_nn _)
      (mul_nonneg
        (mul_nonneg p.hγ.le (Real.rpow_nonneg D.hM.le _)) hCU_nn)
  have hHGd_nn : 0 ≤ HGd := by
    rw [hHGd]
    exact add_nonneg (mul_nonneg p.hμ.le hG0_nn)
      (mul_nonneg p.hν.le hHPow_nn)
  have hHW_nn : 0 ≤ HW := by rw [hHW]; exact mul_nonneg p.hβ hG0_nn
  have hHV_nn : 0 ≤ HV := by
    rw [hHV]
    exact mul_nonneg (by linarith [p.hβ]) hG0_nn
  have hHWd_nn : 0 ≤ HWd := by
    rw [hHWd]
    exact mul_nonneg p.hβ
      (add_nonneg hL0_nn (mul_nonneg hG0_nn hHV_nn))
  have hBA_nn : 0 ≤ BA := by
    rw [hBA]
    exact add_nonneg (mul_nonneg hCU_nn hG0_nn)
      (mul_nonneg D.hM.le hL0_nn)
  have hHA_nn : 0 ≤ HA := by
    rw [hHA]
    exact add_nonneg
      (add_nonneg (mul_nonneg hHU_nn hG0_nn) (mul_nonneg hCU_nn hL0_nn))
      (add_nonneg (mul_nonneg hCU_nn hL0_nn) (mul_nonneg D.hM.le hHGd_nn))
  have hH_nn : 0 ≤ H := by
    rw [hH]
    exact add_nonneg
      (add_nonneg hHA_nn (mul_nonneg hBA_nn hHW_nn))
      (add_nonneg (mul_nonneg hBA_nn hHW_nn)
        (mul_nonneg (mul_nonneg D.hM.le hG0_nn) hHWd_nn))
  refine ⟨eta, H, heta0, heta1, hH_nn, ?_⟩
  intro t hτt htT x hx y hy
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  let G : ℝ → ℝ := resolverGradReal p (D.u t)
  let R : ℝ → ℝ :=
    intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u t))
  let W : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
  let V : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β - 1)
  let Wd : ℝ → ℝ := fun z => G z * (-p.β) * V z
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) U = D.u t := by
      ext ⟨z, hz⟩
      simp [Set.restrict, U, intervalDomainLift, hz]
      rfl
    rw [heq]
    exact D.hcont t ht htT
  have hUnonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ U z := by
    intro z hz
    simpa [U, intervalDomainLift, hz] using D.hnonneg t ht htT ⟨z, hz⟩
  have hUupper : ∀ z ∈ Set.Icc (0 : ℝ) 1, U z ≤ D.M := by
    intro z hz
    have h := D.hbound t ht htT ⟨z, hz⟩
    simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2
  have hUdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ U z := by
    intro z hz
    simpa [U] using
      (conjugateMild_intervalDomainLift_hasDerivAt_interior
        D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
          ht htT hz).differentiableAt
  have hUd_bound : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |deriv U z| ≤ CU := by
    intro z hz
    simpa [U] using hUderiv_bound t hτt htT z hz
  have hGdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ G z := by
    intro z hz
    simpa [G] using
      (ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
        p hUcont hUnonneg hz).differentiableAt
  have hGd_bound : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |deriv G z| ≤ L0 := by
    intro z hz
    rw [hL0]
    simpa [G] using
      ShenWork.IntervalResolverWeakBounds.deriv_resolverGradReal_abs_le_of_bounded
        p hUcont hUnonneg hUupper hz
  have hRdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt R (G z) z := by
    intro z hz
    simpa [R, G] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
        p hUcont hz
  have hU_abs : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |U z| ≤ D.M := by
    intro z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    simpa [U, intervalDomainLift, hzIcc] using D.hbound t ht htT ⟨z, hzIcc⟩
  have hG_abs : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |G z| ≤ G0 := by
    intro z hz
    rw [hG0]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont hUnonneg hUupper (Set.Ioo_subset_Icc_self hz)
  have hR_nonneg : ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ R z := by
    intro z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u) D.hnonneg D.hcont ht htT ⟨z, hzIcc⟩
    simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hzIcc] using h
  have hW_abs : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |W z| ≤ 1 := by
    intro z hz
    have hbase : 1 ≤ 1 + R z := by linarith [hR_nonneg z hz]
    have hnn : 0 ≤ W z := Real.rpow_nonneg (by linarith) _
    rw [abs_of_nonneg hnn]
    exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith [p.hβ])
  have hV_abs : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |V z| ≤ 1 := by
    intro z hz
    have hbase : 1 ≤ 1 + R z := by linarith [hR_nonneg z hz]
    have hnn : 0 ≤ V z := Real.rpow_nonneg (by linarith) _
    rw [abs_of_nonneg hnn]
    exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith [p.hβ])
  have hW_has : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt W (G z * (-p.β) * V z) z := by
    intro z hz
    have hbase : HasDerivAt (fun q : ℝ => 1 + R q) (G z) z :=
      (hRdiff z hz).const_add 1
    simpa [W, V, sub_eq_add_neg] using
      hbase.rpow_const (p := -p.β)
        (Or.inl (by linarith [hR_nonneg z hz] : 1 + R z ≠ 0))
  have hW_deriv_bound : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |deriv W z| ≤ HW := by
    intro z hz
    rw [(hW_has z hz).deriv, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg p.hβ]
    calc
      |G z| * p.β * |V z| ≤ G0 * p.β * 1 := by
        have hgp : |G z| * p.β ≤ G0 * p.β :=
          mul_le_mul_of_nonneg_right (hG_abs z hz) p.hβ
        exact mul_le_mul
          hgp
          (hV_abs z hz) (abs_nonneg _)
          (mul_nonneg hG0_nn p.hβ)
      _ = HW := by rw [hHW]; ring
  have hV_has : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt V
        (G z * (-p.β - 1) * (1 + R z) ^ (-p.β - 1 - 1)) z := by
    intro z hz
    have hbase : HasDerivAt (fun q : ℝ => 1 + R q) (G z) z :=
      (hRdiff z hz).const_add 1
    have hraw := hbase.rpow_const (p := -p.β - 1)
      (Or.inl (by linarith [hR_nonneg z hz] : 1 + R z ≠ 0))
    simpa [V] using hraw
  have hV_deriv_bound : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |deriv V z| ≤ HV := by
    intro z hz
    rw [(hV_has z hz).deriv]
    rw [show -p.β - 1 - 1 = -p.β - 2 by ring]
    rw [abs_mul, abs_mul,
      abs_of_nonpos (by linarith [p.hβ] : -p.β - 1 ≤ 0)]
    have hpow_nn : 0 ≤ (1 + R z) ^ (-p.β - 2) :=
      Real.rpow_nonneg (by linarith [hR_nonneg z hz]) _
    rw [abs_of_nonneg hpow_nn]
    have hpow_le : (1 + R z) ^ (-p.β - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [hR_nonneg z hz]) (by linarith [p.hβ])
    calc
      |G z| * -(-p.β - 1) * (1 + R z) ^ (-p.β - 2)
          ≤ G0 * (p.β + 1) * 1 := by
        have hc : -(-p.β - 1) = p.β + 1 := by ring
        rw [hc]
        have hgp : |G z| * (p.β + 1) ≤ G0 * (p.β + 1) :=
          mul_le_mul_of_nonneg_right (hG_abs z hz) (by linarith [p.hβ])
        exact mul_le_mul
          hgp
          hpow_le hpow_nn (mul_nonneg hG0_nn (by linarith [p.hβ]))
      _ = HV := by rw [hHV]; ring
  have hU_lip : |U x - U y| ≤ CU * |x - y| :=
    abs_sub_le_mul_abs_sub_of_deriv_bound_Ioo hUdiff
      (fun z hz => by rw [Real.norm_eq_abs]; exact hUd_bound z hz) hx hy
  have hpowdist := unitInterval_abs_sub_le_rpow heta0 heta1le
    (Set.Ioo_subset_Icc_self hx) (Set.Ioo_subset_Icc_self hy)
  have hU_holder : |U x - U y| ≤ CU * |x - y| ^ eta :=
    hU_lip.trans (mul_le_mul_of_nonneg_left hpowdist hCU_nn)
  have hUd_holder : |deriv U x - deriv U y| ≤ HU * |x - y| ^ eta := by
    simpa [U] using hUderiv_holder t hτt htT x hx y hy
  have hG_lip : |G x - G y| ≤ L0 * |x - y| :=
    abs_sub_le_mul_abs_sub_of_deriv_bound_Ioo hGdiff
      (fun z hz => by rw [Real.norm_eq_abs]; exact hGd_bound z hz) hx hy
  have hG_holder : |G x - G y| ≤ L0 * |x - y| ^ eta :=
    hG_lip.trans (mul_le_mul_of_nonneg_left hpowdist hL0_nn)
  have hR_lip : |R x - R y| ≤ G0 * |x - y| :=
    abs_sub_le_mul_abs_sub_of_deriv_bound_Ioo
      (fun z hz => (hRdiff z hz).differentiableAt)
      (fun z hz => by
        rw [(hRdiff z hz).deriv, Real.norm_eq_abs]
        exact hG_abs z hz) hx hy
  have hR_holder : |R x - R y| ≤ G0 * |x - y| ^ eta :=
    hR_lip.trans (mul_le_mul_of_nonneg_left hpowdist hG0_nn)
  have hUpow_holder : |(U x) ^ p.γ - (U y) ^ p.γ| ≤
      HPow * |x - y| ^ eta := by
    rw [hHPow]
    exact rpow_holder_of_nonneg_bounded_lipschitz
      p.hγ heta0 heta1le hetagamma D.hM.le hCU_nn
      ⟨hUnonneg x (Set.Ioo_subset_Icc_self hx),
        hUupper x (Set.Ioo_subset_Icc_self hx)⟩
      ⟨hUnonneg y (Set.Ioo_subset_Icc_self hy),
        hUupper y (Set.Ioo_subset_Icc_self hy)⟩
      hU_lip (Set.Ioo_subset_Icc_self hx) (Set.Ioo_subset_Icc_self hy)
  have hGd_eq : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      deriv G z = p.μ * R z - p.ν * (U z) ^ p.γ := by
    intro z hz
    simpa [G, R, U] using
      conjugateMild_resolverGrad_deriv_eq_physical D ht htT hz
  have hGd_holder : |deriv G x - deriv G y| ≤ HGd * |x - y| ^ eta := by
    rw [hGd_eq x hx, hGd_eq y hy, hHGd]
    calc
      |(p.μ * R x - p.ν * U x ^ p.γ) -
          (p.μ * R y - p.ν * U y ^ p.γ)|
          = |p.μ * (R x - R y) -
              p.ν * (U x ^ p.γ - U y ^ p.γ)| := by ring_nf
      _ ≤ |p.μ * (R x - R y)| +
            |p.ν * (U x ^ p.γ - U y ^ p.γ)| := abs_sub _ _
      _ ≤ (p.μ * G0) * |x - y| ^ eta +
            (p.ν * HPow) * |x - y| ^ eta := by
        rw [abs_mul, abs_mul, abs_of_pos p.hμ, abs_of_pos p.hν]
        exact add_le_add
          (by simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hR_holder p.hμ.le)
          (by simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hUpow_holder p.hν.le)
      _ = (p.μ * G0 + p.ν * HPow) * |x - y| ^ eta := by ring
  have hW_holder : |W x - W y| ≤ HW * |x - y| ^ eta := by
    have hlip := abs_sub_le_mul_abs_sub_of_deriv_bound_Ioo
      (fun z hz => (hW_has z hz).differentiableAt)
      (fun z hz => by rw [Real.norm_eq_abs]; exact hW_deriv_bound z hz) hx hy
    exact hlip.trans (mul_le_mul_of_nonneg_left hpowdist hHW_nn)
  have hV_holder : |V x - V y| ≤ HV * |x - y| ^ eta := by
    have hlip := abs_sub_le_mul_abs_sub_of_deriv_bound_Ioo
      (fun z hz => (hV_has z hz).differentiableAt)
      (fun z hz => by rw [Real.norm_eq_abs]; exact hV_deriv_bound z hz) hx hy
    exact hlip.trans (mul_le_mul_of_nonneg_left hpowdist hHV_nn)
  have hWd_abs : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |Wd z| ≤ HW := by
    intro z hz
    dsimp [Wd]
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg p.hβ]
    calc
      |G z| * p.β * |V z| ≤ G0 * p.β * 1 := by
        have hgp : |G z| * p.β ≤ G0 * p.β :=
          mul_le_mul_of_nonneg_right (hG_abs z hz) p.hβ
        exact mul_le_mul
          hgp
          (hV_abs z hz) (abs_nonneg _)
          (mul_nonneg hG0_nn p.hβ)
      _ = HW := by rw [hHW]; ring
  have hGV_holder : |G x * V x - G y * V y| ≤
      (L0 + G0 * HV) * |x - y| ^ eta := by
    have hraw := abs_mul_sub_mul_le_holder
      (hG_abs x hx) (hV_abs y hy) hG_holder hV_holder
      hG0_nn (by norm_num : (0 : ℝ) ≤ 1) hL0_nn hHV_nn (abs_nonneg (x - y))
    simpa using hraw
  have hWd_holder : |Wd x - Wd y| ≤ HWd * |x - y| ^ eta := by
    have heq : Wd x - Wd y = (-p.β) * (G x * V x - G y * V y) := by
      dsimp [Wd]
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg p.hβ, hHWd]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hGV_holder p.hβ
  let A : ℝ → ℝ := fun z => deriv U z * G z + U z * deriv G z
  let UG : ℝ → ℝ := fun z => U z * G z
  have hA_abs : |A x| ≤ BA := by
    dsimp [A]
    rw [hBA]
    calc
      |deriv U x * G x + U x * deriv G x|
          ≤ |deriv U x * G x| + |U x * deriv G x| := abs_add_le _ _
      _ = |deriv U x| * |G x| + |U x| * |deriv G x| := by
        rw [abs_mul, abs_mul]
      _ ≤ CU * G0 + D.M * L0 :=
        add_le_add
          (mul_le_mul (hUd_bound x hx) (hG_abs x hx) (abs_nonneg _) hCU_nn)
          (mul_le_mul (hU_abs x hx) (hGd_bound x hx) (abs_nonneg _) D.hM.le)
  have hA_holder : |A x - A y| ≤ HA * |x - y| ^ eta := by
    have hfirst := abs_mul_sub_mul_le_holder
      (hUd_bound x hx) (hG_abs y hy) hUd_holder hG_holder
      hCU_nn hG0_nn hHU_nn hL0_nn (abs_nonneg (x - y))
    have hsecond := abs_mul_sub_mul_le_holder
      (hU_abs x hx) (hGd_bound y hy) hU_holder hGd_holder
      D.hM.le hL0_nn hCU_nn hHGd_nn (abs_nonneg (x - y))
    dsimp [A]
    rw [hHA]
    calc
      |(deriv U x * G x + U x * deriv G x) -
          (deriv U y * G y + U y * deriv G y)|
          = |(deriv U x * G x - deriv U y * G y) +
              (U x * deriv G x - U y * deriv G y)| := by ring_nf
      _ ≤ |deriv U x * G x - deriv U y * G y| +
            |U x * deriv G x - U y * deriv G y| := abs_add_le _ _
      _ ≤ (HU * G0 + CU * L0) * |x - y| ^ eta +
            (CU * L0 + D.M * HGd) * |x - y| ^ eta :=
        add_le_add hfirst hsecond
      _ = ((HU * G0 + CU * L0) + (CU * L0 + D.M * HGd)) *
            |x - y| ^ eta := by ring
  have hAW_holder : |A x * W x - A y * W y| ≤
      (HA + BA * HW) * |x - y| ^ eta := by
    have hraw := abs_mul_sub_mul_le_holder hA_abs (hW_abs y hy)
      hA_holder hW_holder hBA_nn (by norm_num : (0 : ℝ) ≤ 1)
      hHA_nn hHW_nn (abs_nonneg (x - y))
    simpa using hraw
  have hUG_abs : |UG x| ≤ D.M * G0 := by
    dsimp [UG]
    rw [abs_mul]
    exact mul_le_mul (hU_abs x hx) (hG_abs x hx) (abs_nonneg _) D.hM.le
  have hUG_holder : |UG x - UG y| ≤ BA * |x - y| ^ eta := by
    have hraw := abs_mul_sub_mul_le_holder
      (hU_abs x hx) (hG_abs y hy) hU_holder hG_holder
      D.hM.le hG0_nn hCU_nn hL0_nn (abs_nonneg (x - y))
    rw [hBA]
    exact hraw
  have hUGWd_holder : |UG x * Wd x - UG y * Wd y| ≤
      (BA * HW + (D.M * G0) * HWd) * |x - y| ^ eta := by
    exact abs_mul_sub_mul_le_holder hUG_abs (hWd_abs y hy)
      hUG_holder hWd_holder (mul_nonneg D.hM.le hG0_nn) hHW_nn
      hBA_nn hHWd_nn (abs_nonneg (x - y))
  have hQx := conjugateMild_chemFlux_deriv_eq_components
    D hu₀ hu₀_meas ht htT hx
  have hQy := conjugateMild_chemFlux_deriv_eq_components
    D hu₀ hu₀_meas ht htT hy
  change deriv (chemFluxLifted p (D.u t)) x = A x * W x + UG x * Wd x at hQx
  change deriv (chemFluxLifted p (D.u t)) y = A y * W y + UG y * Wd y at hQy
  rw [hQx, hQy, hH]
  calc
    |(A x * W x + UG x * Wd x) - (A y * W y + UG y * Wd y)|
        = |(A x * W x - A y * W y) +
            (UG x * Wd x - UG y * Wd y)| := by ring_nf
    _ ≤ |A x * W x - A y * W y| +
          |UG x * Wd x - UG y * Wd y| := abs_add_le _ _
    _ ≤ (HA + BA * HW) * |x - y| ^ eta +
          (BA * HW + D.M * G0 * HWd) * |x - y| ^ eta :=
      add_le_add hAW_holder hUGWd_holder
    _ = ((HA + BA * HW) + (BA * HW + D.M * G0 * HWd)) *
          |x - y| ^ eta := by ring

end ShenWork.Paper2
