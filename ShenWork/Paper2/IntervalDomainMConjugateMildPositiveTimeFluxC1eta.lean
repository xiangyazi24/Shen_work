/-
  Positive-time Holder regularity of the derivative of the faithful
  chemotaxis flux.  The resolver-gradient derivative is handled through the
  physical elliptic ODE, including the fractional-power case at `u = 0`.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildPositiveTimeC1
import ShenWork.Paper2.IntervalPositiveRpowHolder

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap (chemFluxMLifted)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (powerLip powerLip_nonneg signedPowerLip signedPowerLip_nonneg
   rpow_lipschitz_on_pos_Icc_real)

/-- The weak resolver ODE identifies the actual derivative of the resolver
gradient without any source-coefficient decay assumption. -/
theorem conjugateMildM_resolverGrad_deriv_eq_physical
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
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
    simpa [intervalDomainLift, hz] using
      D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)
  have hraw :=
    ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
      p hUcont hnonneg hx
  have hUx : 0 ≤ D.u t ⟨x, hxIcc⟩ :=
    D.hc.le.trans (D.hfloor t ht htT ⟨x, hxIcc⟩)
  rw [hraw.deriv]
  simp [ShenWork.IntervalResolverWeakBounds.resolverLapPhysical,
    ShenWork.IntervalResolverWeakBounds.resolverPositiveSourceLifted,
    intervalDomainLift, hxIcc, positivePart_eq_self_of_nonneg hUx]

/-- Product/chain-rule formula for the actual faithful chemotaxis flux
derivative at an interior positive-time point. -/
theorem conjugateMildM_chemFlux_deriv_eq_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    let U : ℝ → ℝ := intervalDomainLift (D.u t)
    let G : ℝ → ℝ := resolverGradReal p (D.u t)
    let R : ℝ → ℝ :=
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u t))
    let W : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
    deriv (chemFluxMLifted p (D.u t)) x =
      (((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
          U x ^ p.m * deriv G x) * W x +
        U x ^ p.m * G x *
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
  have hUraw := conjugateMildM_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      ht htT hx
  have hU' : HasDerivAt U (deriv U x) x := by
    simpa [U] using hUraw.differentiableAt.hasDerivAt
  have hGraw :=
    ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
      p hUcont (fun z hz => by
        simpa [U, intervalDomainLift, hz] using
          D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)) hx
  have hG' : HasDerivAt G (deriv G x) x := by
    simpa [G] using hGraw.differentiableAt.hasDerivAt
  have hR' : HasDerivAt R (G x) x := by
    simpa [R, G] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
        p hUcont hx
  have hR_nonneg : 0 ≤ R x := by
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u)
        (fun s hs hsT y => D.hc.le.trans (D.hfloor s hs hsT y))
        D.hcont ht htT ⟨x, hxIcc⟩
    simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hxIcc] using h
  have hW' : HasDerivAt W
      (G x * (-p.β) * (1 + R x) ^ (-p.β - 1)) x := by
    have hbase : HasDerivAt (fun z : ℝ => 1 + R z) (G x) x :=
      hR'.const_add 1
    simpa [W, sub_eq_add_neg] using
      hbase.rpow_const (p := -p.β) (Or.inl (by linarith : 1 + R x ≠ 0))
  have hUx_pos : 0 < U x := by
    simpa [U, intervalDomainLift, hxIcc] using
      D.hc.trans_le (D.hfloor t ht htT ⟨x, hxIcc⟩)
  have hUm' : HasDerivAt (fun z => U z ^ p.m)
      ((p.m * U x ^ (p.m - 1)) * deriv U x) x := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hU'.rpow_const (p := p.m) (Or.inl hUx_pos.ne')
  have hprod := (hUm'.mul hG').mul hW'
  have hev : chemFluxMLifted p (D.u t) =ᶠ[nhds x]
      (fun z => U z ^ p.m * G z * W z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hRz_nonneg : 0 ≤ R z := by
      have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (T := D.T) p (u := D.u)
          (fun s hs hsT y => D.hc.le.trans (D.hfloor s hs hsT y))
          D.hcont ht htT ⟨z, hzIcc⟩
      simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
        intervalDomainLift, hzIcc] using h
    unfold chemFluxMLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ 1 + R z)]
  simpa [U, G, R, W] using (hev.hasDerivAt_iff.mpr hprod).deriv

/-- On every positive-time strip, the derivative of the actual general-`m`
chemotaxis flux has one spatial power-Holder modulus.  The positive floor
makes every real power appearing in the chain rule locally Lipschitz. -/
theorem conjugateMildM_chemFlux_deriv_positiveTime_holder_uniform
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ eta H : ℝ, 0 < eta ∧ eta < 1 ∧ 0 ≤ H ∧
      ∀ t, τ ≤ t → t ≤ D.T →
        ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
          |deriv (chemFluxMLifted p (D.u t)) x -
            deriv (chemFluxMLifted p (D.u t)) y| ≤ H * |x - y| ^ eta := by
  set eta : ℝ := (1 / 4 : ℝ) with heta
  have heta0 : 0 < eta := by rw [heta]; norm_num
  have heta1 : eta < 1 := by rw [heta]; norm_num
  have heta1le : eta ≤ 1 := heta1.le
  obtain ⟨CU, hCU_nn, hUderiv_bound⟩ :=
    conjugateMildM_intervalDomainLift_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas hτ
  obtain ⟨HU, hHU_nn, hUderiv_holder⟩ :=
    conjugateMildM_intervalDomainLift_deriv_positiveTime_holder_uniform
      D hu₀ hu₀_meas hτ heta0 heta1
  set G0 : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hG0
  set L0 : ℝ := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p D.M
    with hL0
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set Lm : ℝ := powerLip p.m D.c D.M with hLm
  set Ldm : ℝ := p.m * signedPowerLip (p.m - 1) D.c D.M with hLdm
  set A0 : ℝ := D.M ^ p.m with hA0
  set HUm : ℝ := Lm * CU with hHUm
  set B0 : ℝ := Lm with hB0
  set HB : ℝ := Ldm * CU with hHB
  set Hγ : ℝ := powerLip p.γ D.c D.M * CU with hHγ
  set HGd : ℝ := p.μ * G0 + p.ν * Hγ with hHGd
  set HW : ℝ := p.β * G0 with hHW
  set HV : ℝ := (p.β + 1) * G0 with hHV
  set HWd : ℝ := p.β * (L0 + G0 * HV) with hHWd
  set BBU : ℝ := B0 * CU with hBBU
  set HBU : ℝ := HB * CU + B0 * HU with hHBU
  set BA : ℝ := BBU * G0 + A0 * L0 with hBA
  set HA : ℝ :=
    (HBU * G0 + BBU * L0) + (HUm * L0 + A0 * HGd) with hHA
  set HUG : ℝ := HUm * G0 + A0 * L0 with hHUG
  set H : ℝ :=
    (HA + BA * HW) + (HUG * HW + (A0 * G0) * HWd) with hH
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
  have hLm_nn : 0 ≤ Lm := by
    dsimp [Lm]
    exact powerLip_nonneg p.hm D.hc hcM
  have hLdm_nn : 0 ≤ Ldm := by
    dsimp [Ldm]
    exact mul_nonneg p.hm.le (signedPowerLip_nonneg D.hc hcM)
  have hA0_nn : 0 ≤ A0 := by dsimp [A0]; exact Real.rpow_nonneg D.hM.le _
  have hHUm_nn : 0 ≤ HUm := by dsimp [HUm]; exact mul_nonneg hLm_nn hCU_nn
  have hB0_nn : 0 ≤ B0 := by dsimp [B0]; exact hLm_nn
  have hHB_nn : 0 ≤ HB := by dsimp [HB]; exact mul_nonneg hLdm_nn hCU_nn
  have hHγ_nn : 0 ≤ Hγ := by
    dsimp [Hγ]
    exact mul_nonneg (powerLip_nonneg p.hγ D.hc hcM) hCU_nn
  have hHGd_nn : 0 ≤ HGd := by
    rw [hHGd]
    exact add_nonneg (mul_nonneg p.hμ.le hG0_nn)
      (mul_nonneg p.hν.le hHγ_nn)
  have hHW_nn : 0 ≤ HW := by rw [hHW]; exact mul_nonneg p.hβ hG0_nn
  have hHV_nn : 0 ≤ HV := by
    rw [hHV]
    exact mul_nonneg (by linarith [p.hβ]) hG0_nn
  have hHWd_nn : 0 ≤ HWd := by
    rw [hHWd]
    exact mul_nonneg p.hβ
      (add_nonneg hL0_nn (mul_nonneg hG0_nn hHV_nn))
  have hBBU_nn : 0 ≤ BBU := by dsimp [BBU]; exact mul_nonneg hB0_nn hCU_nn
  have hHBU_nn : 0 ≤ HBU := by
    dsimp [HBU]
    exact add_nonneg (mul_nonneg hHB_nn hCU_nn) (mul_nonneg hB0_nn hHU_nn)
  have hBA_nn : 0 ≤ BA := by
    rw [hBA]
    exact add_nonneg (mul_nonneg hBBU_nn hG0_nn)
      (mul_nonneg hA0_nn hL0_nn)
  have hHA_nn : 0 ≤ HA := by
    rw [hHA]
    exact add_nonneg
      (add_nonneg (mul_nonneg hHBU_nn hG0_nn) (mul_nonneg hBBU_nn hL0_nn))
      (add_nonneg (mul_nonneg hHUm_nn hL0_nn) (mul_nonneg hA0_nn hHGd_nn))
  have hHUG_nn : 0 ≤ HUG := by
    rw [hHUG]
    exact add_nonneg (mul_nonneg hHUm_nn hG0_nn) (mul_nonneg hA0_nn hL0_nn)
  have hH_nn : 0 ≤ H := by
    rw [hH]
    exact add_nonneg
      (add_nonneg hHA_nn (mul_nonneg hBA_nn hHW_nn))
      (add_nonneg (mul_nonneg hHUG_nn hHW_nn)
        (mul_nonneg (mul_nonneg hA0_nn hG0_nn) hHWd_nn))
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
    simpa [U, intervalDomainLift, hz] using
      D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)
  have hUfloor : ∀ z ∈ Set.Icc (0 : ℝ) 1, D.c ≤ U z := by
    intro z hz
    simpa [U, intervalDomainLift, hz] using D.hfloor t ht htT ⟨z, hz⟩
  have hUupper : ∀ z ∈ Set.Icc (0 : ℝ) 1, U z ≤ D.M := by
    intro z hz
    have h := D.hbound t ht htT ⟨z, hz⟩
    simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2
  have hUdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ U z := by
    intro z hz
    simpa [U] using
      (conjugateMildM_intervalDomainLift_hasDerivAt_interior
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
      (T := D.T) p (u := D.u)
        (fun s hs hsT q => D.hc.le.trans (D.hfloor s hs hsT q))
        D.hcont ht htT ⟨z, hzIcc⟩
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
      Hγ * |x - y| ^ eta := by
    have hpow := ShenWork.Paper2.rpow_lipschitz_on_pos_Icc p.hγ D.hc
      ⟨hUfloor x (Set.Ioo_subset_Icc_self hx),
        hUupper x (Set.Ioo_subset_Icc_self hx)⟩
      ⟨hUfloor y (Set.Ioo_subset_Icc_self hy),
        hUupper y (Set.Ioo_subset_Icc_self hy)⟩
    have hscaled := mul_le_mul_of_nonneg_left hU_holder
      (powerLip_nonneg p.hγ D.hc hcM)
    exact hpow.trans (by simpa [Hγ, powerLip, mul_assoc] using hscaled)
  have hGd_eq : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      deriv G z = p.μ * R z - p.ν * (U z) ^ p.γ := by
    intro z hz
    simpa [G, R, U] using
      conjugateMildM_resolverGrad_deriv_eq_physical D ht htT hz
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
            (p.ν * Hγ) * |x - y| ^ eta := by
        rw [abs_mul, abs_mul, abs_of_pos p.hμ, abs_of_pos p.hν]
        exact add_le_add
          (by simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hR_holder p.hμ.le)
          (by simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hUpow_holder p.hν.le)
      _ = (p.μ * G0 + p.ν * Hγ) * |x - y| ^ eta := by ring
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
  let Um : ℝ → ℝ := fun z => U z ^ p.m
  let B : ℝ → ℝ := fun z => p.m * U z ^ (p.m - 1)
  let BU : ℝ → ℝ := fun z => B z * deriv U z
  let A : ℝ → ℝ := fun z => BU z * G z + Um z * deriv G z
  let UG : ℝ → ℝ := fun z => Um z * G z
  have hUm_abs : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |Um z| ≤ A0 := by
    intro z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    rw [show Um z = U z ^ p.m by rfl,
      abs_of_nonneg (Real.rpow_nonneg (hUnonneg z hzIcc) _), hA0]
    exact Real.rpow_le_rpow (hUnonneg z hzIcc) (hUupper z hzIcc) p.hm.le
  have hB_abs : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |B z| ≤ B0 := by
    intro z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hpow : U z ^ (p.m - 1) ≤
        D.c ^ (p.m - 1) + D.M ^ (p.m - 1) := by
      rcases le_or_gt 1 p.m with hm1 | hm1
      · have hmono : U z ^ (p.m - 1) ≤ D.M ^ (p.m - 1) :=
          Real.rpow_le_rpow (hUnonneg z hzIcc) (hUupper z hzIcc) (by linarith)
        linarith [Real.rpow_nonneg D.hc.le (p.m - 1)]
      · have hmono : U z ^ (p.m - 1) ≤ D.c ^ (p.m - 1) :=
          Real.rpow_le_rpow_of_nonpos D.hc (hUfloor z hzIcc) (by linarith)
        linarith [Real.rpow_nonneg D.hM.le (p.m - 1)]
    rw [show B z = p.m * U z ^ (p.m - 1) by rfl,
      abs_of_nonneg (mul_nonneg p.hm.le (Real.rpow_nonneg (hUnonneg z hzIcc) _))]
    change p.m * U z ^ (p.m - 1) ≤
      p.m * (D.c ^ (p.m - 1) + D.M ^ (p.m - 1))
    exact mul_le_mul_of_nonneg_left hpow p.hm.le
  have hUm_holder : |Um x - Um y| ≤ HUm * |x - y| ^ eta := by
    have hpow := ShenWork.Paper2.rpow_lipschitz_on_pos_Icc p.hm D.hc
      ⟨hUfloor x (Set.Ioo_subset_Icc_self hx),
        hUupper x (Set.Ioo_subset_Icc_self hx)⟩
      ⟨hUfloor y (Set.Ioo_subset_Icc_self hy),
        hUupper y (Set.Ioo_subset_Icc_self hy)⟩
    rw [show Um x = U x ^ p.m by rfl, show Um y = U y ^ p.m by rfl]
    have hscaled := mul_le_mul_of_nonneg_left hU_holder hLm_nn
    exact hpow.trans (by simpa [HUm, Lm, powerLip, mul_assoc] using hscaled)
  have hB_holder : |B x - B y| ≤ HB * |x - y| ^ eta := by
    have hpow := rpow_lipschitz_on_pos_Icc_real D.hc
      ⟨hUfloor x (Set.Ioo_subset_Icc_self hx),
        hUupper x (Set.Ioo_subset_Icc_self hx)⟩
      ⟨hUfloor y (Set.Ioo_subset_Icc_self hy),
        hUupper y (Set.Ioo_subset_Icc_self hy)⟩
      (q := p.m - 1)
    have hmulpow : |B x - B y| ≤
        Ldm * |U x - U y| := by
      rw [show B x = p.m * U x ^ (p.m - 1) by rfl,
        show B y = p.m * U y ^ (p.m - 1) by rfl, ← mul_sub,
        abs_mul, abs_of_nonneg p.hm.le, hLdm]
      have hscaled := mul_le_mul_of_nonneg_left hpow p.hm.le
      simpa [Ldm, mul_assoc] using hscaled
    have hscaled := mul_le_mul_of_nonneg_left hU_holder hLdm_nn
    exact hmulpow.trans (by simpa [HB, mul_assoc] using hscaled)
  have hBU_abs : |BU x| ≤ BBU := by
    rw [show BU x = B x * deriv U x by rfl, abs_mul, hBBU]
    exact mul_le_mul (hB_abs x hx) (hUd_bound x hx) (abs_nonneg _) hB0_nn
  have hBU_holder : |BU x - BU y| ≤ HBU * |x - y| ^ eta := by
    have hraw := abs_mul_sub_mul_le_holder
      (hB_abs x hx) (hUd_bound y hy) hB_holder hUd_holder
      hB0_nn hCU_nn hHB_nn hHU_nn (abs_nonneg (x - y))
    simpa [BU, HBU] using hraw
  have hA_abs : |A x| ≤ BA := by
    dsimp [A]
    rw [hBA]
    calc
      |BU x * G x + Um x * deriv G x|
          ≤ |BU x * G x| + |Um x * deriv G x| := abs_add_le _ _
      _ = |BU x| * |G x| + |Um x| * |deriv G x| := by
        simp only [abs_mul]
      _ ≤ BBU * G0 + A0 * L0 :=
        add_le_add
          (mul_le_mul hBU_abs (hG_abs x hx) (abs_nonneg _) hBBU_nn)
          (mul_le_mul (hUm_abs x hx) (hGd_bound x hx) (abs_nonneg _) hA0_nn)
  have hA_holder : |A x - A y| ≤ HA * |x - y| ^ eta := by
    have hfirst := abs_mul_sub_mul_le_holder
      hBU_abs (hG_abs y hy) hBU_holder hG_holder
      hBBU_nn hG0_nn hHBU_nn hL0_nn (abs_nonneg (x - y))
    have hsecond := abs_mul_sub_mul_le_holder
      (hUm_abs x hx) (hGd_bound y hy) hUm_holder hGd_holder
      hA0_nn hL0_nn hHUm_nn hHGd_nn (abs_nonneg (x - y))
    dsimp [A]
    rw [hHA]
    calc
      |(BU x * G x + Um x * deriv G x) -
          (BU y * G y + Um y * deriv G y)|
          = |(BU x * G x - BU y * G y) +
              (Um x * deriv G x - Um y * deriv G y)| := by ring_nf
      _ ≤ |BU x * G x - BU y * G y| +
            |Um x * deriv G x - Um y * deriv G y| := abs_add_le _ _
      _ ≤ (HBU * G0 + BBU * L0) * |x - y| ^ eta +
            (HUm * L0 + A0 * HGd) * |x - y| ^ eta :=
        add_le_add hfirst hsecond
      _ = ((HBU * G0 + BBU * L0) + (HUm * L0 + A0 * HGd)) *
            |x - y| ^ eta := by ring
  have hAW_holder : |A x * W x - A y * W y| ≤
      (HA + BA * HW) * |x - y| ^ eta := by
    have hraw := abs_mul_sub_mul_le_holder hA_abs (hW_abs y hy)
      hA_holder hW_holder hBA_nn (by norm_num : (0 : ℝ) ≤ 1)
      hHA_nn hHW_nn (abs_nonneg (x - y))
    simpa using hraw
  have hUG_abs : |UG x| ≤ A0 * G0 := by
    dsimp [UG]
    rw [abs_mul]
    exact mul_le_mul (hUm_abs x hx) (hG_abs x hx) (abs_nonneg _) hA0_nn
  have hUG_holder : |UG x - UG y| ≤ HUG * |x - y| ^ eta := by
    have hraw := abs_mul_sub_mul_le_holder
      (hUm_abs x hx) (hG_abs y hy) hUm_holder hG_holder
      hA0_nn hG0_nn hHUm_nn hL0_nn (abs_nonneg (x - y))
    rw [hHUG]
    exact hraw
  have hUGWd_holder : |UG x * Wd x - UG y * Wd y| ≤
      (HUG * HW + (A0 * G0) * HWd) * |x - y| ^ eta := by
    exact abs_mul_sub_mul_le_holder hUG_abs (hWd_abs y hy)
      hUG_holder hWd_holder (mul_nonneg hA0_nn hG0_nn) hHW_nn
      hHUG_nn hHWd_nn (abs_nonneg (x - y))
  have hQx := conjugateMildM_chemFlux_deriv_eq_components
    D hu₀ hu₀_meas ht htT hx
  have hQy := conjugateMildM_chemFlux_deriv_eq_components
    D hu₀ hu₀_meas ht htT hy
  change deriv (chemFluxMLifted p (D.u t)) x = A x * W x + UG x * Wd x at hQx
  change deriv (chemFluxMLifted p (D.u t)) y = A y * W y + UG y * Wd y at hQy
  rw [hQx, hQy, hH]
  calc
    |(A x * W x + UG x * Wd x) - (A y * W y + UG y * Wd y)|
        = |(A x * W x - A y * W y) +
            (UG x * Wd x - UG y * Wd y)| := by ring_nf
    _ ≤ |A x * W x - A y * W y| +
          |UG x * Wd x - UG y * Wd y| := abs_add_le _ _
    _ ≤ (HA + BA * HW) * |x - y| ^ eta +
          (HUG * HW + A0 * G0 * HWd) * |x - y| ^ eta :=
      add_le_add hAW_holder hUGWd_holder
    _ = ((HA + BA * HW) + (HUG * HW + A0 * G0 * HWd)) *
          |x - y| ^ eta := by ring

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_chemFlux_deriv_eq_components
#print axioms ShenWork.Paper2.conjugateMildM_chemFlux_deriv_positiveTime_holder_uniform
