import ShenWork.Paper3.EventualExponentialStability
import ShenWork.Paper3.LyapunovFunction
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz

/-! # Minimal-model signal energy on the unit interval

This file supplies the concrete elliptic identities behind Theorem 2.5(ii).
The key point is that for `γ = 1` the Neumann resolver is self-adjoint.  We
prove that fact directly from the classical elliptic equation and genuine
closed-interval Neumann integration by parts; no abstract stability package is
used.
-/

namespace ShenWork.Paper3

open Filter MeasureTheory Set Topology
open scoped Interval Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.IntervalUnderIntegralLeibniz

noncomputable section

/-- Closed-interval continuity of the spatial derivative of the signal slice. -/
theorem intervalDomain_solution_v_deriv_lift_continuousOn_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ContinuousOn (deriv (intervalDomainLift (v t))) (Icc (0 : ℝ) 1) := by
  classical
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).2
  have hlimits := (hsol.regularity.2.2.2.1 t ht).2
  have hzero := (hsol.regularity.2.2.2.2.1 t ht).2
  have hinterior :
      ContinuousOn (deriv (intervalDomainLift (v t))) (Ioo (0 : ℝ) 1) :=
    hC2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · rw [ContinuousWithinAt, hzero.2.1,
      nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0 : ℝ) < 1)]
    have hsplit :
        𝓝[Ici (0 : ℝ)] 0 = 𝓝[Ioi (0 : ℝ)] 0 ⊔ 𝓝[{(0 : ℝ)}] 0 := by
      rw [← nhdsWithin_union, Ioi_union_left]
    rw [hsplit, Filter.tendsto_sup]
    refine ⟨hlimits.1, ?_⟩
    rw [nhdsWithin_singleton]
    have h := tendsto_pure_nhds (deriv (intervalDomainLift (v t))) (0 : ℝ)
    rwa [hzero.2.1] at h
  · rcases eq_or_lt_of_le hx.2 with rfl | hx1
    · rw [ContinuousWithinAt, hzero.2.2,
        nhdsWithin_Icc_eq_nhdsLE (by norm_num : (0 : ℝ) < 1)]
      have hsplit :
          𝓝[Iic (1 : ℝ)] 1 = 𝓝[Iio (1 : ℝ)] 1 ⊔ 𝓝[{(1 : ℝ)}] 1 := by
        rw [← nhdsWithin_union, Iio_union_right]
      rw [hsplit, Filter.tendsto_sup]
      refine ⟨hlimits.2, ?_⟩
      rw [nhdsWithin_singleton]
      have h := tendsto_pure_nhds (deriv (intervalDomainLift (v t))) (1 : ℝ)
      rwa [hzero.2.2] at h
    · exact (hinterior x ⟨hx0, hx1⟩).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds
          (IsOpen.mem_nhds isOpen_Ioo ⟨hx0, hx1⟩))

/-- Interior first- and second-spatial derivatives of a signal slice. -/
theorem intervalDomain_solution_v_lift_hasDerivAt_interior
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t x : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (intervalDomainLift (v t))
        (deriv (intervalDomainLift (v t)) x) x ∧
      HasDerivAt (deriv (intervalDomainLift (v t)))
        (deriv (fun z => deriv (intervalDomainLift (v t)) z) x) x := by
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).2
  have h1 : DifferentiableAt ℝ (intervalDomainLift (v t)) x :=
    (hC2.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hx)
  have hC1 : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v t)))
      (Ioo (0 : ℝ) 1) :=
    hC2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) x :=
    (hC1.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hx)
  exact ⟨h1.hasDerivAt, h2.hasDerivAt⟩

/-- The second spatial derivative of a classical signal slice is interval
integrable. -/
theorem intervalDomain_solution_v_lap_lift_intervalIntegrable
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    IntervalIntegrable
      (fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y)
      volume 0 1 := by
  classical
  have hCc : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hCo : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).2
  have huniq : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
    uniqueDiffOn_Icc (by norm_num)
  let ddIcc : ℝ → ℝ :=
    derivWithin (derivWithin (intervalDomainLift (v t)) (Icc (0 : ℝ) 1))
      (Icc (0 : ℝ) 1)
  have hC1 : ContDiffOn ℝ 1
      (derivWithin (intervalDomainLift (v t)) (Icc (0 : ℝ) 1))
      (Icc (0 : ℝ) 1) := hCc.derivWithin huniq (by norm_num)
  have hddCont : ContinuousOn ddIcc (Icc (0 : ℝ) 1) :=
    hC1.continuousOn_derivWithin huniq (by norm_num)
  have hddInt : IntervalIntegrable ddIcc volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hddCont
  have heq : EqOn
      (fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y)
      ddIcc (Ioo (0 : ℝ) 1) := by
    intro y hy
    have hinner : ∀ z ∈ Ioo (0 : ℝ) 1,
        deriv (intervalDomainLift (v t)) z =
          derivWithin (intervalDomainLift (v t)) (Icc (0 : ℝ) 1) z := by
      intro z hz
      have hd : DifferentiableAt ℝ (intervalDomainLift (v t)) z :=
        (hCo.differentiableOn (by norm_num)).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioo hz)
      rw [hd.derivWithin
        (huniq.uniqueDiffWithinAt (Ioo_subset_Icc_self hz))]
    have hout :
        deriv (fun z => deriv (intervalDomainLift (v t)) z) y =
          deriv (derivWithin (intervalDomainLift (v t)) (Icc (0 : ℝ) 1)) y := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy] with z hz
      exact hinner z hz
    have hd : DifferentiableAt ℝ
        (derivWithin (intervalDomainLift (v t)) (Icc (0 : ℝ) 1)) y :=
      (hC1.differentiableOn (by norm_num)).differentiableAt
        (mem_nhds_iff.2
          ⟨Ioo (0 : ℝ) 1, Ioo_subset_Icc_self, isOpen_Ioo, hy⟩)
    change deriv (fun z => deriv (intervalDomainLift (v t)) z) y = ddIcc y
    rw [hout]
    simpa [ddIcc] using (hd.derivWithin
      (huniq.uniqueDiffWithinAt (Ioo_subset_Icc_self hy))).symm
  refine hddInt.congr_ae ?_
  rw [uIoc_of_le zero_le_one]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
  refine (ae_iff).2 (measure_mono_null ?_ hnull)
  intro y hy
  simp only [mem_setOf_eq] at hy
  push_neg at hy
  obtain ⟨hyIoc, hne⟩ := hy
  simp only [mem_singleton_iff]
  by_contra hy1
  exact hne ((heq ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩).symm)

/-- Neumann integration by parts between two signal slices. -/
theorem intervalDomain_minimal_signal_cross_ibp
    {p : CM2Params} {T s t vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs : s ∈ Ioo (0 : ℝ) T) (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (v s) y - vStar) *
          deriv (fun z => deriv (intervalDomainLift (v t)) z) y) =
      -∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (v s)) y *
          deriv (intervalDomainLift (v t)) y := by
  let phi : ℝ → ℝ := fun y => intervalDomainLift (v s) y - vStar
  let phi' : ℝ → ℝ := fun y => deriv (intervalDomainLift (v s)) y
  let F : ℝ → ℝ := fun y => deriv (intervalDomainLift (v t)) y
  let F' : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y
  have hphiCont : ContinuousOn phi (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 s hs).2.1.continuousOn).sub
      continuousOn_const
  have hFCont : ContinuousOn F (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le zero_le_one, F] using
      intervalDomain_solution_v_deriv_lift_continuousOn_Icc hsol ht
  have hphi : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt phi (phi' y) y := by
    intro y hy
    simpa [phi, phi'] using
      (intervalDomain_solution_v_lift_hasDerivAt_interior hsol hs hy).1.sub_const vStar
  have hF : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' y) y := by
    intro y hy
    simpa [F, F'] using
      (intervalDomain_solution_v_lift_hasDerivAt_interior hsol ht hy).2
  have hphiInt : IntervalIntegrable phi' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one, phi'] using
      intervalDomain_solution_v_deriv_lift_continuousOn_Icc hsol hs
  have hFInt : IntervalIntegrable F' volume 0 1 := by
    simpa [F'] using intervalDomain_solution_v_lap_lift_intervalIntegrable hsol ht
  have hzero := (hsol.regularity.2.2.2.2.1 t ht).2
  simpa [phi, phi', F, F'] using
    (intervalFluxByParts_open hphiCont hFCont hphi hF hphiInt hFInt
      hzero.2.1 hzero.2.2)

/-- At `γ = 1`, subtracting the constant equilibrium from the elliptic
equation gives `ν(u-u*) = μ(v-v*) - vₓₓ` on the open interval. -/
theorem intervalDomain_minimal_elliptic_difference
    {p : CM2Params} {T t uStar vStar y : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (hy : y ∈ Ioo (0 : ℝ) 1) :
    p.ν * (intervalDomainLift (u t) y - uStar) =
      p.μ * (intervalDomainLift (v t) y - vStar) -
        deriv (fun z => deriv (intervalDomainLift (v t)) z) y := by
  let x : intervalDomainPoint := ⟨y, Ioo_subset_Icc_self hy⟩
  have hpde := hsol.pde_v ht.1 ht.2 (x := x) hy
  have hu : u t x = intervalDomainLift (u t) y := by
    simp [x, intervalDomainLift, Ioo_subset_Icc_self hy]
  have hv : v t x = intervalDomainLift (v t) y := by
    simp [x, intervalDomainLift, Ioo_subset_Icc_self hy]
  have hlap : intervalDomain.laplacian (v t) x =
      deriv (fun z => deriv (intervalDomainLift (v t)) z) y := rfl
  have heq' : p.μ * vStar = p.ν * uStar := by
    simpa [hgamma] using heq.elliptic_relation
  rw [hlap, hu, hv, hgamma, Real.rpow_one] at hpde
  linarith

/-- The scaled cross pairing has the symmetric resolvent representation. -/
theorem intervalDomain_minimal_signal_pairing_scaled
    {p : CM2Params} {T s t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs : s ∈ Ioo (0 : ℝ) T) (ht : t ∈ Ioo (0 : ℝ) T) :
    p.ν * (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y - uStar) *
          (intervalDomainLift (v s) y - vStar)) =
      p.μ * (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (v t) y - vStar) *
          (intervalDomainLift (v s) y - vStar)) +
        ∫ y in (0 : ℝ)..1,
          deriv (intervalDomainLift (v t)) y *
            deriv (intervalDomainLift (v s)) y := by
  let A : ℝ → ℝ := fun y => intervalDomainLift (u t) y - uStar
  let Ws : ℝ → ℝ := fun y => intervalDomainLift (v s) y - vStar
  let Wt : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let Lapt : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y
  have hACont : ContinuousOn A (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hWsCont : ContinuousOn Ws (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 s hs).2.1.continuousOn).sub
      continuousOn_const
  have hWtCont : ContinuousOn Wt (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
      continuousOn_const
  have hAInt : IntervalIntegrable A volume 0 1 := hACont.intervalIntegrable
  have hWsInt : IntervalIntegrable Ws volume 0 1 := hWsCont.intervalIntegrable
  have hWtInt : IntervalIntegrable Wt volume 0 1 := hWtCont.intervalIntegrable
  have hLapInt : IntervalIntegrable Lapt volume 0 1 := by
    simpa [Lapt] using intervalDomain_solution_v_lap_lift_intervalIntegrable hsol ht
  have hAWs : IntervalIntegrable (fun y => A y * Ws y) volume 0 1 :=
    by simpa [mul_comm] using hAInt.continuousOn_mul hWsCont
  have hWtWs : IntervalIntegrable (fun y => Wt y * Ws y) volume 0 1 :=
    by simpa [mul_comm] using hWtInt.continuousOn_mul hWsCont
  have hLapWs : IntervalIntegrable (fun y => Lapt y * Ws y) volume 0 1 :=
    by simpa [mul_comm] using hLapInt.continuousOn_mul hWsCont
  have hpoint : EqOn (fun y => p.ν * (A y * Ws y))
      (fun y => p.μ * (Wt y * Ws y) - Lapt y * Ws y)
      (Ioo (0 : ℝ) 1) := by
    intro y hy
    have h := intervalDomain_minimal_elliptic_difference
      hgamma heq hsol ht hy
    calc
      p.ν * (A y * Ws y) = (p.ν * A y) * Ws y := by ring
      _ = (p.μ * Wt y - Lapt y) * Ws y := by rw [h]
      _ = p.μ * (Wt y * Ws y) - Lapt y * Ws y := by ring
  have hscaled :
      p.ν * (∫ y in (0 : ℝ)..1, A y * Ws y) =
        p.μ * (∫ y in (0 : ℝ)..1, Wt y * Ws y) -
          ∫ y in (0 : ℝ)..1, Lapt y * Ws y := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
        (hWtWs.const_mul p.μ) hLapWs]
    apply intervalIntegral.integral_congr_ae
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc, hne⟩ := hy
    rw [uIoc_of_le zero_le_one] at hyIoc
    simp only [mem_singleton_iff]
    by_contra hy1
    exact hne (hpoint ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩)
  have hibp := intervalDomain_minimal_signal_cross_ibp
    (vStar := vStar) hsol hs ht
  have hLapComm : (∫ y in (0 : ℝ)..1, Lapt y * Ws y) =
      ∫ y in (0 : ℝ)..1, Ws y * Lapt y := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hGradComm : (∫ y in (0 : ℝ)..1,
      deriv (intervalDomainLift (v s)) y *
        deriv (intervalDomainLift (v t)) y) =
      ∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (v t)) y *
          deriv (intervalDomainLift (v s)) y := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hLapComm, hibp, hGradComm] at hscaled
  dsimp [A, Ws, Wt] at hscaled
  linarith

/-- Self-adjointness of the `γ = 1` elliptic signal map on positive slices. -/
theorem intervalDomain_minimal_signal_pairing_comm
    {p : CM2Params} {T s t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs : s ∈ Ioo (0 : ℝ) T) (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y - uStar) *
          (intervalDomainLift (v s) y - vStar)) =
      ∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u s) y - uStar) *
          (intervalDomainLift (v t) y - vStar) := by
  have hts := intervalDomain_minimal_signal_pairing_scaled
    hgamma heq hsol hs ht
  have hst := intervalDomain_minimal_signal_pairing_scaled
    hgamma heq hsol ht hs
  have hvalue :
      (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (v t) y - vStar) *
            (intervalDomainLift (v s) y - vStar)) =
        ∫ y in (0 : ℝ)..1,
          (intervalDomainLift (v s) y - vStar) *
            (intervalDomainLift (v t) y - vStar) := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hgradient :
      (∫ y in (0 : ℝ)..1,
          deriv (intervalDomainLift (v t)) y *
            deriv (intervalDomainLift (v s)) y) =
        ∫ y in (0 : ℝ)..1,
          deriv (intervalDomainLift (v s)) y *
            deriv (intervalDomainLift (v t)) y := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  have hrhs :
      p.μ * (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (v t) y - vStar) *
            (intervalDomainLift (v s) y - vStar)) +
        ∫ y in (0 : ℝ)..1,
          deriv (intervalDomainLift (v t)) y *
            deriv (intervalDomainLift (v s)) y =
      p.μ * (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (v s) y - vStar) *
            (intervalDomainLift (v t) y - vStar)) +
        ∫ y in (0 : ℝ)..1,
          deriv (intervalDomainLift (v s)) y *
            deriv (intervalDomainLift (v t)) y := by
    rw [hvalue, hgradient]
  rw [hrhs] at hts
  exact (mul_left_cancel₀ (ne_of_gt p.hν) (hts.trans hst.symm))

/-- On a classical `γ = 1` slice, the physical signal energy is the positive
elliptic pairing `ν∫(u-u*)(v-v*)`. -/
theorem intervalDomain_chemotaxisSignalEnergy_eq_pairing
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    chemotaxisSignalEnergy intervalDomain p.μ vStar v t =
      p.ν * (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y - uStar) *
          (intervalDomainLift (v t) y - vStar)) := by
  have hscaled := intervalDomain_minimal_signal_pairing_scaled
    hgamma heq hsol ht ht
  rw [show (∫ y in (0 : ℝ)..1,
      deriv (intervalDomainLift (v t)) y *
        deriv (intervalDomainLift (v t)) y) =
      ∫ y in (0 : ℝ)..1, (deriv (intervalDomainLift (v t)) y) ^ 2 from by
        apply intervalIntegral.integral_congr
        intro y _
        ring] at hscaled
  have henergy :
      chemotaxisSignalEnergy intervalDomain p.μ vStar v t =
        p.μ * (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (v t) y - vStar) *
            (intervalDomainLift (v t) y - vStar)) +
          ∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2 := by
    have hvalueCont : ContinuousOn
        (fun y => intervalDomainLift (v t) y - vStar) (uIcc (0 : ℝ) 1) := by
      rw [uIcc_of_le zero_le_one]
      exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
        continuousOn_const
    have hvalueInt : IntervalIntegrable
        (fun y => p.μ *
          ((intervalDomainLift (v t) y - vStar) *
            (intervalDomainLift (v t) y - vStar))) volume 0 1 := by
      exact ((hvalueCont.mul hvalueCont).const_mul p.μ).intervalIntegrable
    have hgradCont : ContinuousOn
        (fun y => (deriv (intervalDomainLift (v t)) y) ^ 2)
        (uIcc (0 : ℝ) 1) := by
      rw [uIcc_of_le zero_le_one]
      exact (intervalDomain_solution_v_deriv_lift_continuousOn_Icc hsol ht).pow 2
    have hgradInt : IntervalIntegrable
        (fun y => (deriv (intervalDomainLift (v t)) y) ^ 2) volume 0 1 :=
      hgradCont.intervalIntegrable
    unfold chemotaxisSignalEnergy intervalDomain intervalDomainIntegral
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add hvalueInt hgradInt]
    apply intervalIntegral.integral_congr_ae
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc, hne⟩ := hy
    rw [uIoc_of_le zero_le_one] at hyIoc
    simp only [mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Ioo (0 : ℝ) 1 :=
      ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
    have hliftDiff :
        (fun z => intervalDomainLift (fun x => v t x - vStar) z) =ᶠ[𝓝 y]
          fun z => intervalDomainLift (v t) z - vStar := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hyIoo] with z hz
      have hzIcc := Ioo_subset_Icc_self hz
      simp [intervalDomainLift, hzIcc]
    have hderiv :
        deriv (intervalDomainLift (fun x => v t x - vStar)) y =
          deriv (intervalDomainLift (v t)) y := by
      rw [hliftDiff.deriv_eq]
      simp
    have hyIcc := Ioo_subset_Icc_self hyIoo
    apply hne
    simp only [intervalDomainLift, hyIcc, dif_pos, intervalDomainGradNorm]
    rw [hderiv, sq_abs]
    ring
  exact henergy.trans hscaled.symm

/-! ## Time differentiation through the self-adjoint pairing -/

/-- A reusable closed-slab Leibniz rule for jointly continuous scalar fields on
the unit interval. -/
theorem intervalDomain_joint_intervalIntegral_hasDerivAt
    {T t : ℝ} {F F' : ℝ → ℝ → ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hF : ContinuousOn (Function.uncurry F)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1))
    (hF' : ContinuousOn (Function.uncurry F')
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1))
    (hdiff : ∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => F r y) (F' s y) s) :
    HasDerivAt (fun s => ∫ y in (0 : ℝ)..1, F s y)
      (∫ y in (0 : ℝ)..1, F' t y) t := by
  obtain ⟨delta, hdelta, hball, hIcc⟩ :=
    ShenWork.Paper2.exists_closedSlab_subset ht
  have hslab := hF'.mono (Set.prod_mono hIcc (le_refl _))
  obtain ⟨bound, hboundInt, hbound⟩ :=
    exists_bound_of_continuousOn_slab hdelta hslab
  have hFint : IntervalIntegrable (F t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hF ht
  have hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (F s) intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ((ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hF hs).mono
      Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hF'meas : AEStronglyMeasurable (F' t)
      intervalDomainInteriorMeasure :=
    ((ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hF' ht).mono
      Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hdiffAE : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball t delta,
        HasDerivAt (fun r => F r y) (F' s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    exact Filter.Eventually.of_forall fun y hy s hs =>
      hdiff s (hball hs) y hy
  exact intervalIntegral_hasDerivAt_time_of_local hdelta hFmeas hFint
    hF'meas hbound hboundInt hdiffAE

/-- Lifted diagonal pairing `∫(u-u*)(v-v*)`. -/
def intervalDomainMinimalSignalPairingIntegrand
    (u v : ℝ → intervalDomainPoint → ℝ) (uStar vStar s y : ℝ) : ℝ :=
  (intervalDomainLift (u s) y - uStar) *
    (intervalDomainLift (v s) y - vStar)

/-- Pointwise time derivative of the diagonal signal pairing. -/
def intervalDomainMinimalSignalPairingTimeIntegrand
    (u v : ℝ → intervalDomainPoint → ℝ) (uStar vStar s y : ℝ) : ℝ :=
  deriv (fun r => intervalDomainLift (u r) y) s *
      (intervalDomainLift (v s) y - vStar) +
    (intervalDomainLift (u s) y - uStar) *
      deriv (fun r => intervalDomainLift (v r) y) s

/-- The diagonal elliptic pairing as a time profile. -/
def intervalDomainMinimalSignalPairing
    (u v : ℝ → intervalDomainPoint → ℝ) (uStar vStar s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    intervalDomainMinimalSignalPairingIntegrand u v uStar vStar s y

/-- Genuine time derivative of the diagonal signal pairing. -/
theorem intervalDomain_minimal_signal_pairing_hasDerivAt
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (intervalDomainMinimalSignalPairing u v uStar vStar)
      (∫ y in (0 : ℝ)..1,
        intervalDomainMinimalSignalPairingTimeIntegrand
          u v uStar vStar t y) t := by
  let F : ℝ → ℝ → ℝ :=
    intervalDomainMinimalSignalPairingIntegrand u v uStar vStar
  let F' : ℝ → ℝ → ℝ :=
    intervalDomainMinimalSignalPairingTimeIntegrand u v uStar vStar
  have hU := hsol.regularity.2.2.2.2.2.2.1
  have hV := hsol.regularity.2.2.2.2.2.2.2
  have hUt := hsol.regularity.2.2.2.2.2.1.1
  have hVt := hsol.regularity.2.2.2.2.2.1.2
  have hF : ContinuousOn (Function.uncurry F)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun q : ℝ × ℝ =>
      (intervalDomainLift (u q.1) q.2 - uStar) *
        (intervalDomainLift (v q.1) q.2 - vStar)) _
    exact (hU.sub continuousOn_const).mul (hV.sub continuousOn_const)
  have hF' : ContinuousOn (Function.uncurry F')
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun r => intervalDomainLift (u r) q.2) q.1 *
          (intervalDomainLift (v q.1) q.2 - vStar) +
        (intervalDomainLift (u q.1) q.2 - uStar) *
          deriv (fun r => intervalDomainLift (v r) q.2) q.1) _
    exact (hUt.mul (hV.sub continuousOn_const)).add
      ((hU.sub continuousOn_const).mul hVt)
  have hdiff : ∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => F r y) (F' s y) s := by
    intro s hs y hy
    have hyIcc := Ioo_subset_Icc_self hy
    let x : intervalDomainPoint := ⟨y, hyIcc⟩
    have hu : HasDerivAt (fun r => intervalDomainLift (u r) y)
        (deriv (fun r => intervalDomainLift (u r) y) s) s := by
      have heq : (fun r => intervalDomainLift (u r) y) = fun r => u r x := by
        funext r
        simp [intervalDomainLift, hyIcc, x]
      rw [heq]
      exact (hsol.regularity.2.1 x s hs).1.1.hasDerivAt
    have hv : HasDerivAt (fun r => intervalDomainLift (v r) y)
        (deriv (fun r => intervalDomainLift (v r) y) s) s := by
      have heq : (fun r => intervalDomainLift (v r) y) = fun r => v r x := by
        funext r
        simp [intervalDomainLift, hyIcc, x]
      rw [heq]
      exact (hsol.regularity.2.1 x s hs).1.2.hasDerivAt
    simpa [F, F', intervalDomainMinimalSignalPairingIntegrand,
      intervalDomainMinimalSignalPairingTimeIntegrand] using
        (hu.sub_const uStar).mul (hv.sub_const vStar)
  simpa [intervalDomainMinimalSignalPairing, F, F'] using
    intervalDomain_joint_intervalIntegral_hasDerivAt ht hF hF' hdiff

/-- Self-adjointness identifies the two terms in the derivative of the
diagonal pairing. -/
theorem intervalDomain_minimal_signal_pairing_slope_eq_twice
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ y in (0 : ℝ)..1,
      intervalDomainMinimalSignalPairingTimeIntegrand
        u v uStar vStar t y) =
      2 * (∫ y in (0 : ℝ)..1,
        deriv (fun r => intervalDomainLift (u r) y) t *
          (intervalDomainLift (v t) y - vStar)) := by
  let Ut : ℝ → ℝ := fun y => intervalDomainLift (u t) y - uStar
  let Vt : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let Utime : ℝ → ℝ → ℝ :=
    fun s y => deriv (fun r => intervalDomainLift (u r) y) s
  let Vtime : ℝ → ℝ → ℝ :=
    fun s y => deriv (fun r => intervalDomainLift (v r) y) s
  let left : ℝ → ℝ → ℝ :=
    fun s y => Ut y * (intervalDomainLift (v s) y - vStar)
  let left' : ℝ → ℝ → ℝ := fun s y => Ut y * Vtime s y
  let right : ℝ → ℝ → ℝ :=
    fun s y => (intervalDomainLift (u s) y - uStar) * Vt y
  let right' : ℝ → ℝ → ℝ := fun s y => Utime s y * Vt y
  have hU := hsol.regularity.2.2.2.2.2.2.1
  have hV := hsol.regularity.2.2.2.2.2.2.2
  have hUtime := hsol.regularity.2.2.2.2.2.1.1
  have hVtime := hsol.regularity.2.2.2.2.2.1.2
  have hUtCont : ContinuousOn Ut (Icc (0 : ℝ) 1) := by
    exact (ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hU ht).sub
      continuousOn_const
  have hVtCont : ContinuousOn Vt (Icc (0 : ℝ) 1) := by
    exact (ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hV ht).sub
      continuousOn_const
  have hleft : ContinuousOn (Function.uncurry left)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    have hfixed : ContinuousOn (fun q : ℝ × ℝ => Ut q.2)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
      hUtCont.comp continuous_snd.continuousOn (fun q hq => hq.2)
    change ContinuousOn (fun q : ℝ × ℝ =>
      Ut q.2 * (intervalDomainLift (v q.1) q.2 - vStar)) _
    exact hfixed.mul (hV.sub continuousOn_const)
  have hleft' : ContinuousOn (Function.uncurry left')
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    have hfixed : ContinuousOn (fun q : ℝ × ℝ => Ut q.2)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
      hUtCont.comp continuous_snd.continuousOn (fun q hq => hq.2)
    change ContinuousOn (fun q : ℝ × ℝ =>
      Ut q.2 * deriv (fun r => intervalDomainLift (v r) q.2) q.1) _
    exact hfixed.mul hVtime
  have hright : ContinuousOn (Function.uncurry right)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    have hfixed : ContinuousOn (fun q : ℝ × ℝ => Vt q.2)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
      hVtCont.comp continuous_snd.continuousOn (fun q hq => hq.2)
    change ContinuousOn (fun q : ℝ × ℝ =>
      (intervalDomainLift (u q.1) q.2 - uStar) * Vt q.2) _
    exact (hU.sub continuousOn_const).mul hfixed
  have hright' : ContinuousOn (Function.uncurry right')
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    have hfixed : ContinuousOn (fun q : ℝ × ℝ => Vt q.2)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
      hVtCont.comp continuous_snd.continuousOn (fun q hq => hq.2)
    change ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun r => intervalDomainLift (u r) q.2) q.1 * Vt q.2) _
    exact hUtime.mul hfixed
  have hleftDiff : ∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => left r y) (left' s y) s := by
    intro s hs y hy
    have hyIcc := Ioo_subset_Icc_self hy
    let x : intervalDomainPoint := ⟨y, hyIcc⟩
    have hv : HasDerivAt (fun r => intervalDomainLift (v r) y)
        (Vtime s y) s := by
      have heq : (fun r => intervalDomainLift (v r) y) = fun r => v r x := by
        funext r
        simp [intervalDomainLift, hyIcc, x]
      have hder : Vtime s y = deriv (fun r => v r x) s := by
        dsimp [Vtime]
        rw [heq]
      rw [heq, hder]
      exact (hsol.regularity.2.1 x s hs).1.2.hasDerivAt
    simpa [left, left', Vtime] using
      (hasDerivAt_const s (Ut y)).mul (hv.sub_const vStar)
  have hrightDiff : ∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => right r y) (right' s y) s := by
    intro s hs y hy
    have hyIcc := Ioo_subset_Icc_self hy
    let x : intervalDomainPoint := ⟨y, hyIcc⟩
    have hu : HasDerivAt (fun r => intervalDomainLift (u r) y)
        (Utime s y) s := by
      have heq : (fun r => intervalDomainLift (u r) y) = fun r => u r x := by
        funext r
        simp [intervalDomainLift, hyIcc, x]
      have hder : Utime s y = deriv (fun r => u r x) s := by
        dsimp [Utime]
        rw [heq]
      rw [heq, hder]
      exact (hsol.regularity.2.1 x s hs).1.1.hasDerivAt
    simpa [right, right', Utime] using
      (hu.sub_const uStar).mul (hasDerivAt_const s (Vt y))
  have hleftDeriv := intervalDomain_joint_intervalIntegral_hasDerivAt
    ht hleft hleft' hleftDiff
  have hrightDeriv := intervalDomain_joint_intervalIntegral_hasDerivAt
    ht hright hright' hrightDiff
  have hfun :
      (fun s => ∫ y in (0 : ℝ)..1, left s y) =ᶠ[𝓝 t]
        fun s => ∫ y in (0 : ℝ)..1, right s y := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simpa [left, right, Ut, Vt] using
      intervalDomain_minimal_signal_pairing_comm
        hgamma heq hsol hs ht
  have hslopeEq :
      (∫ y in (0 : ℝ)..1, left' t y) =
        ∫ y in (0 : ℝ)..1, right' t y := by
    have := hfun.deriv_eq
    rw [hleftDeriv.deriv, hrightDeriv.deriv] at this
    exact this
  have hsum :
      (∫ y in (0 : ℝ)..1,
        intervalDomainMinimalSignalPairingTimeIntegrand
          u v uStar vStar t y) =
        (∫ y in (0 : ℝ)..1, right' t y) +
          ∫ y in (0 : ℝ)..1, left' t y := by
    have hrightInt : IntervalIntegrable (right' t) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      exact ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hright' ht
    have hleftInt : IntervalIntegrable (left' t) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      exact ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hleft' ht
    rw [← intervalIntegral.integral_add hrightInt hleftInt]
    apply intervalIntegral.integral_congr
    intro y _
    rfl
  rw [hsum, hslopeEq]
  dsimp [right', Utime, Vt]
  ring

/-- Concrete signal-energy derivative identity for Theorem 2.5(ii), obtained
without assuming a signal-energy derivative interface. -/
theorem intervalDomain_minimal_signal_energy_hasDerivAt
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => chemotaxisSignalEnergy intervalDomain p.μ vStar v s)
      (2 * p.ν * (∫ y in (0 : ℝ)..1,
        deriv (fun r => intervalDomainLift (u r) y) t *
          (intervalDomainLift (v t) y - vStar))) t := by
  have hpair := intervalDomain_minimal_signal_pairing_hasDerivAt
    (uStar := uStar) (vStar := vStar) hsol ht
  have hslope := intervalDomain_minimal_signal_pairing_slope_eq_twice
    hgamma heq hsol ht
  have hscaled := hpair.const_mul p.ν
  have hlocal :
      (fun s => chemotaxisSignalEnergy intervalDomain p.μ vStar v s) =ᶠ[𝓝 t]
        fun s => p.ν * intervalDomainMinimalSignalPairing
          u v uStar vStar s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simpa [intervalDomainMinimalSignalPairing,
      intervalDomainMinimalSignalPairingIntegrand] using
        intervalDomain_chemotaxisSignalEnergy_eq_pairing
          hgamma heq hsol hs
  apply hlocal.hasDerivAt_iff.2
  convert hscaled using 1
  rw [hslope]
  ring

#print axioms intervalDomain_minimal_signal_pairing_comm
#print axioms intervalDomain_chemotaxisSignalEnergy_eq_pairing
#print axioms intervalDomain_joint_intervalIntegral_hasDerivAt
#print axioms intervalDomain_minimal_signal_energy_hasDerivAt

end

end ShenWork.Paper3
