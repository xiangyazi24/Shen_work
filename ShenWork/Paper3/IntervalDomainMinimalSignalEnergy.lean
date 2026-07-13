import ShenWork.Paper3.EventualExponentialStability
import ShenWork.Paper3.EventualGlobalStability
import ShenWork.Paper3.IntervalDomainEntropyBasinEntry
import ShenWork.Paper3.LyapunovFunction
import ShenWork.Paper3.IntervalDomainMinimalPoincare
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit
import ShenWork.Paper3.IntervalDomainEntropyStrong2Dynamics
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz
import ShenWork.Paper2.IntervalDomainProposition21
import ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer

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
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalFullKernelRegularity
open ShenWork.Poincare
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

/-- The squared signal Laplacian is integrable on a classical `γ = 1` slice;
the elliptic equation represents it by continuous zeroth-order fields. -/
theorem intervalDomain_minimal_signal_lap_sq_intervalIntegrable
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    IntervalIntegrable
      (fun y =>
        (deriv (fun z => deriv (intervalDomainLift (v t)) z) y) ^ 2)
      volume 0 1 := by
  let U : ℝ → ℝ := fun y => intervalDomainLift (u t) y - uStar
  let W : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let Lap : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y
  have hUCont : ContinuousOn U (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hWCont : ContinuousOn W (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
      continuousOn_const
  have hrepCont : ContinuousOn
      (fun y => p.μ * W y - p.ν * U y) (uIcc (0 : ℝ) 1) :=
    (hWCont.const_mul p.μ).sub (hUCont.const_mul p.ν)
  have hrepSqInt : IntervalIntegrable
      (fun y => (p.μ * W y - p.ν * U y) ^ 2) volume 0 1 :=
    (hrepCont.pow 2).intervalIntegrable
  have hLapSqInt : IntervalIntegrable (fun y => (Lap y) ^ 2) volume 0 1 := by
    refine hrepSqInt.congr_ae ?_
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
    have hdiff := intervalDomain_minimal_elliptic_difference
      hgamma heq hsol ht ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
    apply hne
    dsimp [U, W, Lap]
    have hrearranged :
        p.μ * (intervalDomainLift (v t) y - vStar) -
            p.ν * (intervalDomainLift (u t) y - uStar) =
          deriv (fun z => deriv (intervalDomainLift (v t)) z) y := by
      linarith
    rw [hrearranged]
  simpa [Lap] using hLapSqInt

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

/-! ## PDE dissipation identity -/

/-- Pointwise minimal-model parabolic equation in lifted coordinates. -/
theorem intervalDomain_minimal_u_timeDeriv_pde
    {p : CM2Params} {T t y : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (hy : y ∈ Ioo (0 : ℝ) 1) :
    deriv (fun r => intervalDomainLift (u r) y) t =
      deriv (fun z => deriv (intervalDomainLift (u t)) z) y -
        p.χ₀ * deriv (intervalFlux p (u t) (v t)) y := by
  let x : intervalDomainPoint := ⟨y, Ioo_subset_Icc_self hy⟩
  have htime :
      deriv (fun r => intervalDomainLift (u r) y) t =
        intervalDomain.timeDeriv u t x := by
    have heq : (fun r => intervalDomainLift (u r) y) = fun r => u r x := by
      funext r
      simp [intervalDomainLift, x, Ioo_subset_Icc_self hy]
    rw [heq]
    rfl
  have hpde := hsol.pde_u ht.1 ht.2 (x := x) hy
  rw [htime, hpde]
  change
    intervalDomainLaplacian (u t) x -
      p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x +
        u t x * (p.a - p.b * (u t x) ^ p.α) = _
  simp only [intervalDomainLaplacian, intervalDomainChemotaxisDiv]
  have hu : u t x = intervalDomainLift (u t) y := by
    simp [intervalDomainLift, x, Ioo_subset_Icc_self hy]
  rw [hu, ha0, hb0]
  dsimp [x]
  have hfluxeq :
      (fun yy : ℝ => intervalDomainLift (u t) yy *
        deriv (intervalDomainLift (v t)) yy /
          (1 + intervalDomainLift (v t) yy) ^ p.β) =
        intervalFlux p (u t) (v t) := rfl
  rw [hfluxeq]
  ring

/-- Cross integration by parts between the signal difference and the
parabolic Laplacian. -/
theorem intervalDomain_minimal_signal_u_lap_cross_ibp
    {p : CM2Params} {T t vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (v t) y - vStar) *
          deriv (fun z => deriv (intervalDomainLift (u t)) z) y) =
      -∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (v t)) y *
          deriv (intervalDomainLift (u t)) y := by
  let phi : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let phi' : ℝ → ℝ := fun y => deriv (intervalDomainLift (v t)) y
  let F : ℝ → ℝ := fun y => deriv (intervalDomainLift (u t)) y
  let F' : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (u t)) z) y
  have hphiCont : ContinuousOn phi (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
      continuousOn_const
  have hFCont : ContinuousOn F (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le zero_le_one, F] using
      solution_deriv_lift_continuousOn_Icc hsol ht
  have hphi : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt phi (phi' y) y := by
    intro y hy
    simpa [phi, phi'] using
      (intervalDomain_solution_v_lift_hasDerivAt_interior hsol ht hy).1.sub_const vStar
  have hF : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' y) y := by
    intro y hy
    simpa [F, F'] using (lift_hasDerivAt_interior hsol ht hy).2
  have hphiInt : IntervalIntegrable phi' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one, phi'] using
      intervalDomain_solution_v_deriv_lift_continuousOn_Icc hsol ht
  have hFInt : IntervalIntegrable F' volume 0 1 := by
    simpa [F'] using solution_lap_lift_intervalIntegrable hsol ht
  have hzero := (hsol.regularity.2.2.2.2.1 t ht).1
  simpa [phi, phi', F, F'] using
    intervalFluxByParts_open hphiCont hFCont hphi hF hphiInt hFInt
      hzero.2.1 hzero.2.2

/-- Cross integration by parts for the chemotaxis divergence. -/
theorem intervalDomain_minimal_signal_flux_cross_ibp
    {p : CM2Params} {T t vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (v t) y - vStar) *
          deriv (intervalFlux p (u t) (v t)) y) =
      -∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (v t)) y *
          intervalFlux p (u t) (v t) y := by
  let phi : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let phi' : ℝ → ℝ := fun y => deriv (intervalDomainLift (v t)) y
  let F : ℝ → ℝ := intervalFlux p (u t) (v t)
  let F' : ℝ → ℝ := fun y => deriv F y
  have hphiCont : ContinuousOn phi (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
      continuousOn_const
  have hFCont : ContinuousOn F (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (flux_contDiffOn_Icc hsol ht).continuousOn
  have hphi : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt phi (phi' y) y := by
    intro y hy
    simpa [phi, phi'] using
      (intervalDomain_solution_v_lift_hasDerivAt_interior hsol ht hy).1.sub_const vStar
  have hF : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' y) y := by
    intro y hy
    exact (((flux_contDiffOn_Ioo_of_solution hsol ht).differentiableOn
      (by norm_num)).differentiableAt
        (IsOpen.mem_nhds isOpen_Ioo hy)).hasDerivAt
  have hphiInt : IntervalIntegrable phi' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one, phi'] using
      intervalDomain_solution_v_deriv_lift_continuousOn_Icc hsol ht
  have hFInt : IntervalIntegrable F' volume 0 1 := by
    simpa [F, F'] using solution_deriv_flux_intervalIntegrable hsol ht
  have hzero := flux_endpoint_zero hsol ht
  simpa [phi, phi', F, F'] using
    intervalFluxByParts_open hphiCont hFCont hphi hF hphiInt hFInt
      hzero.1 hzero.2

/-- Testing the minimal parabolic equation against `v-vStar`. -/
theorem intervalDomain_minimal_signal_ut_pairing_pde
    {p : CM2Params} {T t vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ y in (0 : ℝ)..1,
        deriv (fun r => intervalDomainLift (u r) y) t *
          (intervalDomainLift (v t) y - vStar)) =
      -(∫ y in (0 : ℝ)..1,
          deriv (intervalDomainLift (u t)) y *
            deriv (intervalDomainLift (v t)) y) +
        p.χ₀ * (∫ y in (0 : ℝ)..1,
          intervalDomainLift (u t) y *
            (deriv (intervalDomainLift (v t)) y) ^ 2 /
              (1 + intervalDomainLift (v t) y) ^ p.β) := by
  let Ut : ℝ → ℝ :=
    fun y => deriv (fun r => intervalDomainLift (u r) y) t
  let W : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let Lap : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (u t)) z) y
  let Fd : ℝ → ℝ := fun y => deriv (intervalFlux p (u t) (v t)) y
  have hUtCont : ContinuousOn Ut (Icc (0 : ℝ) 1) := by
    simpa [Ut] using ShenWork.Paper2.intervalDomain_continuousOn_timeSlice
      hsol.regularity.2.2.2.2.2.1.1 ht
  have hWCont : ContinuousOn W (Icc (0 : ℝ) 1) := by
    exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
      continuousOn_const
  have hWContU : ContinuousOn W (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le zero_le_one] using hWCont
  have hLapInt : IntervalIntegrable Lap volume 0 1 := by
    simpa [Lap] using solution_lap_lift_intervalIntegrable hsol ht
  have hFdInt : IntervalIntegrable Fd volume 0 1 := by
    simpa [Fd] using solution_deriv_flux_intervalIntegrable hsol ht
  have hUtWInt : IntervalIntegrable (fun y => Ut y * W y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hUtCont.mul hWCont
  have hWLapInt : IntervalIntegrable (fun y => W y * Lap y) volume 0 1 :=
    hLapInt.continuousOn_mul hWContU
  have hWFdInt : IntervalIntegrable (fun y => W y * Fd y) volume 0 1 :=
    hFdInt.continuousOn_mul hWContU
  have hpoint : EqOn (fun y => Ut y * W y)
      (fun y => W y * Lap y - p.χ₀ * (W y * Fd y))
      (Ioo (0 : ℝ) 1) := by
    intro y hy
    have h := intervalDomain_minimal_u_timeDeriv_pde
      ha0 hb0 hsol ht hy
    dsimp [Ut, W, Lap, Fd]
    rw [h]
    ring
  have hintegral :
      (∫ y in (0 : ℝ)..1, Ut y * W y) =
        (∫ y in (0 : ℝ)..1, W y * Lap y) -
          p.χ₀ * (∫ y in (0 : ℝ)..1, W y * Fd y) := by
    calc
      (∫ y in (0 : ℝ)..1, Ut y * W y) =
          ∫ y in (0 : ℝ)..1,
            W y * Lap y - p.χ₀ * (W y * Fd y) := by
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
      _ = (∫ y in (0 : ℝ)..1, W y * Lap y) -
          ∫ y in (0 : ℝ)..1, p.χ₀ * (W y * Fd y) := by
        rw [intervalIntegral.integral_sub hWLapInt (hWFdInt.const_mul p.χ₀)]
      _ = (∫ y in (0 : ℝ)..1, W y * Lap y) -
          p.χ₀ * (∫ y in (0 : ℝ)..1, W y * Fd y) := by
        rw [intervalIntegral.integral_const_mul]
  have hlap := intervalDomain_minimal_signal_u_lap_cross_ibp
    (vStar := vStar) hsol ht
  have hflux := intervalDomain_minimal_signal_flux_cross_ibp
    (vStar := vStar) hsol ht
  have hchem :
      (∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (v t)) y *
          intervalFlux p (u t) (v t) y) =
        ∫ y in (0 : ℝ)..1,
          intervalDomainLift (u t) y *
            (deriv (intervalDomainLift (v t)) y) ^ 2 /
              (1 + intervalDomainLift (v t) y) ^ p.β := by
    apply intervalIntegral.integral_congr
    intro y _
    unfold intervalFlux
    ring
  rw [hlap, hflux, hchem] at hintegral
  dsimp [Ut, W, Lap, Fd] at hintegral
  have hgradComm :
      (∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (v t)) y *
          deriv (intervalDomainLift (u t)) y) =
        ∫ y in (0 : ℝ)..1,
          deriv (intervalDomainLift (u t)) y *
            deriv (intervalDomainLift (v t)) y := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [hgradComm] at hintegral
  linarith

/-- Cross integration by parts between the population difference and the
signal Laplacian. -/
theorem intervalDomain_minimal_u_signal_lap_cross_ibp
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y - uStar) *
          deriv (fun z => deriv (intervalDomainLift (v t)) z) y) =
      -∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (u t)) y *
          deriv (intervalDomainLift (v t)) y := by
  let phi : ℝ → ℝ := fun y => intervalDomainLift (u t) y - uStar
  let phi' : ℝ → ℝ := fun y => deriv (intervalDomainLift (u t)) y
  let F : ℝ → ℝ := fun y => deriv (intervalDomainLift (v t)) y
  let F' : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y
  have hphiCont : ContinuousOn phi (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hFCont : ContinuousOn F (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le zero_le_one, F] using
      intervalDomain_solution_v_deriv_lift_continuousOn_Icc hsol ht
  have hphi : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt phi (phi' y) y := by
    intro y hy
    simpa [phi, phi'] using
      (lift_hasDerivAt_interior hsol ht hy).1.sub_const uStar
  have hF : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' y) y := by
    intro y hy
    simpa [F, F'] using
      (intervalDomain_solution_v_lift_hasDerivAt_interior hsol ht hy).2
  have hphiInt : IntervalIntegrable phi' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one, phi'] using
      solution_deriv_lift_continuousOn_Icc hsol ht
  have hFInt : IntervalIntegrable F' volume 0 1 := by
    simpa [F'] using intervalDomain_solution_v_lap_lift_intervalIntegrable hsol ht
  have hzero := (hsol.regularity.2.2.2.2.1 t ht).2
  simpa [phi, phi', F, F'] using
    intervalFluxByParts_open hphiCont hFCont hphi hF hphiInt hFInt
      hzero.2.1 hzero.2.2

/-- The `γ = 1` elliptic equation converts the population--signal gradient
pairing into the two coercive signal terms. -/
theorem intervalDomain_minimal_signal_diffusion_pairing
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    -p.ν * (∫ y in (0 : ℝ)..1,
        deriv (intervalDomainLift (u t)) y *
          deriv (intervalDomainLift (v t)) y) =
      -(∫ y in (0 : ℝ)..1,
          (deriv (fun z => deriv (intervalDomainLift (v t)) z) y) ^ 2) -
        p.μ * (∫ y in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) y) ^ 2) := by
  let U : ℝ → ℝ := fun y => intervalDomainLift (u t) y - uStar
  let W : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let Lap : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y
  have hUCont : ContinuousOn U (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hWCont : ContinuousOn W (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
      continuousOn_const
  have hLapInt : IntervalIntegrable Lap volume 0 1 := by
    simpa [Lap] using intervalDomain_solution_v_lap_lift_intervalIntegrable hsol ht
  have hULapInt : IntervalIntegrable (fun y => U y * Lap y) volume 0 1 := by
    simpa [mul_comm] using hLapInt.continuousOn_mul hUCont
  have hWLapInt : IntervalIntegrable (fun y => W y * Lap y) volume 0 1 := by
    simpa [mul_comm] using hLapInt.continuousOn_mul hWCont
  have hLapSqInt : IntervalIntegrable (fun y => (Lap y) ^ 2) volume 0 1 := by
    simpa [Lap] using intervalDomain_minimal_signal_lap_sq_intervalIntegrable
      hgamma heq hsol ht
  have hpoint : EqOn (fun y => p.ν * (U y * Lap y))
      (fun y => p.μ * (W y * Lap y) - (Lap y) ^ 2)
      (Ioo (0 : ℝ) 1) := by
    intro y hy
    have hdiff := intervalDomain_minimal_elliptic_difference
      hgamma heq hsol ht hy
    calc
      p.ν * (U y * Lap y) = (p.ν * U y) * Lap y := by ring
      _ = (p.μ * W y - Lap y) * Lap y := by rw [hdiff]
      _ = p.μ * (W y * Lap y) - (Lap y) ^ 2 := by ring
  have hscaled :
      p.ν * (∫ y in (0 : ℝ)..1, U y * Lap y) =
        p.μ * (∫ y in (0 : ℝ)..1, W y * Lap y) -
          ∫ y in (0 : ℝ)..1, (Lap y) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
        (hWLapInt.const_mul p.μ) hLapSqInt]
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
  have huCross := intervalDomain_minimal_u_signal_lap_cross_ibp
    (uStar := uStar) hsol ht
  have hvCross := intervalDomain_minimal_signal_cross_ibp
    (vStar := vStar) hsol ht ht
  rw [huCross, hvCross] at hscaled
  dsimp [U, W, Lap] at hscaled
  ring_nf at hscaled ⊢
  linarith

/-- Exact signal-energy dissipation identity for the minimal `γ = 1` model. -/
theorem intervalDomain_minimal_signal_energy_hasDerivAt_pde
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => chemotaxisSignalEnergy intervalDomain p.μ vStar v s)
      (-2 * (∫ y in (0 : ℝ)..1,
          (deriv (fun z => deriv (intervalDomainLift (v t)) z) y) ^ 2) -
        2 * p.μ * (∫ y in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) y) ^ 2) +
        2 * p.ν * p.χ₀ * (∫ y in (0 : ℝ)..1,
          intervalDomainLift (u t) y *
            (deriv (intervalDomainLift (v t)) y) ^ 2 /
              (1 + intervalDomainLift (v t) y) ^ p.β)) t := by
  have henergy := intervalDomain_minimal_signal_energy_hasDerivAt
    hgamma heq hsol ht
  have hut := intervalDomain_minimal_signal_ut_pairing_pde
    (vStar := vStar) ha0 hb0 hsol ht
  have hdiff := intervalDomain_minimal_signal_diffusion_pairing
    hgamma heq hsol ht
  convert henergy using 1
  rw [hut]
  ring_nf at hdiff ⊢
  linarith

/-! ## Eventual-box absorption -/

/-- The strict gradient coefficient left after absorbing the chemotaxis term
in the second minimal formula branch. -/
def minimal2SignalCoefficient
    (p : CM2Params) (uBar vLower : ℝ) : ℝ :=
  p.μ - p.ν * p.χ₀ * uBar / (1 + vLower) ^ p.β

/-- The literal second threshold in Theorem 2.5 leaves a positive signal
gradient coefficient. -/
theorem minimal2SignalCoefficient_pos
    (p : CM2Params) {uBar vLower : ℝ}
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hchi : p.χ₀ < chiMinimal2Formula p uBar vLower) :
    0 < minimal2SignalCoefficient p uBar vLower := by
  let B : ℝ := (1 + vLower) ^ p.β
  have hB : 0 < B := by
    exact Real.rpow_pos_of_pos (by linarith) _
  have hden : 0 < p.ν * uBar := mul_pos p.hν huBar
  have hthird : p.χ₀ < p.μ * B / (p.ν * uBar) := by
    exact hchi.trans_le (by
      unfold chiMinimal2Formula
      exact min_le_right _ _)
  have hmul : p.χ₀ * (p.ν * uBar) < p.μ * B :=
    (lt_div_iff₀ hden).1 hthird
  have hnum : p.ν * p.χ₀ * uBar < p.μ * B := by
    nlinarith
  have hquot : p.ν * p.χ₀ * uBar / B < p.μ :=
    (div_lt_iff₀ hB).2 (by simpa [mul_comm] using hnum)
  simpa [minimal2SignalCoefficient, B] using sub_pos.mpr hquot

/-- On one classical slice in the eventual box, the chemotaxis integral is
bounded by the constant box ratio times the signal-gradient energy. -/
theorem intervalDomain_minimal_signal_chemotaxis_integral_le
    {p : CM2Params} {T t uBar vLower : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hbeta : 1 ≤ p.β) (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hupper : ∀ x : intervalDomainPoint, u t x ≤ uBar)
    (hfloor : ∀ x : intervalDomainPoint, vLower ≤ v t x) :
    (∫ y in (0 : ℝ)..1,
        intervalDomainLift (u t) y *
          (deriv (intervalDomainLift (v t)) y) ^ 2 /
            (1 + intervalDomainLift (v t) y) ^ p.β) ≤
      (uBar / (1 + vLower) ^ p.β) *
        (∫ y in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) y) ^ 2) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let Vx : ℝ → ℝ := deriv V
  let B : ℝ := (1 + vLower) ^ p.β
  have hUCont : ContinuousOn U (Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hVCont : ContinuousOn V (Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hVxCont : ContinuousOn Vx (Icc (0 : ℝ) 1) := by
    simpa [V, Vx] using
      intervalDomain_solution_v_deriv_lift_continuousOn_Icc hsol ht
  have hbasePos : ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + V y := by
    intro y hy
    have hv : 0 ≤ V y := by
      simpa [V, intervalDomainLift, hy] using
        hsol.v_nonneg (x := (⟨y, hy⟩ : intervalDomainPoint)) ht.1 ht.2
    linarith
  have hdenCont : ContinuousOn (fun y => (1 + V y) ^ p.β)
      (Icc (0 : ℝ) 1) :=
    (continuousOn_const.add hVCont).rpow_const
      (fun y hy => Or.inl (ne_of_gt (hbasePos y hy)))
  have hleftCont : ContinuousOn
      (fun y => U y * (Vx y) ^ 2 / (1 + V y) ^ p.β)
      (Icc (0 : ℝ) 1) :=
    (hUCont.mul (hVxCont.pow 2)).div hdenCont
      (fun y hy => ne_of_gt (Real.rpow_pos_of_pos (hbasePos y hy) _))
  have hrightCont : ContinuousOn
      (fun y => (uBar / B) * (Vx y) ^ 2) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (hVxCont.pow 2)
  have hleftInt : IntervalIntegrable
      (fun y => U y * (Vx y) ^ 2 / (1 + V y) ^ p.β)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hleftCont
  have hrightInt : IntervalIntegrable
      (fun y => (uBar / B) * (Vx y) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hrightCont
  have hBPos : 0 < B := Real.rpow_pos_of_pos (by linarith) _
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1,
      U y * (Vx y) ^ 2 / (1 + V y) ^ p.β ≤
        (uBar / B) * (Vx y) ^ 2 := by
    intro y hy
    have hUPos : 0 < U y := by
      simpa [U, intervalDomainLift, hy] using
        hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomainPoint)) ht.1 ht.2
    have hUUpper : U y ≤ uBar := by
      simpa [U, intervalDomainLift, hy] using
        hupper (⟨y, hy⟩ : intervalDomainPoint)
    have hVFloor : vLower ≤ V y := by
      simpa [V, intervalDomainLift, hy] using
        hfloor (⟨y, hy⟩ : intervalDomainPoint)
    have hbaseLe : 1 + vLower ≤ 1 + V y := by linarith
    have hdenLe : B ≤ (1 + V y) ^ p.β := by
      exact Real.rpow_le_rpow (by linarith) hbaseLe (by linarith)
    have hratio : U y / (1 + V y) ^ p.β ≤ uBar / B :=
      div_le_div₀ huBar.le hUUpper hBPos hdenLe
    calc
      U y * (Vx y) ^ 2 / (1 + V y) ^ p.β =
          (U y / (1 + V y) ^ p.β) * (Vx y) ^ 2 := by ring
      _ ≤ (uBar / B) * (Vx y) ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) hleftInt hrightInt hpoint
  dsimp [U, V, Vx, B] at hmono ⊢
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- Eventual-box absorption turns the exact PDE identity into a coercive
signal-energy slope estimate. -/
theorem intervalDomain_minimal_signal_energy_slope_le
    {p : CM2Params} {T t uStar vStar uBar vLower : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hbeta : 1 ≤ p.β) (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hchi : 0 < p.χ₀)
    (hupper : ∀ x : intervalDomainPoint, u t x ≤ uBar)
    (hfloor : ∀ x : intervalDomainPoint, vLower ≤ v t x) :
    deriv (fun s => chemotaxisSignalEnergy intervalDomain p.μ vStar v s) t ≤
      -2 * (∫ y in (0 : ℝ)..1,
          (deriv (fun z => deriv (intervalDomainLift (v t)) z) y) ^ 2) -
        2 * minimal2SignalCoefficient p uBar vLower *
          (∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2) := by
  have hder := intervalDomain_minimal_signal_energy_hasDerivAt_pde
    ha0 hb0 hgamma heq hsol ht
  have hchem := intervalDomain_minimal_signal_chemotaxis_integral_le
    hsol ht hbeta huBar hvLower hupper hfloor
  have hscale : 0 ≤ 2 * p.ν * p.χ₀ := by
    exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le) hchi.le
  have hscaled := mul_le_mul_of_nonneg_left hchem hscale
  rw [hder.deriv]
  unfold minimal2SignalCoefficient
  ring_nf at hscaled ⊢
  linarith

/-! ## Poincare control and exponential signal decay -/

/-- At `γ = 1`, conserved population mass and the integrated elliptic
equation force the signal perturbation to have zero mean. -/
theorem intervalDomain_minimal_signal_mean_zero
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hmass : intervalDomain.integral (u t) = uStar) :
    (∫ y in (0 : ℝ)..1,
        intervalDomainLift (v t) y - vStar) = 0 := by
  have hchem := intervalDomain_chemical_mass_identity hsol ht.1 ht.2
  have hchem' :
      p.μ * (∫ y in (0 : ℝ)..1, intervalDomainLift (v t) y) =
        p.ν * (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y) := by
    simpa [hgamma] using hchem
  have hmassLift :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y) = uStar := by
    simpa [intervalDomain, intervalDomainIntegral] using hmass
  rw [hmassLift] at hchem'
  have heqRel : p.μ * vStar = p.ν * uStar := by
    simpa [hgamma] using heq.elliptic_relation
  have hvMean :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (v t) y) = vStar := by
    nlinarith [p.hμ, hchem']
  have hVInt : IntervalIntegrable (intervalDomainLift (v t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using
      (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  rw [intervalIntegral.integral_sub hVInt intervalIntegrable_const,
    hvMean, intervalIntegral.integral_const]
  norm_num [smul_eq_mul]

/-- Coarse unit-interval Poincare control for the `γ = 1` signal
perturbation with conserved equilibrium mass. -/
theorem intervalDomain_minimal_signal_poincare
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1) (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hmass : intervalDomain.integral (u t) = uStar) :
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (v t) y - vStar) ^ 2) ≤
      ∫ y in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) y) ^ 2 := by
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let F : ℝ → ℝ := liftRepr (v t)
  let Vx : ℝ → ℝ := deriv V
  have hV2 : ContDiffOn ℝ 2 V (Icc (0 : ℝ) 1) := by
    simpa [V] using (hsolM.regularity.2.2.2.2.1 t ht).2.1
  have hneu0 : derivWithin V (Icc (0 : ℝ) 1) 0 = 0 := by
    simpa [V] using derivWithin_left_zero hsolM ht.1 ht.2 v (Or.inr rfl)
  have hneu1 : derivWithin V (Icc (0 : ℝ) 1) 1 = 0 := by
    simpa [V] using derivWithin_right_zero hsolM ht.1 ht.2 v (Or.inr rfl)
  have hVx1 : ContDiffOn ℝ 1 Vx (Icc (0 : ℝ) 1) := by
    simpa [V, Vx] using deriv_lift_contDiffOn_one_Icc hV2 hneu0 hneu1
  have hFCont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    (liftRepr_continuous hV2.continuousOn).continuousOn
  have hFDeriv : ∀ y ∈ Icc (0 : ℝ) 1, HasDerivAt F (Vx y) y := by
    intro y hy
    simpa [F, V, Vx] using
      liftRepr_hasDerivAt_Icc_of_neumann hV2 hneu0 hneu1 y hy
  have hVxInt : IntervalIntegrable Vx volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hVx1.continuousOn
  have hVxSqInt : IntervalIntegrable (fun y => (Vx y) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hVx1.continuousOn.pow 2
  have hp := poincare_unit_interval_coarse
    hFCont hFDeriv hVxInt hVxSqInt
  have hmeanZero := intervalDomain_minimal_signal_mean_zero
    hgamma heq hsol ht hmass
  have hmean : (∫ y in (0 : ℝ)..1, F y) = vStar := by
    have hVInt : IntervalIntegrable V volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le zero_le_one, V] using
        (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
    have hdiff :
        (∫ y in (0 : ℝ)..1, V y - vStar) =
          (∫ y in (0 : ℝ)..1, V y) - vStar := by
      rw [intervalIntegral.integral_sub hVInt intervalIntegrable_const,
        intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    have hVMean : (∫ y in (0 : ℝ)..1, V y) = vStar := by
      rw [hdiff] at hmeanZero
      linarith
    calc
      (∫ y in (0 : ℝ)..1, F y) = ∫ y in (0 : ℝ)..1, V y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le zero_le_one] at hy
        exact liftRepr_eq_on_Icc hy
      _ = vStar := hVMean
  calc
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (v t) y - vStar) ^ 2) =
        ∫ y in (0 : ℝ)..1, (F y - vStar) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le zero_le_one] at hy
      change (V y - vStar) ^ 2 = (F y - vStar) ^ 2
      rw [show F y = V y by exact liftRepr_eq_on_Icc hy]
    _ ≤ ∫ y in (0 : ℝ)..1, (Vx y) ^ 2 := by
      simpa [hmean] using hp
    _ = ∫ y in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) y) ^ 2 := by rfl

/-- Raw interval representation of the signal energy on a `γ = 1` slice. -/
theorem intervalDomain_minimal_signal_energy_eq_raw
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    chemotaxisSignalEnergy intervalDomain p.μ vStar v t =
      p.μ * (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (v t) y - vStar) ^ 2) +
        ∫ y in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) y) ^ 2 := by
  have hpair := intervalDomain_chemotaxisSignalEnergy_eq_pairing
    hgamma heq hsol ht
  have helliptic := intervalDomain_minimal_signal_pairing_scaled
    hgamma heq hsol ht ht
  calc
    chemotaxisSignalEnergy intervalDomain p.μ vStar v t =
        p.ν * (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (u t) y - uStar) *
            (intervalDomainLift (v t) y - vStar)) := hpair
    _ = p.μ * (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (v t) y - vStar) *
            (intervalDomainLift (v t) y - vStar)) +
          ∫ y in (0 : ℝ)..1,
            deriv (intervalDomainLift (v t)) y *
              deriv (intervalDomainLift (v t)) y := helliptic
    _ = p.μ * (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (v t) y - vStar) ^ 2) +
          ∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2 := by
      have hvalue :
          (∫ y in (0 : ℝ)..1,
            (intervalDomainLift (v t) y - vStar) *
              (intervalDomainLift (v t) y - vStar)) =
            ∫ y in (0 : ℝ)..1,
              (intervalDomainLift (v t) y - vStar) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      have hgradient :
          (∫ y in (0 : ℝ)..1,
            deriv (intervalDomainLift (v t)) y *
              deriv (intervalDomainLift (v t)) y) =
            ∫ y in (0 : ℝ)..1,
              (deriv (intervalDomainLift (v t)) y) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      rw [hvalue, hgradient]

/-- The `γ = 1` elliptic equation controls the population `L²` distance by
the signal energy and the squared signal Laplacian. -/
theorem intervalDomain_minimal_signal_elliptic_l2
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    p.ν ^ 2 * (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y - uStar) ^ 2) ≤
      2 * p.μ * chemotaxisSignalEnergy intervalDomain p.μ vStar v t +
        2 * (∫ y in (0 : ℝ)..1,
          (deriv (fun z => deriv (intervalDomainLift (v t)) z) y) ^ 2) := by
  let U : ℝ → ℝ := fun y => intervalDomainLift (u t) y - uStar
  let W : ℝ → ℝ := fun y => intervalDomainLift (v t) y - vStar
  let Lap : ℝ → ℝ :=
    fun y => deriv (fun z => deriv (intervalDomainLift (v t)) z) y
  have hUCont : ContinuousOn U (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hWCont : ContinuousOn W (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn).sub
      continuousOn_const
  have hU2Int : IntervalIntegrable (fun y => (U y) ^ 2) volume 0 1 :=
    (hUCont.pow 2).intervalIntegrable
  have hW2Int : IntervalIntegrable (fun y => (W y) ^ 2) volume 0 1 :=
    (hWCont.pow 2).intervalIntegrable
  have hLap2Int : IntervalIntegrable (fun y => (Lap y) ^ 2) volume 0 1 := by
    simpa [Lap] using intervalDomain_minimal_signal_lap_sq_intervalIntegrable
      hgamma heq hsol ht
  have hleftInt : IntervalIntegrable
      (fun y => (p.ν * U y) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuousOn_const.mul hUCont).pow 2)
  have hWTermInt : IntervalIntegrable
      (fun y => 2 * (p.μ * W y) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul ((continuousOn_const.mul hWCont).pow 2)
  have hrightInt : IntervalIntegrable
      (fun y => 2 * (p.μ * W y) ^ 2 + 2 * (Lap y) ^ 2)
      volume 0 1 :=
    hWTermInt.add (hLap2Int.const_mul 2)
  have hae : (fun y => (p.ν * U y) ^ 2) ≤ᵐ[
      volume.restrict (Icc (0 : ℝ) 1)]
      (fun y => 2 * (p.μ * W y) ^ 2 + 2 * (Lap y) ^ 2) := by
    have hrestrict : volume.restrict (Icc (0 : ℝ) 1) =
        volume.restrict (Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hrestrict]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hdiff := intervalDomain_minimal_elliptic_difference
      hgamma heq hsol ht hy
    change p.ν * U y = p.μ * W y - Lap y at hdiff
    rw [hdiff]
    nlinarith [sq_nonneg (p.μ * W y + Lap y)]
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (by norm_num : (0 : ℝ) ≤ 1) hleftInt hrightInt hae
  have hleftEq :
      (∫ y in (0 : ℝ)..1, (p.ν * U y) ^ 2) =
        p.ν ^ 2 * (∫ y in (0 : ℝ)..1, (U y) ^ 2) := by
    calc
      (∫ y in (0 : ℝ)..1, (p.ν * U y) ^ 2) =
          ∫ y in (0 : ℝ)..1, p.ν ^ 2 * (U y) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      _ = p.ν ^ 2 * (∫ y in (0 : ℝ)..1, (U y) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
  have hrightEq :
      (∫ y in (0 : ℝ)..1,
        2 * (p.μ * W y) ^ 2 + 2 * (Lap y) ^ 2) =
        2 * p.μ ^ 2 * (∫ y in (0 : ℝ)..1, (W y) ^ 2) +
          2 * (∫ y in (0 : ℝ)..1, (Lap y) ^ 2) := by
    rw [intervalIntegral.integral_add hWTermInt (hLap2Int.const_mul 2),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have hmu :
        (∫ y in (0 : ℝ)..1, (p.μ * W y) ^ 2) =
          p.μ ^ 2 * (∫ y in (0 : ℝ)..1, (W y) ^ 2) := by
      calc
        (∫ y in (0 : ℝ)..1, (p.μ * W y) ^ 2) =
            ∫ y in (0 : ℝ)..1, p.μ ^ 2 * (W y) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro y _
          ring
        _ = _ := by rw [intervalIntegral.integral_const_mul]
    rw [hmu]
    ring
  rw [hleftEq, hrightEq] at hmono
  have henergy := intervalDomain_minimal_signal_energy_eq_raw
    hgamma heq hsol ht
  have hGnonneg : 0 ≤
      ∫ y in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) y) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have hWle :
      p.μ * (∫ y in (0 : ℝ)..1, (W y) ^ 2) ≤
        chemotaxisSignalEnergy intervalDomain p.μ vStar v t := by
    change chemotaxisSignalEnergy intervalDomain p.μ vStar v t =
      p.μ * (∫ y in (0 : ℝ)..1, (W y) ^ 2) +
        ∫ y in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) y) ^ 2 at henergy
    linarith
  have hWscaled :
      (2 * p.μ) * (p.μ * (∫ y in (0 : ℝ)..1, (W y) ^ 2)) ≤
        (2 * p.μ) *
          chemotaxisSignalEnergy intervalDomain p.μ vStar v t :=
    mul_le_mul_of_nonneg_left hWle
      (mul_nonneg (by norm_num) p.hμ.le)
  change p.ν ^ 2 * (∫ y in (0 : ℝ)..1, (U y) ^ 2) ≤
    2 * p.μ * chemotaxisSignalEnergy intervalDomain p.μ vStar v t +
      2 * (∫ y in (0 : ℝ)..1, (Lap y) ^ 2)
  nlinarith

/-- The signal energy is controlled by `(μ+1)` times its gradient part on
every positive mass-constrained `γ = 1` slice. -/
theorem intervalDomain_minimal_signal_energy_control
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1) (hgamma : p.γ = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hmass : intervalDomain.integral (u t) = uStar) :
    chemotaxisSignalEnergy intervalDomain p.μ vStar v t ≤
      (p.μ + 1) * (∫ y in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) y) ^ 2) := by
  have hpoincare := intervalDomain_minimal_signal_poincare
    hm hgamma heq hsol ht hmass
  have hscaled := mul_le_mul_of_nonneg_left hpoincare p.hμ.le
  have henergy := intervalDomain_minimal_signal_energy_eq_raw
    hgamma heq hsol ht
  rw [henergy]
  nlinarith

/-- Once a mass-constrained orbit has entered the concrete eventual box, its
signal energy decays exponentially with the literal second-branch coefficient. -/
theorem intervalDomain_minimal2_signal_energy_exponential_decay
    (p : CM2Params) (hm : p.m = 1)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hgamma : p.γ = 1)
    (hbeta : 1 ≤ p.β) {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal2Formula p uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x) :
    ∃ s > 0, ∃ rate > 0, ∀ t, s ≤ t →
      chemotaxisSignalEnergy intervalDomain p.μ vStar v t ≤
        chemotaxisSignalEnergy intervalDomain p.μ vStar v s *
          Real.exp (-rate * (t - s)) := by
  let c : ℝ := minimal2SignalCoefficient p uBar vLower
  let K : ℝ := p.μ + 1
  have hc : 0 < c := by
    simpa [c] using minimal2SignalCoefficient_pos
      p huBar hvLower hthreshold
  have hK : 0 < K := by
    dsimp [K]
    linarith [p.hμ]
  rcases eventually_atTop.1 hupper with ⟨Tu, hTu⟩
  rcases eventually_atTop.1 hfloor with ⟨Tv, hTv⟩
  let Tbase : ℝ := max (max Tu Tv) 1
  have hTbase : 0 < Tbase :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hTuLe : Tu ≤ Tbase :=
    (le_max_left Tu Tv).trans (le_max_left (max Tu Tv) 1)
  have hTvLe : Tv ≤ Tbase :=
    (le_max_right Tu Tv).trans (le_max_left (max Tu Tv) 1)
  have hboxAt : ∀ q : ℝ, Tbase ≤ q →
      ∃ hsol : IsPaper2ClassicalSolution intervalDomain p (q + 1) u v,
        q ∈ Ioo (0 : ℝ) (q + 1) ∧
        intervalDomain.integral (u q) = uStar ∧
        (∀ x : intervalDomainPoint, u q x ≤ uBar) ∧
        (∀ x : intervalDomainPoint, vLower ≤ v q x) := by
    intro q hq
    have hq0 : 0 < q := lt_of_lt_of_le hTbase hq
    have hH : 0 < q + 1 := by linarith
    let hsol := huv.classical (q + 1) hH
    have hqmem : q ∈ Ioo (0 : ℝ) (q + 1) := ⟨hq0, by linarith⟩
    have hsup : intervalDomain.supNorm (u q) ≤ uBar :=
      hTu q (hTuLe.trans hq)
    have hpoint : ∀ x : intervalDomainPoint, u q x ≤ uBar := by
      intro x
      have hx :=
        IntervalChiNegH1PhysicalResolverSupProducer.intervalDomainLift_le_supNorm_of_classical
          hsol hqmem x.property
      have hx' : u q x ≤ intervalDomain.supNorm (u q) := by
        simpa [intervalDomainLift, x.property] using hx
      exact hx'.trans hsup
    have hmassQ : intervalDomain.integral (u q) = uStar := by
      simpa [HasEquilibriumMassOnPositiveTimes, intervalDomain] using
        hmass q hq0
    exact ⟨hsol, hqmem, hmassQ, hpoint,
      hTv q (hTvLe.trans hq)⟩
  let E : ℝ → ℝ := fun r =>
    chemotaxisSignalEnergy intervalDomain p.μ vStar v (r + Tbase)
  let G : ℝ → ℝ := fun r => ∫ y in (0 : ℝ)..1,
    (deriv (intervalDomainLift (v (r + Tbase))) y) ^ 2
  have hderiv : ∀ r, 0 < r → HasDerivAt E (deriv E r) r := by
    intro r hr
    let q : ℝ := r + Tbase
    obtain ⟨hsol, hqmem, _hmassQ, _hpoint, _hVfloor⟩ :=
      hboxAt q (by dsimp [q]; linarith)
    have horig := intervalDomain_minimal_signal_energy_hasDerivAt_pde
      ha0 hb0 hgamma heq hsol hqmem
    have hinner : HasDerivAt (fun z : ℝ => z + Tbase) 1 r := by
      simpa using (hasDerivAt_id r).add_const Tbase
    have hcomp := horig.comp r hinner
    have hdiff : DifferentiableAt ℝ E r := by
      simpa [E, q] using hcomp.differentiableAt
    exact hdiff.hasDerivAt
  have hdiss : ∀ r, 0 < r →
      (1 / 2 : ℝ) * deriv E r + c * G r ≤ 0 := by
    intro r hr
    let q : ℝ := r + Tbase
    obtain ⟨hsol, hqmem, _hmassQ, hpoint, hVfloor⟩ :=
      hboxAt q (by dsimp [q]; linarith)
    have horig := intervalDomain_minimal_signal_energy_hasDerivAt_pde
      ha0 hb0 hgamma heq hsol hqmem
    have hinner : HasDerivAt (fun z : ℝ => z + Tbase) 1 r := by
      simpa using (hasDerivAt_id r).add_const Tbase
    have hcomp := horig.comp r hinner
    have hslope := intervalDomain_minimal_signal_energy_slope_le
      ha0 hb0 hgamma heq hsol hqmem hbeta huBar hvLower hchi
        hpoint hVfloor
    rw [horig.deriv] at hslope
    have hLapNonneg : 0 ≤
        ∫ y in (0 : ℝ)..1,
          (deriv (fun z => deriv (intervalDomainLift (v q)) z) y) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
    have hslopeShift : deriv E r ≤
        -2 * (∫ y in (0 : ℝ)..1,
          (deriv (fun z => deriv (intervalDomainLift (v q)) z) y) ^ 2) -
          2 * c * G r := by
      calc
        deriv E r = _ := by simpa [E, q] using hcomp.deriv
        _ ≤ -2 * (∫ y in (0 : ℝ)..1,
              (deriv (fun z => deriv (intervalDomainLift (v q)) z) y) ^ 2) -
            2 * c * G r := by
          simpa [G, q, c] using hslope
    linarith
  have hcontrol : ∀ r, 0 < r → E r ≤ K * G r := by
    intro r hr
    let q : ℝ := r + Tbase
    obtain ⟨hsol, hqmem, hmassQ, _hpoint, _hVfloor⟩ :=
      hboxAt q (by dsimp [q]; linarith)
    have h := intervalDomain_minimal_signal_energy_control
      hm hgamma heq hsol hqmem hmassQ
    simpa [E, G, K, q] using h
  have hdecay := energy_exponential_decay_of_dissipation_control
    hc hK hderiv hdiss hcontrol
  let s : ℝ := Tbase + 1
  let rate : ℝ := 2 * c / K
  have hs : 0 < s := by dsimp [s]; linarith
  have hrate : 0 < rate := by
    dsimp [rate]
    positivity
  refine ⟨s, hs, rate, hrate, ?_⟩
  intro t hst
  have htShift : 1 ≤ t - Tbase := by
    dsimp [s] at hst
    linarith
  have h := hdecay 1 (t - Tbase) zero_lt_one htShift
  dsimp [E] at h
  have hleftTime : t - Tbase + Tbase = t := by ring
  have honeTime : (1 : ℝ) + Tbase = s := by
    dsimp [s]
    ring
  have htimeDiff : t - Tbase - 1 = t - s := by
    dsimp [s]
    ring
  rw [hleftTime, honeTime, htimeDiff] at h
  simpa [rate] using h

/-- The second minimal formula branch drives the signal energy to zero along
every positive bounded orbit with the equilibrium mass. -/
theorem intervalDomain_minimal2_signal_energy_tendsto_zero
    (p : CM2Params) (hm : p.m = 1)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hgamma : p.γ = 1)
    (hbeta : 1 ≤ p.β) {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal2Formula p uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x) :
    Tendsto
      (fun t => chemotaxisSignalEnergy intervalDomain p.μ vStar v t)
      atTop (𝓝 0) := by
  obtain ⟨s, hs, rate, hrate, hdecay⟩ :=
    intervalDomain_minimal2_signal_energy_exponential_decay
      p hm ha0 hb0 hgamma hbeta heq huBar hvLower hchi hthreshold
        huv hmass hupper hfloor
  have hexp0 :
      Tendsto (fun t : ℝ => Real.exp (-rate * (t - s))) atTop (𝓝 0) := by
    have hlinear :
        Tendsto (fun t : ℝ => (-rate) * t + rate * s) atTop atBot := by
      exact tendsto_atBot_add_const_right _ (rate * s)
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hrate))
    refine (Real.tendsto_exp_atBot.comp hlinear).congr' ?_
    filter_upwards with t
    apply congrArg Real.exp
    ring
  have hupper0 : Tendsto
      (fun t : ℝ =>
        chemotaxisSignalEnergy intervalDomain p.μ vStar v s *
          Real.exp (-rate * (t - s))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hexp0
  refine squeeze_zero' ?_ ?_ hupper0
  · exact Filter.Eventually.of_forall fun _ =>
      intervalDomain_chemotaxisSignalEnergy_nonneg p.hμ.le
  · exact eventually_atTop.2 ⟨s, fun t ht => hdecay t ht⟩

/-- The coercive `vₓₓ` term has arbitrarily late small slices in the second
minimal formula branch. -/
theorem intervalDomain_minimal2_exists_late_signal_lap_lt
    (p : CM2Params)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hgamma : p.γ = 1)
    (hbeta : 1 ≤ p.β) {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal2Formula p uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x)
    {T q : ℝ} (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      (∫ y in (0 : ℝ)..1,
        (deriv (fun z => deriv (intervalDomainLift (v t)) z) y) ^ 2) < q := by
  let c : ℝ := minimal2SignalCoefficient p uBar vLower
  have hc : 0 < c := by
    simpa [c] using minimal2SignalCoefficient_pos
      p huBar hvLower hthreshold
  rcases eventually_atTop.1 hupper with ⟨Tu, hTu⟩
  rcases eventually_atTop.1 hfloor with ⟨Tv, hTv⟩
  let Tbase : ℝ := max (max Tu Tv) (max T 1)
  have hTbase : 0 < Tbase :=
    lt_of_lt_of_le zero_lt_one
      ((le_max_right T 1).trans (le_max_right (max Tu Tv) (max T 1)))
  have hTle : T ≤ Tbase :=
    (le_max_left T 1).trans (le_max_right (max Tu Tv) (max T 1))
  have hTuLe : Tu ≤ Tbase :=
    (le_max_left Tu Tv).trans (le_max_left (max Tu Tv) (max T 1))
  have hTvLe : Tv ≤ Tbase :=
    (le_max_right Tu Tv).trans (le_max_left (max Tu Tv) (max T 1))
  let E : ℝ → ℝ := fun s =>
    chemotaxisSignalEnergy intervalDomain p.μ vStar v s
  let D : ℝ → ℝ := fun s => ∫ y in (0 : ℝ)..1,
    (deriv (fun z => deriv (intervalDomainLift (v s)) z) y) ^ 2
  obtain ⟨t, htbase, htSmall⟩ :=
    exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
      (E := E) (D := D) (slope := fun s => deriv E s)
      (c := (2 : ℝ)) (T := Tbase) (q := q)
      (by norm_num) hTbase hq
      (fun _ _ => by
        dsimp [E]
        exact intervalDomain_chemotaxisSignalEnergy_nonneg p.hμ.le)
      (fun s hs => by
        have hH : 0 < s + 1 := by linarith
        have hsmem : s ∈ Ioo (0 : ℝ) (s + 1) := ⟨hs, by linarith⟩
        have horig := intervalDomain_minimal_signal_energy_hasDerivAt_pde
          ha0 hb0 hgamma heq (huv.classical (s + 1) hH) hsmem
        exact (by
          simpa [E] using horig.differentiableAt.hasDerivAt))
      (fun s hs => by
        have hs0 : 0 < s := lt_of_lt_of_le hTbase hs
        have hH : 0 < s + 1 := by linarith
        have hsmem : s ∈ Ioo (0 : ℝ) (s + 1) := ⟨hs0, by linarith⟩
        let hsol := huv.classical (s + 1) hH
        have hsup : intervalDomain.supNorm (u s) ≤ uBar :=
          hTu s (hTuLe.trans hs)
        have hpoint : ∀ x : intervalDomainPoint, u s x ≤ uBar := by
          intro x
          have hx :=
            IntervalChiNegH1PhysicalResolverSupProducer.intervalDomainLift_le_supNorm_of_classical
              hsol hsmem x.property
          have hx' : u s x ≤ intervalDomain.supNorm (u s) := by
            simpa [intervalDomainLift, x.property] using hx
          exact hx'.trans hsup
        have hVfloor : ∀ x : intervalDomainPoint, vLower ≤ v s x :=
          hTv s (hTvLe.trans hs)
        have hslope := intervalDomain_minimal_signal_energy_slope_le
          ha0 hb0 hgamma heq hsol hsmem hbeta huBar hvLower hchi
            hpoint hVfloor
        have hGnonneg : 0 ≤
            ∫ y in (0 : ℝ)..1,
              (deriv (intervalDomainLift (v s)) y) ^ 2 :=
          intervalIntegral.integral_nonneg (by norm_num)
            (fun _ _ => sq_nonneg _)
        dsimp [E, D]
        exact le_trans hslope (by nlinarith [mul_nonneg hc.le hGnonneg]))
  exact ⟨t, hTle.trans htbase, by simpa [D] using htSmall⟩

/-- The decaying signal energy and arbitrarily late small signal-Laplacian
slices force arbitrarily late small population `L²` slices. -/
theorem intervalDomain_minimal2_exists_late_l2_lt
    (p : CM2Params) (hm : p.m = 1)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hgamma : p.γ = 1)
    (hbeta : 1 ≤ p.β) {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal2Formula p uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x)
    {T q : ℝ} (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y - uStar) ^ 2) < q := by
  let E : ℝ → ℝ := fun s ⇒
    chemotaxisSignalEnergy intervalDomain p.μ vStar v s
  let L2 : ℝ → ℝ := fun s ⇒ ∫ y in (0 : ℝ)..1,
    (intervalDomainLift (u s) y - uStar) ^ 2
  let Lap2 : ℝ → ℝ := fun s ⇒ ∫ y in (0 : ℝ)..1,
    (deriv (fun z ⇒ deriv (intervalDomainLift (v s)) z) y) ^ 2
  let energyTarget : ℝ := q * p.ν ^ 2 / (8 * p.μ)
  let lapTarget : ℝ := q * p.ν ^ 2 / 8
  have henergyTarget : 0 < energyTarget := by
    dsimp [energyTarget]
    positivity
  have hlapTarget : 0 < lapTarget := by
    dsimp [lapTarget]
    positivity
  have hconv : Tendsto E atTop (𝒩 0) := by
    simpa [E] using intervalDomain_minimal2_signal_energy_tendsto_zero
      p hm ha0 hb0 hgamma hbeta heq huBar hvLower hchi hthreshold
        huv hmass hupper hfloor
  have henergyEventually : ∀ᶠ s : ℝ in atTop, E s < energyTarget :=
    hconv.eventually (Iio_mem_nhds henergyTarget)
  rcases eventually_atTop.1 henergyEventually with ⟨Te, hTe⟩
  let Tbase : ℝ := max (max T Te) 1
  obtain ⟨t, htbase, hlap⟩ :=
    intervalDomain_minimal2_exists_late_signal_lap_lt
      p ha0 hb0 hgamma hbeta heq huBar hvLower hchi hthreshold
        huv hupper hfloor (T := Tbase) hlapTarget
  have htT : T ≤ t :=
    (le_max_left T Te).trans ((le_max_left (max T Te) 1).trans htbase)
  have htTe : Te ≤ t :=
    (le_max_right T Te).trans ((le_max_left (max T Te) 1).trans htbase)
  have htPos : 0 < t :=
    lt_of_lt_of_le zero_lt_one ((le_max_right (max T Te) 1).trans htbase)
  have henergy : E t < energyTarget := hTe t htTe
  have hH : 0 < t + 1 := by linarith
  have helliptic : p.ν ^ 2 * L2 t ≤
      2 * p.μ * E t + 2 * Lap2 t := by
    simpa [E, L2, Lap2] using intervalDomain_minimal_signal_elliptic_l2
      hgamma heq (huv.classical (t + 1) hH)
        (⟨htPos, by linarith⟩ : t ∈ Ioo (0 : ℝ) (t + 1))
  have henergyScaled : 2 * p.μ * E t < q * p.ν ^ 2 / 4 := by
    have hmul := mul_lt_mul_of_pos_left henergy
      (mul_pos (by norm_num : (0 : ℝ) < 2) p.hμ)
    have hrewrite : 2 * p.μ * energyTarget = q * p.ν ^ 2 / 4 := by
      dsimp [energyTarget]
      field_simp [ne_of_gt p.hμ]
      <;> ring
    rw [hrewrite] at hmul
    exact hmul
  have hlapScaled : 2 * Lap2 t < q * p.ν ^ 2 / 4 := by
    have hmul := mul_lt_mul_of_pos_left hlap (by norm_num : (0 : ℝ) < 2)
    have hrewrite : 2 * lapTarget = q * p.ν ^ 2 / 4 := by
      dsimp [lapTarget]
      ring
    simpa [Lap2, hrewrite] using hmul
  have hrhs : 2 * p.μ * E t + 2 * Lap2 t < p.ν ^ 2 * q := by
    have hsum := add_lt_add henergyScaled hlapScaled
    nlinarith
  have hscaled : p.ν ^ 2 * L2 t < p.ν ^ 2 * q :=
    helliptic.trans_lt hrhs
  have hnuSq : 0 < p.ν ^ 2 := sq_pos_of_pos p.hν
  have hL2 : L2 t < q := (mul_lt_mul_left hnuSq).mp hscaled
  exact ⟨t, htT, by simpa [L2] using hL2⟩

/-- The signal-energy slices from the second minimal formula branch enter
every weak supremum neighborhood at arbitrarily late positive times. -/
theorem intervalDomain_minimal2_exists_late_supClose
    (p : CM2Params) (hm : p.m = 1)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hgamma : p.γ = 1)
    (hbeta : 1 ≤ p.β) {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal2Formula p uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x)
    {T eps : ℝ} (heps : 0 < eps) :
    ∃ t, T ≤ t ∧
      SupCloseToConstant intervalDomain (u t) uStar eps := by
  have hlate : ∀ {T q : ℝ}, 0 < q →
      ∃ t, T ≤ t ∧
        chemotaxisThetaDissipation intervalDomain uStar 1 (u t) < q := by
    intro T q hq
    obtain ⟨t, ht, hsmall⟩ := intervalDomain_minimal2_exists_late_l2_lt
      p hm ha0 hb0 hgamma hbeta heq huBar hvLower hchi hthreshold
        huv hmass hupper hfloor hq
    refine ⟨t, ht, ?_⟩
    unfold chemotaxisThetaDissipation
    simp only [Real.rpow_one]
    change intervalDomainIntegral
      (fun x ⇒ (u t x - uStar) * (u t x - uStar)) < q
    unfold intervalDomainIntegral
    calc
      (∫ y in (0 : ℝ)..1,
          intervalDomainLift
            (fun x ⇒ (u t x - uStar) * (u t x - uStar)) y) =
          ∫ y in (0 : ℝ)..1,
            (intervalDomainLift (u t) y - uStar) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
        simp [intervalDomainLift, hy, pow_two]
      _ < q := hsmall
  exact intervalDomain_exists_late_supClose_of_thetaDissipation_slices
    p hm heq.u_pos (by norm_num) huv hlate heps

#print axioms intervalDomain_minimal_signal_pairing_comm
#print axioms intervalDomain_minimal_signal_lap_sq_intervalIntegrable
#print axioms intervalDomain_chemotaxisSignalEnergy_eq_pairing
#print axioms intervalDomain_joint_intervalIntegral_hasDerivAt
#print axioms intervalDomain_minimal_signal_energy_hasDerivAt
#print axioms intervalDomain_minimal_signal_ut_pairing_pde
#print axioms intervalDomain_minimal_signal_diffusion_pairing
#print axioms intervalDomain_minimal_signal_energy_hasDerivAt_pde
#print axioms minimal2SignalCoefficient_pos
#print axioms intervalDomain_minimal_signal_chemotaxis_integral_le
#print axioms intervalDomain_minimal_signal_energy_slope_le
#print axioms intervalDomain_minimal_signal_mean_zero
#print axioms intervalDomain_minimal_signal_poincare
#print axioms intervalDomain_minimal_signal_energy_control
#print axioms intervalDomain_minimal_signal_elliptic_l2
#print axioms intervalDomain_minimal2_signal_energy_exponential_decay
#print axioms intervalDomain_minimal2_signal_energy_tendsto_zero
#print axioms intervalDomain_minimal2_exists_late_signal_lap_lt
#print axioms intervalDomain_minimal2_exists_late_l2_lt
#print axioms intervalDomain_minimal2_exists_late_supClose

end

end ShenWork.Paper3
