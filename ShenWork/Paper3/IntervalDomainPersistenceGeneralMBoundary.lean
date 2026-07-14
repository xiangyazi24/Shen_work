import ShenWork.Paper3.IntervalDomainPersistenceGeneralMMinPoint
import ShenWork.Paper2.IntervalDomainMChemDivBoundaryLimit
import ShenWork.Paper2.IntervalLemma31Closure

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.MinPersistenceAtoms
open ShenWork.Paper2.IntervalDomainMMinPersistence

namespace ShenWork.Paper3

noncomputable section

/-!
# Faithful general-m endpoint minimum slopes

The parabolic equation is imposed on the open interval.  At a Neumann
endpoint we pass its faithful `u^m` chemotaxis divergence to the boundary via
the already proved continuous physical representative, then use the one-sided
second-derivative minimum test.
-/

private def generalMBoundaryChemValue
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) (e : ℝ) : ℝ :=
  intervalDomainLift u e ^ p.m *
    ((1 + intervalDomainLift v e) ^ (-p.β) *
      (p.μ * intervalDomainLift v e -
        p.ν * intervalDomainLift u e ^ p.γ))

private theorem boundaryChemDivM_eq_physicalRep_eventually
    {p : CM2Params} {T t e : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    boundaryChemDivMReal p (u t) (v t) =ᶠ[
      nhdsWithin e (Ioo (0 : ℝ) 1)]
        classicalChemDivMPhysicalRep p u v t := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [boundaryChemDivMReal, dif_pos (Ioo_subset_Icc_self hy)]
  exact intervalDomainMChemotaxisDiv_eq_physicalRep_interior
    hsol ht0 htT hy

/-- Exact left-endpoint physical limit of the faithful divergence. -/
theorem boundaryChemDivM_left_limit_exact
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    Tendsto (boundaryChemDivMReal p (u t) (v t))
      (nhdsWithin (0 : ℝ) (Ioo (0 : ℝ) 1))
      (nhds (generalMBoundaryChemValue p (u t) (v t) 0)) := by
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hclosed := hsol.regularity.2.2.2.2.1 t ht
  have hdu : deriv (intervalDomainLift (u t)) 0 = 0 := hclosed.1.2.1
  have hdv : deriv (intervalDomainLift (v t)) 0 = 0 := hclosed.2.2.1
  have hcont := classicalChemDivMPhysicalRep_continuousOn_Icc
    hsol ht0 htT
  have hlim : Tendsto (classicalChemDivMPhysicalRep p u v t)
      (nhdsWithin (0 : ℝ) (Ioo (0 : ℝ) 1))
      (nhds (classicalChemDivMPhysicalRep p u v t 0)) :=
    (hcont 0 ⟨le_rfl, zero_le_one⟩).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  have hvalue : classicalChemDivMPhysicalRep p u v t 0 =
      generalMBoundaryChemValue p (u t) (v t) 0 := by
    simp only [classicalChemDivMPhysicalRep, generalMBoundaryChemValue]
    rw [hdu, hdv]
    ring
  rw [hvalue] at hlim
  exact hlim.congr'
    (boundaryChemDivM_eq_physicalRep_eventually hsol ht0 htT).symm

/-- Exact right-endpoint physical limit of the faithful divergence. -/
theorem boundaryChemDivM_right_limit_exact
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    Tendsto (boundaryChemDivMReal p (u t) (v t))
      (nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1))
      (nhds (generalMBoundaryChemValue p (u t) (v t) 1)) := by
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hclosed := hsol.regularity.2.2.2.2.1 t ht
  have hdu : deriv (intervalDomainLift (u t)) 1 = 0 := hclosed.1.2.2
  have hdv : deriv (intervalDomainLift (v t)) 1 = 0 := hclosed.2.2.2
  have hcont := classicalChemDivMPhysicalRep_continuousOn_Icc
    hsol ht0 htT
  have hlim : Tendsto (classicalChemDivMPhysicalRep p u v t)
      (nhdsWithin (1 : ℝ) (Ioo (0 : ℝ) 1))
      (nhds (classicalChemDivMPhysicalRep p u v t 1)) :=
    (hcont 1 ⟨zero_le_one, le_rfl⟩).mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
  have hvalue : classicalChemDivMPhysicalRep p u v t 1 =
      generalMBoundaryChemValue p (u t) (v t) 1 := by
    simp only [classicalChemDivMPhysicalRep, generalMBoundaryChemValue]
    rw [hdu, hdv]
    ring
  rw [hvalue] at hlim
  exact hlim.congr'
    (boundaryChemDivM_eq_physicalRep_eventually hsol ht0 htT).symm

/-- The exact endpoint physical divergence is bounded above by the
signal-weighted `Theta` coefficient. -/
private theorem generalMBoundaryChemValue_le
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {e : ℝ}
    (hβ : 1 ≤ p.β) (hu : 0 ≤ intervalDomainLift u e)
    (hv : 0 ≤ intervalDomainLift v e) :
    generalMBoundaryChemValue p u v e ≤
      intervalDomainLift u e ^ p.m *
        (p.μ * Theta_beta (p.β - 1)) := by
  let U : ℝ := intervalDomainLift u e
  let V : ℝ := intervalDomainLift v e
  have htheta := theta_linear_bound_public (p := p) hβ hv
  have hden_nonneg : 0 ≤ (1 + V) ^ (-p.β) :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 + V) _
  have hUγ_nonneg : 0 ≤ U ^ p.γ := Real.rpow_nonneg hu _
  have hdrop :
      (1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ) ≤
        (1 + V) ^ (-p.β) * (p.μ * V) := by
    apply mul_le_mul_of_nonneg_left _ hden_nonneg
    have : 0 ≤ p.ν * U ^ p.γ := mul_nonneg p.hν.le hUγ_nonneg
    linarith
  have hpow_eq :
      (1 + V) ^ (-p.β) * (p.μ * V) =
        p.μ * (V / (1 + V) ^ p.β) := by
    rw [Real.rpow_neg (le_of_lt (by linarith : 0 < 1 + V))]
    ring
  have hcoeff :
      (1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ) ≤
        p.μ * Theta_beta (p.β - 1) :=
    hdrop.trans (by
      rw [hpow_eq]
      exact mul_le_mul_of_nonneg_left htheta p.hμ.le)
  exact mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg hu _)

set_option maxHeartbeats 2400000 in
/-- Faithful general-`m` slope bound at a left-endpoint spatial minimum. -/
theorem intervalDomain_generalM_boundary_min_point_left
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmin : ∀ y ∈ Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y) :
    generalMLogisticRhs p (intervalDomainLift (u t) 0) ≤
      deriv (fun r => intervalDomainLift (u r) 0) t := by
  have htmem : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨_, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let R : ℝ → ℝ := fun x => U x * (p.a - p.b * U x ^ p.α)
  let Gt : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t
  let CD : ℝ → ℝ := boundaryChemDivMReal p (u t) (v t)
  let C0 : ℝ := generalMBoundaryChemValue p (u t) (v t) 0
  have h01 : (0 : ℝ) < 1 := by norm_num
  have h0Icc : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hfilter : nhdsWithin (0 : ℝ) (Ioo 0 1) =
      nhdsWithin 0 (Ioi 0) := nhdsWithin_Ioo_eq_nhdsGT h01
  have hCD_lim : Tendsto CD (nhdsWithin 0 (Ioi 0)) (nhds C0) := by
    rw [← hfilter]
    exact boundaryChemDivM_left_limit_exact hsol ht0 htT
  have hGt_lim : Tendsto Gt (nhdsWithin 0 (Ioi 0)) (nhds (Gt 0)) := by
    have hmaps : MapsTo (fun w => (t, w)) (Icc (0 : ℝ) 1)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn Gt (Icc (0 : ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  have hUcont : ContinuousOn U (Icc (0 : ℝ) 1) :=
    (hClosed t htmem).1.1.continuousOn
  have hR_lim : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds (R 0)) := by
    have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) :=
      hUcont.mul (continuousOn_const.sub
        (continuousOn_const.mul
          (hUcont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcont 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  have hpde_eq : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (deriv U) x = Gt x + p.χ₀ * CD x - R x := by
    intro x hx
    have hpu := ShenWork.Paper2.IsPaper2ClassicalSolution.pde_u
      (D := intervalDomainM) hsol ht0 htT
        (x := (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)) hx
    have etd : intervalDomainM.timeDeriv u t
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = Gt x := by
      change deriv (fun r =>
        u r (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)) t = Gt x
      simp only [Gt]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    have elap : intervalDomainM.laplacian (u t)
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        deriv (deriv U) x := rfl
    have ecd : intervalDomainM.chemotaxisDiv p (u t) (v t)
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x := by
      change intervalDomainChemotaxisDivM p (u t) (v t)
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x
      simp [CD, boundaryChemDivMReal, Ioo_subset_Icc_self hx]
    have eu : u t (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = U x := by
      change u t (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        intervalDomainLift (u t) x
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    rw [etd, elap, ecd, eu] at hpu
    simp only [R]
    linarith
  let Vlim : ℝ := Gt 0 + p.χ₀ * C0 - R 0
  have hUxx_lim : Tendsto (deriv (deriv U))
      (nhdsWithin 0 (Ioi 0)) (nhds Vlim) := by
    refine ((hGt_lim.add (hCD_lim.const_mul p.χ₀)).sub hR_lim).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hpde_eq x hx).symm
  have hU2 : ContDiffOn ℝ 2 U (Icc (0 : ℝ) 1) :=
    (hClosed t htmem).1.1
  have hU2Ioo := hU2.mono Ioo_subset_Icc_self
  have hNeu0 : Tendsto (deriv U) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (hNeu t htmem).1.1
  have hwcont : ContinuousWithinAt U (Ici 0) 0 := by
    refine (hUcont 0 h0Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Icc (0 : ℝ) 1 = Ici (0 : ℝ) ∩ Iic 1 := by
      ext z
      simp [mem_Icc, mem_Ici, mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  have hd1 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt U (deriv U x) x := fun x hx =>
    (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hU2Ioo hx).1
  have hd2 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x := fun x hx =>
    (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hU2Ioo hx).2
  have hVlim : 0 ≤ Vlim :=
    boundary_min_deriv2_rlimit_nonneg h01 hwcont hmin hd1 hd2
      hNeu0 hUxx_lim
  have hU0pos : 0 < U 0 := by
    simpa [U, intervalDomainLift] using
      hsol.u_pos' (x := (⟨0, h0Icc⟩ : intervalDomainPoint)) ht0 htT
  have hV0nn : 0 ≤ intervalDomainLift (v t) 0 := by
    simpa [intervalDomainLift] using
      hsol.v_nonneg (x := (⟨0, h0Icc⟩ : intervalDomainPoint)) ht0 htT
  have hC0_le : C0 ≤ U 0 ^ p.m *
      (p.μ * Theta_beta (p.β - 1)) := by
    exact generalMBoundaryChemValue_le hβ hU0pos.le hV0nn
  have hchem :
      -p.χ₀ * (U 0 ^ p.m * (p.μ * Theta_beta (p.β - 1))) ≤
        -p.χ₀ * C0 :=
    mul_le_mul_of_nonpos_left hC0_le (by linarith : -p.χ₀ ≤ 0)
  have hpow : U 0 * (p.b * U 0 ^ p.α) =
      p.b * U 0 ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hU0pos.le
      (by norm_num : 0 ≤ (1 : ℝ)) p.hα.le, Real.rpow_one]
    ring
  have hGt : R 0 - p.χ₀ * C0 ≤ Gt 0 := by
    dsimp [Vlim] at hVlim
    linarith
  change generalMLogisticRhs p (U 0) ≤ Gt 0
  simp only [generalMLogisticRhs, generalMChemLoss, R] at hGt ⊢
  nlinarith [hGt, hchem, hpow]

set_option maxHeartbeats 2400000 in
/-- Faithful general-`m` slope bound at a right-endpoint spatial minimum. -/
theorem intervalDomain_generalM_boundary_min_point_right
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmin : ∀ y ∈ Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) 1 ≤ intervalDomainLift (u t) y) :
    generalMLogisticRhs p (intervalDomainLift (u t) 1) ≤
      deriv (fun r => intervalDomainLift (u r) 1) t := by
  have htmem : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨_, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let R : ℝ → ℝ := fun x => U x * (p.a - p.b * U x ^ p.α)
  let Gt : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t
  let CD : ℝ → ℝ := boundaryChemDivMReal p (u t) (v t)
  let C1 : ℝ := generalMBoundaryChemValue p (u t) (v t) 1
  have h01 : (0 : ℝ) < 1 := by norm_num
  have h1Icc : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hfilter : nhdsWithin (1 : ℝ) (Ioo 0 1) =
      nhdsWithin 1 (Iio 1) := nhdsWithin_Ioo_eq_nhdsLT h01
  have hCD_lim : Tendsto CD (nhdsWithin 1 (Iio 1)) (nhds C1) := by
    rw [← hfilter]
    exact boundaryChemDivM_right_limit_exact hsol ht0 htT
  have hGt_lim : Tendsto Gt (nhdsWithin 1 (Iio 1)) (nhds (Gt 1)) := by
    have hmaps : MapsTo (fun w => (t, w)) (Icc (0 : ℝ) 1)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn Gt (Icc (0 : ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
  have hUcont : ContinuousOn U (Icc (0 : ℝ) 1) :=
    (hClosed t htmem).1.1.continuousOn
  have hR_lim : Tendsto R (nhdsWithin 1 (Iio 1)) (nhds (R 1)) := by
    have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) :=
      hUcont.mul (continuousOn_const.sub
        (continuousOn_const.mul
          (hUcont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcont 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
  have hpde_eq : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (deriv U) x = Gt x + p.χ₀ * CD x - R x := by
    intro x hx
    have hpu := ShenWork.Paper2.IsPaper2ClassicalSolution.pde_u
      (D := intervalDomainM) hsol ht0 htT
        (x := (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)) hx
    have etd : intervalDomainM.timeDeriv u t
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = Gt x := by
      change deriv (fun r =>
        u r (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)) t = Gt x
      simp only [Gt]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    have elap : intervalDomainM.laplacian (u t)
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        deriv (deriv U) x := rfl
    have ecd : intervalDomainM.chemotaxisDiv p (u t) (v t)
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x := by
      change intervalDomainChemotaxisDivM p (u t) (v t)
        (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = CD x
      simp [CD, boundaryChemDivMReal, Ioo_subset_Icc_self hx]
    have eu : u t (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = U x := by
      change u t (⟨x, Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        intervalDomainLift (u t) x
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    rw [etd, elap, ecd, eu] at hpu
    simp only [R]
    linarith
  let Vlim : ℝ := Gt 1 + p.χ₀ * C1 - R 1
  have hUxx_lim : Tendsto (deriv (deriv U))
      (nhdsWithin 1 (Iio 1)) (nhds Vlim) := by
    refine ((hGt_lim.add (hCD_lim.const_mul p.χ₀)).sub hR_lim).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hpde_eq x hx).symm
  have hU2 : ContDiffOn ℝ 2 U (Icc (0 : ℝ) 1) :=
    (hClosed t htmem).1.1
  have hU2Ioo := hU2.mono Ioo_subset_Icc_self
  have hNeu1 : Tendsto (deriv U) (nhdsWithin 1 (Iio 1)) (nhds 0) :=
    (hNeu t htmem).1.2
  have hwcont : ContinuousWithinAt U (Iic 1) 1 := by
    refine (hUcont 1 h1Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Icc (0 : ℝ) 1 = Ici (0 : ℝ) ∩ Iic 1 := by
      ext z
      simp [mem_Icc, mem_Ici, mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h01)) self_mem_nhdsWithin
  have hd1 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt U (deriv U x) x := fun x hx =>
    (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hU2Ioo hx).1
  have hd2 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x := fun x hx =>
    (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hU2Ioo hx).2
  have hVlim : 0 ≤ Vlim :=
    boundary_min_deriv2_llimit_nonneg (η := 1) h01 hwcont
      (fun x hx => hmin x (by simpa using hx))
      (fun x hx => hd1 x (by simpa using hx))
      (fun x hx => hd2 x (by simpa using hx))
      hNeu1 hUxx_lim
  have hU1pos : 0 < U 1 := by
    simpa [U, intervalDomainLift] using
      hsol.u_pos' (x := (⟨1, h1Icc⟩ : intervalDomainPoint)) ht0 htT
  have hV1nn : 0 ≤ intervalDomainLift (v t) 1 := by
    simpa [intervalDomainLift] using
      hsol.v_nonneg (x := (⟨1, h1Icc⟩ : intervalDomainPoint)) ht0 htT
  have hC1_le : C1 ≤ U 1 ^ p.m *
      (p.μ * Theta_beta (p.β - 1)) := by
    exact generalMBoundaryChemValue_le hβ hU1pos.le hV1nn
  have hchem :
      -p.χ₀ * (U 1 ^ p.m * (p.μ * Theta_beta (p.β - 1))) ≤
        -p.χ₀ * C1 :=
    mul_le_mul_of_nonpos_left hC1_le (by linarith : -p.χ₀ ≤ 0)
  have hpow : U 1 * (p.b * U 1 ^ p.α) =
      p.b * U 1 ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hU1pos.le
      (by norm_num : 0 ≤ (1 : ℝ)) p.hα.le, Real.rpow_one]
    ring
  have hGt : R 1 - p.χ₀ * C1 ≤ Gt 1 := by
    dsimp [Vlim] at hVlim
    linarith
  change generalMLogisticRhs p (U 1) ≤ Gt 1
  simp only [generalMLogisticRhs, generalMChemLoss, R] at hGt ⊢
  nlinarith [hGt, hchem, hpow]

/-- Faithful general-`m` minimum-slope bound at every point of the closed
unit interval. -/
theorem intervalDomain_generalM_min_point_slope_bound
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmin : ∀ y, u t x ≤ u t y) :
    generalMLogisticRhs p (intervalDomainLift (u t) x.1) ≤
      intervalDomainM.timeDeriv u t x := by
  rcases lt_or_eq_of_le x.2.1 with h0 | h0
  · rcases lt_or_eq_of_le x.2.2 with h1 | h1
    · have hx_lift : intervalDomainLift (u t) x.1 = u t x := by
        unfold intervalDomainLift
        split_ifs with hx
        · exact congrArg (u t) (Subtype.ext rfl)
        · exact False.elim (hx x.2)
      rw [hx_lift]
      exact intervalDomain_generalM_interior_min_point_of_solution
        hχ0 hβ hsol ht0 htT ⟨h0, h1⟩ hmin
    · have hx11 : x.1 = 1 := h1
      have hminlift : ∀ y ∈ Ioo (0 : ℝ) 1,
          intervalDomainLift (u t) 1 ≤ intervalDomainLift (u t) y := by
        intro y hy
        have hlift1 : intervalDomainLift (u t) 1 = u t x := by
          rw [intervalDomainLift,
            dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from
              ⟨zero_le_one, le_refl _⟩)]
          exact congrArg (u t) (Subtype.ext hx11.symm)
        have hlifty : intervalDomainLift (u t) y =
            u t ⟨y, Ioo_subset_Icc_self hy⟩ := by
          rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hy)]
        rw [hlift1, hlifty]
        exact hmin ⟨y, Ioo_subset_Icc_self hy⟩
      have hb := intervalDomain_generalM_boundary_min_point_right
        hχ0 hβ hsol ht0 htT hminlift
      have htd : intervalDomainM.timeDeriv u t x =
          deriv (fun r => intervalDomainLift (u r) 1) t := by
        show deriv (fun s => u s x) t =
          deriv (fun r => intervalDomainLift (u r) 1) t
        congr 1
        funext r
        rw [intervalDomainLift,
          dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from
            ⟨zero_le_one, le_refl _⟩)]
        exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
      rw [hx11, htd]
      exact hb
  · have hx10 : x.1 = 0 := h0.symm
    have hminlift : ∀ y ∈ Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y := by
      intro y hy
      have hlift0 : intervalDomainLift (u t) 0 = u t x := by
        rw [intervalDomainLift,
          dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
            ⟨le_refl _, zero_le_one⟩)]
        exact congrArg (u t) (Subtype.ext hx10.symm)
      have hlifty : intervalDomainLift (u t) y =
          u t ⟨y, Ioo_subset_Icc_self hy⟩ := by
        rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hy)]
      rw [hlift0, hlifty]
      exact hmin ⟨y, Ioo_subset_Icc_self hy⟩
    have hb := intervalDomain_generalM_boundary_min_point_left
      hχ0 hβ hsol ht0 htT hminlift
    have htd : intervalDomainM.timeDeriv u t x =
        deriv (fun r => intervalDomainLift (u r) 0) t := by
      show deriv (fun s => u s x) t =
        deriv (fun r => intervalDomainLift (u r) 0) t
      congr 1
      funext r
      rw [intervalDomainLift,
        dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
          ⟨le_refl _, zero_le_one⟩)]
      exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
    rw [hx10, htd]
    exact hb

end


end ShenWork.Paper3

#print axioms ShenWork.Paper3.boundaryChemDivM_left_limit_exact
#print axioms ShenWork.Paper3.boundaryChemDivM_right_limit_exact
#print axioms ShenWork.Paper3.intervalDomain_generalM_boundary_min_point_left
#print axioms ShenWork.Paper3.intervalDomain_generalM_boundary_min_point_right
#print axioms ShenWork.Paper3.intervalDomain_generalM_min_point_slope_bound
