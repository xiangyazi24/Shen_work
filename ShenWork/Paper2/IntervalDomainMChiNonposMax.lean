/-
  Maximum-principle estimates for the faithful general-m interval model.
-/
import ShenWork.Paper2.IntervalDomainMChemDivBoundaryLimit
import ShenWork.Paper2.IntervalLemma31Closure

open ShenWork.IntervalDomain ShenWork.Paper2 Filter Topology
open ShenWork.MaxPrincipleAtoms ShenWork.MinPersistenceAtoms
open ShenWork.Paper2.IntervalDomainMMinPersistence
open Set

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMChiNonpos

private theorem lift_eq_interior (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- Interior maximum estimate for a faithful general-`m` solution. -/
theorem interior_max_point_of_solution_M
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hmax : ∀ y, u t y ≤ u t x) :
    intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
        (p.a - p.b * intervalDomainLift (u t) x.1 ^ p.α) := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, _, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t))
      (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).2
  have hv_cont : ContinuousOn (intervalDomainLift (v t))
      (Set.Icc (0 : ℝ) 1) := (hClosed t htmem).2.1.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (hNeu t htmem).2.2
  have hu_pos : ∀ y, 0 < u t y := fun y => hsol.u_pos' ht0 htT
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hux_lift : intervalDomainLift (u t) x.1 = u t x := by
    rw [lift_eq_interior (u t) hint]
    exact congrArg (u t) (Subtype.ext rfl)
  have hM_nonneg : 0 ≤ intervalDomainLift (u t) x.1 := by
    rw [hux_lift]
    exact (hu_pos x).le
  have hu_le_int : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ intervalDomainLift (u t) x.1 := by
    intro y hy
    rw [lift_eq_interior (u t) hy, hux_lift]
    exact hmax _
  have hu_nonneg_int : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ intervalDomainLift (u t) y := by
    intro y hy
    rw [lift_eq_interior (u t) hy]
    exact (hu_pos _).le
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y =
        p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ := by
    intro y hy
    have hpv := hsol.pde_v ht0 htT
      (show (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) ∈
        intervalDomainM.inside from hy)
    rw [lift_eq_interior (v t) hy, lift_eq_interior (u t) hy]
    have hlap : intervalDomainM.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) =
          deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  set B : ℝ := p.ν * intervalDomainLift (u t) x.1 ^ p.γ with hBdef
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
  have hd1 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift (v t)) y := by
    intro y hy
    exact (hv_c2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hy)
  have hd2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y := by
    intro y hy
    exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).2).differentiableAt
  have hSrc : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      |p.ν * intervalDomainLift (u t) y ^ p.γ| ≤ B := by
    intro y hy
    have huy_nn := hu_nonneg_int y hy
    have hpow : intervalDomainLift (u t) y ^ p.γ ≤
        intervalDomainLift (u t) x.1 ^ p.γ :=
      Real.rpow_le_rpow huy_nn (hu_le_int y hy) p.hγ.le
    have hnn : 0 ≤ p.ν * intervalDomainLift (u t) y ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg huy_nn _)
    rw [abs_of_nonneg hnn, hBdef]
    exact mul_le_mul_of_nonneg_left hpow p.hν.le
  have hv_bound := elliptic_sup_bound (w := intervalDomainLift (v t))
    (Src := fun y => p.ν * intervalDomainLift (u t) y ^ p.γ)
    (μ := p.μ) (B := B) p.hμ hv_cont hd1 hd2 hPDE_v hSrc hNeu0 hNeu1
  have hvx_le : intervalDomainLift (v t) x.1 ≤ B / p.μ :=
    hv_bound x.1 (Set.Ioo_subset_Icc_self hint)
  have hμv_le : p.μ * intervalDomainLift (v t) x.1 ≤ B := by
    rw [mul_comm]
    exact (le_div_iff₀ p.hμ).mp hvx_le
  have hvxx_nonpos : deriv (deriv (intervalDomainLift (v t))) x.1 ≤ 0 := by
    rw [hPDE_v x.1 hint, ← hBdef]
    linarith
  have hux0 := interior_argmax_deriv_zero hmax hint
    ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hint).1.differentiableAt)
  have hG_nonpos := flux_coeff_nonpos (β := p.β)
    (v := intervalDomainLift (v t) x.1)
    (vx := deriv (intervalDomainLift (v t)) x.1)
    (vxx := deriv (deriv (intervalDomainLift (v t))) x.1)
    p.hβ (hv_nn x.1) hvxx_nonpos
  have hrep : classicalChemDivMPhysicalRep p u v t x.1 =
      intervalDomainLift (u t) x.1 ^ p.m *
        (-p.β * (1 + intervalDomainLift (v t) x.1) ^ (-p.β - 1) *
            deriv (intervalDomainLift (v t)) x.1 ^ 2 +
          (1 + intervalDomainLift (v t) x.1) ^ (-p.β) *
            deriv (deriv (intervalDomainLift (v t))) x.1) := by
    simp only [classicalChemDivMPhysicalRep]
    rw [hux0.deriv, hPDE_v x.1 hint]
    ring
  have hcd_eq := intervalDomainMChemotaxisDiv_eq_physicalRep_interior
    hsol ht0 htT hint
  have hcd_nonpos : intervalDomainChemotaxisDivM p (u t) (v t) x ≤ 0 := by
    have hx : (⟨x.1, Set.Ioo_subset_Icc_self hint⟩ : intervalDomainPoint) = x :=
      Subtype.ext rfl
    rw [← hx, hcd_eq, hrep]
    exact mul_nonpos_of_nonneg_of_nonpos
      (Real.rpow_nonneg hM_nonneg _) hG_nonpos
  have huxx := interior_argmax_deriv2_nonpos hmax hint hu_c2
  have hpde' : intervalDomain.timeDeriv u t x =
      deriv (deriv (intervalDomainLift (u t))) x.1 -
        p.χ₀ * intervalDomainChemotaxisDivM p (u t) (v t) x +
          intervalDomainLift (u t) x.1 *
            (p.a - p.b * intervalDomainLift (u t) x.1 ^ p.α) := by
    rw [hux_lift]
    exact hsol.pde_u ht0 htT hint
  exact max_point_estimate hχ huxx hcd_nonpos hpde'

private theorem physicalRep_nonpos_at_neumann_argmax
    {p : CM2Params} {T t e : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (he : e ∈ Set.Icc (0 : ℝ) 1)
    (hdu : deriv (intervalDomainLift (u t)) e = 0)
    (hmaxlift : ∀ y, intervalDomainLift (u t) y ≤
      intervalDomainLift (u t) e) :
    classicalChemDivMPhysicalRep p u v t e ≤ 0 := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, _, _⟩ := hsol.regularity
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t))
      (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).2
  have hv_cont : ContinuousOn (intervalDomainLift (v t))
      (Set.Icc (0 : ℝ) 1) := (hClosed t htmem).2.1.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (hNeu t htmem).2.2
  have hUe_nonneg : 0 ≤ intervalDomainLift (u t) e := by
    simpa [intervalDomainLift, he] using
      (hsol.u_pos' (x := (⟨e, he⟩ : intervalDomainPoint)) ht0 htT).le
  have hVnn : 0 ≤ intervalDomainLift (v t) e := by
    simpa [intervalDomainLift, he] using
      hsol.v_nonneg (x := (⟨e, he⟩ : intervalDomainPoint)) ht0 htT
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y =
        p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ := by
    intro y hy
    have hpv := hsol.pde_v ht0 htT
      (show (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) ∈
        intervalDomainM.inside from hy)
    rw [lift_eq_interior (v t) hy, lift_eq_interior (u t) hy]
    have hlap : intervalDomainM.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) =
          deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  set B : ℝ := p.ν * intervalDomainLift (u t) e ^ p.γ with hBdef
  have hd1 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift (v t)) y := by
    intro y hy
    exact (hv_c2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hy)
  have hd2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y := by
    intro y hy
    exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).2).differentiableAt
  have hSrc : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      |p.ν * intervalDomainLift (u t) y ^ p.γ| ≤ B := by
    intro y hy
    have huy_nn : 0 ≤ intervalDomainLift (u t) y := by
      rw [lift_eq_interior (u t) hy]
      exact (hsol.u_pos' ht0 htT).le
    have hpow : intervalDomainLift (u t) y ^ p.γ ≤
        intervalDomainLift (u t) e ^ p.γ :=
      Real.rpow_le_rpow huy_nn (hmaxlift y) p.hγ.le
    have hnn : 0 ≤ p.ν * intervalDomainLift (u t) y ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg huy_nn _)
    rw [abs_of_nonneg hnn, hBdef]
    exact mul_le_mul_of_nonneg_left hpow p.hν.le
  have hv_bound := elliptic_sup_bound (w := intervalDomainLift (v t))
    (Src := fun y => p.ν * intervalDomainLift (u t) y ^ p.γ)
    (μ := p.μ) (B := B) p.hμ hv_cont hd1 hd2 hPDE_v hSrc hNeu0 hNeu1
  have hμv : p.μ * intervalDomainLift (v t) e ≤ B := by
    have he_bound := hv_bound e he
    rw [mul_comm]
    exact (le_div_iff₀ p.hμ).mp he_bound
  have hreact : p.μ * intervalDomainLift (v t) e -
      p.ν * intervalDomainLift (u t) e ^ p.γ ≤ 0 := by
    rw [← hBdef]
    linarith
  have hG := flux_coeff_nonpos (β := p.β)
    (v := intervalDomainLift (v t) e)
    (vx := deriv (intervalDomainLift (v t)) e)
    (vxx := p.μ * intervalDomainLift (v t) e -
      p.ν * intervalDomainLift (u t) e ^ p.γ)
    p.hβ hVnn hreact
  have hrep : classicalChemDivMPhysicalRep p u v t e =
      intervalDomainLift (u t) e ^ p.m *
        (-p.β * (1 + intervalDomainLift (v t) e) ^ (-p.β - 1) *
            deriv (intervalDomainLift (v t)) e ^ 2 +
          (1 + intervalDomainLift (v t) e) ^ (-p.β) *
            (p.μ * intervalDomainLift (v t) e -
              p.ν * intervalDomainLift (u t) e ^ p.γ)) := by
    simp only [classicalChemDivMPhysicalRep]
    rw [hdu]
    ring
  rw [hrep]
  exact mul_nonpos_of_nonneg_of_nonpos
    (Real.rpow_nonneg hUe_nonneg _) hG

/-- Left-boundary maximum estimate for a faithful general-`m` solution. -/
theorem boundary_max_point_left_M
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmaxlift : ∀ y, intervalDomainLift (u t) y ≤
      intervalDomainLift (u t) 0) :
    deriv (fun r => intervalDomainLift (u r) 0) t ≤
      intervalDomainLift (u t) 0 *
        (p.a - p.b * intervalDomainLift (u t) 0 ^ p.α) := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  have hu_c2 : ContDiffOn ℝ 2 U (Set.Ioo (0 : ℝ) 1) :=
    (hC2 t htmem).1
  have hu_cont : ContinuousOn U (Set.Icc (0 : ℝ) 1) :=
    (hClosed t htmem).1.1.continuousOn
  have hNeuU0 : Tendsto (deriv U) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (hNeu t htmem).1.1
  have hdu0 : deriv U 0 = 0 := (hClosed t htmem).1.2.1
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  set G : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x =>
    U x * (p.a - p.b * U x ^ p.α) with hR_def
  set Cfun : ℝ → ℝ :=
    boundaryChemDivMReal p (u t) (v t) with hCfun_def
  have hfilter : nhdsWithin (0 : ℝ) (Set.Ioo 0 1) =
      nhdsWithin 0 (Set.Ioi 0) := nhdsWithin_Ioo_eq_nhdsGT h01
  have hG_lim : Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds (G 0)) := by
    have hmaps : Set.MapsTo (fun w => (t, w)) (Set.Icc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn G (Set.Icc (0 : ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  have hR_lim : Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds (R 0)) := by
    have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
      hu_cont.mul (continuousOn_const.sub (continuousOn_const.mul
        (hu_cont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcont 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  have hUxx_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    have hpu := hsol.pde_u ht0 htT
      (show (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) ∈
        intervalDomainM.inside from hx)
    have e_td : intervalDomainM.timeDeriv u t
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      show deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) t = G x
      simp only [hG_def]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomainM.laplacian (u t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = deriv (deriv U) x := rfl
    have e_cd : intervalDomainM.chemotaxisDiv p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x := by
      change intervalDomainChemotaxisDivM p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x
      simp [hCfun_def, boundaryChemDivMReal, Set.Ioo_subset_Icc_self hx]
    have e_u : u t (⟨x, Set.Ioo_subset_Icc_self hx⟩ :
        intervalDomainPoint) = U x := by
      rw [hU_def, intervalDomainLift,
        dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu
    rw [hR_def]
    linarith
  set CL : ℝ := classicalChemDivMPhysicalRep p u v t 0 with hCL_def
  have hC_lim : Tendsto Cfun (nhdsWithin 0 (Set.Ioi 0)) (nhds CL) := by
    have hcont := classicalChemDivMPhysicalRep_continuousOn_Icc
      hsol ht0 htT
    have hlim : Tendsto (classicalChemDivMPhysicalRep p u v t)
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (classicalChemDivMPhysicalRep p u v t 0)) :=
      (hcont 0 h0Icc).mono_left
        (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
    have heq : (fun y => boundaryChemDivMReal p (u t) (v t) y) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)]
          classicalChemDivMPhysicalRep p u v t := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [boundaryChemDivMReal,
        dif_pos (Set.Ioo_subset_Icc_self hy)]
      exact intervalDomainMChemotaxisDiv_eq_physicalRep_interior
        hsol ht0 htT hy
    have hlim' := Filter.Tendsto.congr' heq.symm hlim
    rw [hfilter] at hlim'
    simpa [hCfun_def, hCL_def] using hlim'
  have hCL_nonpos : CL ≤ 0 := by
    rw [hCL_def]
    exact physicalRep_nonpos_at_neumann_argmax hsol ht0 htT h0Icc
      hdu0 hmaxlift
  set Vlim : ℝ := G 0 - R 0 + p.χ₀ * CL with hVlim_def
  have hUxx_lim : Tendsto (deriv (deriv U))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Vlim) := by
    refine ((hG_lim.sub hR_lim).add (hC_lim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hUxx_eq x hx).symm
  have hwcont : ContinuousWithinAt U (Set.Ici 0) 0 := by
    refine (hu_cont 0 h0Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0 : ℝ) 1 =
        Set.Ici (0 : ℝ) ∩ Set.Iic 1 := by
      ext z
      simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  have hd1U : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt U (deriv U x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
  have hd2U : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).2
  have hVlim_nonpos : Vlim ≤ 0 :=
    ShenWork.Paper2.Lemma31Closure.boundary_max_deriv2_rlimit_nonpos
      h01 hwcont (fun x hx => hmaxlift x) hd1U hd2U hNeuU0 hUxx_lim
  have hkey : 0 ≤ p.χ₀ * CL := by
    rw [← neg_mul_neg]
    exact mul_nonneg (neg_nonneg.2 hχ) (neg_nonneg.2 hCL_nonpos)
  have hG0 : G 0 = Vlim + R 0 - p.χ₀ * CL := by
    rw [hVlim_def]
    ring
  have hfinal : G 0 ≤ R 0 := by
    rw [hG0]
    linarith
  show G 0 ≤ U 0 * (p.a - p.b * U 0 ^ p.α)
  calc
    G 0 ≤ R 0 := hfinal
    _ = U 0 * (p.a - p.b * U 0 ^ p.α) := by simp only [hR_def]

/-- Right-boundary maximum estimate for a faithful general-`m` solution. -/
theorem boundary_max_point_right_M
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmaxlift : ∀ y, intervalDomainLift (u t) y ≤
      intervalDomainLift (u t) 1) :
    deriv (fun r => intervalDomainLift (u r) 1) t ≤
      intervalDomainLift (u t) 1 *
        (p.a - p.b * intervalDomainLift (u t) 1 ^ p.α) := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  have hu_c2 : ContDiffOn ℝ 2 U (Set.Ioo (0 : ℝ) 1) :=
    (hC2 t htmem).1
  have hu_cont : ContinuousOn U (Set.Icc (0 : ℝ) 1) :=
    (hClosed t htmem).1.1.continuousOn
  have hNeuU1 : Tendsto (deriv U) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) :=
    (hNeu t htmem).1.2
  have hdu1 : deriv U 1 = 0 := (hClosed t htmem).1.2.2
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  set G : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x =>
    U x * (p.a - p.b * U x ^ p.α) with hR_def
  set Cfun : ℝ → ℝ :=
    boundaryChemDivMReal p (u t) (v t) with hCfun_def
  have hfilter : nhdsWithin (1 : ℝ) (Set.Ioo 0 1) =
      nhdsWithin 1 (Set.Iio 1) := nhdsWithin_Ioo_eq_nhdsLT h01
  have hG_lim : Tendsto G (nhdsWithin 1 (Set.Iio 1)) (nhds (G 1)) := by
    have hmaps : Set.MapsTo (fun w => (t, w)) (Set.Icc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn G (Set.Icc (0 : ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hR_lim : Tendsto R (nhdsWithin 1 (Set.Iio 1)) (nhds (R 1)) := by
    have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
      hu_cont.mul (continuousOn_const.sub (continuousOn_const.mul
        (hu_cont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcont 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hUxx_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    have hpu := hsol.pde_u ht0 htT
      (show (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) ∈
        intervalDomainM.inside from hx)
    have e_td : intervalDomainM.timeDeriv u t
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      show deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) t = G x
      simp only [hG_def]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomainM.laplacian (u t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = deriv (deriv U) x := rfl
    have e_cd : intervalDomainM.chemotaxisDiv p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x := by
      change intervalDomainChemotaxisDivM p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x
      simp [hCfun_def, boundaryChemDivMReal, Set.Ioo_subset_Icc_self hx]
    have e_u : u t (⟨x, Set.Ioo_subset_Icc_self hx⟩ :
        intervalDomainPoint) = U x := by
      rw [hU_def, intervalDomainLift,
        dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu
    rw [hR_def]
    linarith
  set CL : ℝ := classicalChemDivMPhysicalRep p u v t 1 with hCL_def
  have hC_lim : Tendsto Cfun (nhdsWithin 1 (Set.Iio 1)) (nhds CL) := by
    have hcont := classicalChemDivMPhysicalRep_continuousOn_Icc
      hsol ht0 htT
    have hlim : Tendsto (classicalChemDivMPhysicalRep p u v t)
        (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1))
        (nhds (classicalChemDivMPhysicalRep p u v t 1)) :=
      (hcont 1 h1Icc).mono_left
        (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
    have heq : (fun y => boundaryChemDivMReal p (u t) (v t) y) =ᶠ[
        nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)]
          classicalChemDivMPhysicalRep p u v t := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [boundaryChemDivMReal,
        dif_pos (Set.Ioo_subset_Icc_self hy)]
      exact intervalDomainMChemotaxisDiv_eq_physicalRep_interior
        hsol ht0 htT hy
    have hlim' := Filter.Tendsto.congr' heq.symm hlim
    rw [hfilter] at hlim'
    simpa [hCfun_def, hCL_def] using hlim'
  have hCL_nonpos : CL ≤ 0 := by
    rw [hCL_def]
    exact physicalRep_nonpos_at_neumann_argmax hsol ht0 htT h1Icc
      hdu1 hmaxlift
  set Vlim : ℝ := G 1 - R 1 + p.χ₀ * CL with hVlim_def
  have hUxx_lim : Tendsto (deriv (deriv U))
      (nhdsWithin 1 (Set.Iio 1)) (nhds Vlim) := by
    refine ((hG_lim.sub hR_lim).add (hC_lim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hUxx_eq x hx).symm
  have hwcont : ContinuousWithinAt U (Set.Iic 1) 1 := by
    refine (hu_cont 1 h1Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0 : ℝ) 1 =
        Set.Ici (0 : ℝ) ∩ Set.Iic 1 := by
      ext z
      simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h01))
      self_mem_nhdsWithin
  have hd1U : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt U (deriv U x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
  have hd2U : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).2
  have hII : Set.Ioo (1 - (1 : ℝ)) 1 = Set.Ioo (0 : ℝ) 1 := by
    rw [sub_self]
  have hVlim_nonpos : Vlim ≤ 0 :=
    ShenWork.Paper2.Lemma31Closure.boundary_max_deriv2_llimit_nonpos
      h01 hwcont
        (by rw [hII]; exact fun x hx => hmaxlift x)
        (by rw [hII]; exact hd1U)
        (by rw [hII]; exact hd2U)
        hNeuU1 hUxx_lim
  have hkey : 0 ≤ p.χ₀ * CL := by
    rw [← neg_mul_neg]
    exact mul_nonneg (neg_nonneg.2 hχ) (neg_nonneg.2 hCL_nonpos)
  have hG1 : G 1 = Vlim + R 1 - p.χ₀ * CL := by
    rw [hVlim_def]
    ring
  have hfinal : G 1 ≤ R 1 := by
    rw [hG1]
    linarith
  show G 1 ≤ U 1 * (p.a - p.b * U 1 ^ p.α)
  calc
    G 1 ≤ R 1 := hfinal
    _ = U 1 * (p.a - p.b * U 1 ^ p.α) := by simp only [hR_def]

/-- Reaction-only slope bound at every spatial maximum. -/
theorem max_point_slope_bound_M
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmax : ∀ y, u t y ≤ u t x) :
    intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
        (p.a - p.b * intervalDomainLift (u t) x.1 ^ p.α) := by
  rcases lt_or_eq_of_le x.2.1 with h0 | h0
  · rcases lt_or_eq_of_le x.2.2 with h1 | h1
    · exact interior_max_point_of_solution_M hχ hsol ht0 htT
        ⟨h0, h1⟩ hmax
    · have hx11 : x.1 = 1 := h1
      have hmaxlift : ∀ y, intervalDomainLift (u t) y ≤
          intervalDomainLift (u t) 1 := by
        intro y
        have hlift1 : intervalDomainLift (u t) 1 = u t x := by
          rw [intervalDomainLift, dif_pos
            (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
              ⟨zero_le_one, le_rfl⟩)]
          exact congrArg (u t) (Subtype.ext hx11.symm)
        rw [hlift1]
        unfold intervalDomainLift
        split_ifs with hy
        · exact hmax ⟨y, hy⟩
        · exact (hsol.u_pos' ht0 htT (x := x)).le
      have hb := boundary_max_point_right_M hχ hsol ht0 htT hmaxlift
      have htd : intervalDomain.timeDeriv u t x =
          deriv (fun r => intervalDomainLift (u r) 1) t := by
        show deriv (fun s => u s x) t =
          deriv (fun r => intervalDomainLift (u r) 1) t
        congr 1
        funext r
        rw [intervalDomainLift, dif_pos
          (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
            ⟨zero_le_one, le_rfl⟩)]
        exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
      rw [hx11, htd]
      exact hb
  · have hx10 : x.1 = 0 := h0.symm
    have hmaxlift : ∀ y, intervalDomainLift (u t) y ≤
        intervalDomainLift (u t) 0 := by
      intro y
      have hlift0 : intervalDomainLift (u t) 0 = u t x := by
        rw [intervalDomainLift, dif_pos
          (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
            ⟨le_rfl, zero_le_one⟩)]
        exact congrArg (u t) (Subtype.ext hx10.symm)
      rw [hlift0]
      unfold intervalDomainLift
      split_ifs with hy
      · exact hmax ⟨y, hy⟩
      · exact (hsol.u_pos' ht0 htT (x := x)).le
    have hb := boundary_max_point_left_M hχ hsol ht0 htT hmaxlift
    have htd : intervalDomain.timeDeriv u t x =
        deriv (fun r => intervalDomainLift (u r) 0) t := by
      show deriv (fun s => u s x) t =
        deriv (fun r => intervalDomainLift (u r) 0) t
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
          ⟨le_rfl, zero_le_one⟩)]
      exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
    rw [hx10, htd]
    exact hb

end ShenWork.Paper2.IntervalDomainMChiNonpos
