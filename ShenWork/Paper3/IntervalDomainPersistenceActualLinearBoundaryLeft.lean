import ShenWork.Paper3.IntervalDomainPersistenceActualLinearTheta
import ShenWork.Paper2.IntervalLemma31Closure
open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.MinPersistenceAtoms
open Set Filter Topology
namespace ShenWork.Paper3
noncomputable section
set_option maxHeartbeats 1600000 in
theorem intervalDomain_actualLinear_boundary_min_point_left
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hminlift : ∀ y ∈ Set.Ioo (0 : ℝ) 1, intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y) :
    actualLinearLogisticRhs p (intervalDomainLift (u t) 0) ≤
      deriv (fun r => intervalDomainLift (u r) 0) t := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  set Vv : ℝ → ℝ := intervalDomainLift (v t) with hVv_def
  have hu_c2 : ContDiffOn ℝ 2 U (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 Vv (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).2
  have hu_cont_Icc : ContinuousOn U (Set.Icc (0 : ℝ) 1) := (hClosed t htmem).1.1.continuousOn
  have hv_cont_Icc : ContinuousOn Vv (Set.Icc (0 : ℝ) 1) := (hClosed t htmem).2.1.continuousOn
  have hNeuU0 : Tendsto (deriv U) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).1.1
  have hNeuV0 : Tendsto (deriv Vv) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).2.1
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hU0_pos : 0 < U 0 := by rw [hU_def, intervalDomainLift, dif_pos h0Icc]; exact hsol.u_pos' ht0 htT
  have hv_nn : ∀ y, 0 ≤ Vv y := by
    intro y; rw [hVv_def]; unfold intervalDomainLift
    split_ifs with hy <;> first | exact hsol.v_nonneg ht0 htT | exact le_refl 0
  have hpos_v : ∀ y, (0 : ℝ) < 1 + Vv y := fun y => by linarith [hv_nn y]
  set G : ℝ → ℝ := fun x => deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x => U x * (p.a - p.b * (U x) ^ p.α) with hR_def
  set Cfun : ℝ → ℝ := fun x => deriv (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β) x with hCfun_def
  have hfilter : nhdsWithin (0 : ℝ) (Set.Ioo 0 1) = nhdsWithin 0 (Set.Ioi 0) := nhdsWithin_Ioo_eq_nhdsGT h01
  have hG_lim : Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds (G 0)) := by
    have hmaps : Set.MapsTo (fun w => (t, w)) (Set.Icc (0 : ℝ) 1) (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn G (Set.Icc (0 : ℝ) 1) := hJDt.1.comp (Continuous.continuousOn (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]; exact (hcomp 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  have hR_lim : Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds (R 0)) := by
    have hRcontOn : ContinuousOn R (Set.Icc (0 : ℝ) 1) := hu_cont_Icc.mul (continuousOn_const.sub (continuousOn_const.mul (hu_cont_Icc.rpow_const (fun x _ => Or.inr p.hα.le))))
    rw [← hfilter]; exact (hRcontOn 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  have hUxx_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx; have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) ∈ intervalDomain.inside := hx; have hpu := hsol.pde_u ht0 htT hmem
    have e_td : intervalDomain.timeDeriv u t ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by show deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) t = G x; simp only [hG_def]; congr 1; funext r; rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomain.laplacian (u t) ⟨x, Set.Ioo_subset_Icc_self hx⟩ = deriv (deriv U) x := rfl
    have e_cd : intervalDomain.chemotaxisDiv p (u t) (v t) ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x := rfl
    have e_u : u t (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = U x := by rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu; rw [hR_def]; linarith [hpu]
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1, deriv (deriv Vv) y = p.μ * Vv y - p.ν * (U y) ^ p.γ := by
    intro y hy; have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) ∈ intervalDomain.inside := hy; have hpv := hsol.pde_v ht0 htT hxy
    have e_lap : intervalDomain.laplacian (v t) ⟨y, Set.Ioo_subset_Icc_self hy⟩ = deriv (deriv Vv) y := rfl
    have e_u : u t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) = U y := by rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    have e_v : v t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) = Vv y := by rw [hVv_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    rw [e_lap, e_u, e_v] at hpv; linarith [hpv]
  set CL : ℝ := 0 * (0 * (1 + Vv 0) ^ (-p.β)) + U 0 * (-p.β * (1 + Vv 0) ^ (-p.β - 1) * (0 : ℝ) ^ 2 + (1 + Vv 0) ^ (-p.β) * (p.μ * Vv 0 - p.ν * (U 0) ^ p.γ)) with hCL_def
  have hCexpr : ∀ x ∈ Set.Ioo (0 : ℝ) 1, Cfun x = deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β)) + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 + (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * (U x) ^ p.γ)) := by
    intro x hx; have hUx : HasDerivAt U (deriv U x) x := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1; have hVx : HasDerivAt Vv (deriv Vv x) x := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).1; have hVxx : HasDerivAt (deriv Vv) (deriv (deriv Vv) x) x := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).2
    have hP' : HasDerivAt (fun y => deriv Vv y * (1 + Vv y) ^ (-p.β)) (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 + (1 + Vv x) ^ (-p.β) * (deriv (deriv Vv) x)) x := flux_integrand_hasDerivAt hVx hVxx (hpos_v x)
    have hFeq2 : (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β) = (fun y => U y * (deriv Vv y * (1 + Vv y) ^ (-p.β))) := by funext y; rw [mul_div_assoc, Real.rpow_neg (hpos_v y).le, div_eq_mul_inv]
    have hCfx : Cfun x = deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β)) + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 + (1 + Vv x) ^ (-p.β) * (deriv (deriv Vv) x)) := by simp only [hCfun_def]; rw [hFeq2]; exact (hUx.mul hP').deriv
    rw [hCfx, hPDE_v x hx]
  have hU0L : Tendsto U (nhdsWithin 0 (Set.Ioi 0)) (nhds (U 0)) := by have h := (hu_cont_Icc 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self); rwa [hfilter] at h
  have hVv0L : Tendsto Vv (nhdsWithin 0 (Set.Ioi 0)) (nhds (Vv 0)) := by have h := (hv_cont_Icc 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self); rwa [hfilter] at h
  have h1Vv0L : Tendsto (fun x => 1 + Vv x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 + Vv 0)) := hVv0L.const_add 1
  have hrpb : Tendsto (fun x => (1 + Vv x) ^ (-p.β)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 + Vv 0) ^ (-p.β))) := h1Vv0L.rpow_const (Or.inl (ne_of_gt (hpos_v 0)))
  have hrpb1 : Tendsto (fun x => (1 + Vv x) ^ (-p.β - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 + Vv 0) ^ (-p.β - 1))) := h1Vv0L.rpow_const (Or.inl (ne_of_gt (hpos_v 0)))
  have hUg : Tendsto (fun x => (U x) ^ p.γ) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((U 0) ^ p.γ)) := hU0L.rpow_const (Or.inl (ne_of_gt hU0_pos))
  have hexpr : Tendsto (fun x => deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β)) + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 + (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * (U x) ^ p.γ))) (nhdsWithin 0 (Set.Ioi 0)) (nhds CL) := by
    have hsum := (hNeuU0.mul (hNeuV0.mul hrpb)).add (hU0L.mul ((((tendsto_const_nhds (x := -p.β)).mul hrpb1).mul (hNeuV0.pow 2)).add (hrpb.mul ((hVv0L.const_mul p.μ).sub (hUg.const_mul p.ν)))))
    rw [hCL_def]; exact hsum
  have hC_lim : Tendsto Cfun (nhdsWithin 0 (Set.Ioi 0)) (nhds CL) := by
    refine hexpr.congr' ?_; rw [← hfilter]; filter_upwards [self_mem_nhdsWithin] with x hx; exact (hCexpr x hx).symm
  have hCL_le : CL ≤ U 0 * (p.μ * Theta_beta (p.β - 1)) := by
    have hden_nonneg : 0 ≤ (1 + Vv 0) ^ (-p.β) := Real.rpow_nonneg (by linarith [hv_nn 0] : 0 ≤ 1 + Vv 0) _
    have hUγ_nonneg : 0 ≤ (U 0) ^ p.γ := Real.rpow_nonneg hU0_pos.le _
    have hdrop : (1 + Vv 0) ^ (-p.β) * (p.μ * Vv 0 - p.ν * (U 0) ^ p.γ) ≤ (1 + Vv 0) ^ (-p.β) * (p.μ * Vv 0) := mul_le_mul_of_nonneg_left (by have : 0 ≤ p.ν * (U 0) ^ p.γ := mul_nonneg p.hν.le hUγ_nonneg; linarith) hden_nonneg
    have hpow_eq : (1 + Vv 0) ^ (-p.β) * (p.μ * Vv 0) = p.μ * (Vv 0 / (1 + Vv 0) ^ p.β) := by rw [Real.rpow_neg (le_of_lt (by linarith [hv_nn 0] : 0 < 1 + Vv 0))]; ring
    have hsecond : (1 + Vv 0) ^ (-p.β) * (p.μ * Vv 0 - p.ν * (U 0) ^ p.γ) ≤ p.μ * Theta_beta (p.β - 1) := by
      exact hdrop.trans (by rw [hpow_eq]; exact mul_le_mul_of_nonneg_left (theta_linear_bound_public (p := p) hβ (hv_nn 0)) p.hμ.le)
    rw [hCL_def]; norm_num; exact mul_le_mul_of_nonneg_left hsecond hU0_pos.le
  set Vlim : ℝ := G 0 - R 0 + p.χ₀ * CL with hVlim_def
  have hUxx_lim : Tendsto (deriv (deriv U)) (nhdsWithin 0 (Set.Ioi 0)) (nhds Vlim) := by refine ((hG_lim.sub hR_lim).add (hC_lim.const_mul p.χ₀)).congr' ?_; rw [← hfilter]; filter_upwards [self_mem_nhdsWithin] with x hx using (hUxx_eq x hx).symm
  have hwcont : ContinuousWithinAt U (Set.Ici 0) 0 := by
    refine (hu_cont_Icc 0 h0Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0 : ℝ) 1 = Set.Ici (0 : ℝ) ∩ Set.Iic 1 := by ext z; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]; exact Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  have hd1U : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (deriv U x) x := fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
  have hd2U : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (deriv U) (deriv (deriv U) x) x := fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).2
  have hVlim_nonneg : 0 ≤ Vlim := boundary_min_deriv2_rlimit_nonneg h01 hwcont (fun x hx => hminlift x hx) hd1U hd2U hNeuU0 hUxx_lim
  have hG0 : G 0 = Vlim + R 0 - p.χ₀ * CL := by rw [hVlim_def]; ring
  have hchem : -p.χ₀ * (U 0 * (p.μ * Theta_beta (p.β - 1))) ≤ -p.χ₀ * CL := mul_le_mul_of_nonpos_left hCL_le (by linarith : -p.χ₀ ≤ 0)
  have hpow : U 0 * (p.b * (U 0) ^ p.α) = p.b * (U 0) ^ (1 + p.α) := by rw [Real.rpow_add_of_nonneg hU0_pos.le (by norm_num : 0 ≤ (1 : ℝ)) p.hα.le, Real.rpow_one]; ring
  rw [show deriv (fun r => intervalDomainLift (u r) 0) t = G 0 from rfl, hG0]
  simp only [actualLinearLogisticRhs, actualLinearChemLoss, hR_def]
  nlinarith [hVlim_nonneg, hchem, hpow]
end
end ShenWork.Paper3
#print axioms ShenWork.Paper3.intervalDomain_actualLinear_boundary_min_point_left
