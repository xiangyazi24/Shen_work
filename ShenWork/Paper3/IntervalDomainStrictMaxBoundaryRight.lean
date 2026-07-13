import ShenWork.Paper3.IntervalDomainSolutionPowerResolverGap
import ShenWork.Paper2.IntervalLemma31Closure

open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.MinPersistenceAtoms
open Set Filter Topology

namespace ShenWork.Paper3

noncomputable section

/- At a right-boundary spatial maximum, a quantitative elliptic signal gap
is retained as a strictly dissipative chemotaxis term. -/
set_option maxHeartbeats 1600000 in
theorem intervalDomain_boundary_max_point_right_strict_signal
    {p : CM2Params} {T t q : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmaxlift : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1)
    (hsignal : q ≤
      p.ν * (intervalDomainLift (u t) 1) ^ p.γ / p.μ -
        intervalDomainLift (v t) 1) :
    deriv (fun r => intervalDomainLift (u r) 1) t ≤
      intervalDomainLift (u t) 1 *
          (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) +
        p.χ₀ *
          (intervalDomainLift (u t) 1 *
            ((1 + intervalDomainLift (v t) 1) ^ (-p.β) * (p.μ * q))) := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  set Vv : ℝ → ℝ := intervalDomainLift (v t) with hVv_def
  have hu_c2 : ContDiffOn ℝ 2 U (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 Vv (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).2
  have hu_cont_Icc : ContinuousOn U (Set.Icc (0 : ℝ) 1) :=
    (hClosed t htmem).1.1.continuousOn
  have hv_cont_Icc : ContinuousOn Vv (Set.Icc (0 : ℝ) 1) :=
    (hClosed t htmem).2.1.continuousOn
  have hNeuU1 : Tendsto (deriv U) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) :=
    (hNeu t htmem).1.2
  have hNeuV1 : Tendsto (deriv Vv) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) :=
    (hNeu t htmem).2.2
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hU1_pos : 0 < U 1 := by
    rw [hU_def, intervalDomainLift, dif_pos h1Icc]
    exact hsol.u_pos' ht0 htT
  have hv_nn : ∀ y, 0 ≤ Vv y := by
    intro y
    rw [hVv_def]
    unfold intervalDomainLift
    split_ifs with hy
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hpos_v : ∀ y, 0 < 1 + Vv y := fun y => by linarith [hv_nn y]
  set G : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x => U x * (p.a - p.b * U x ^ p.α) with hR_def
  set Cfun : ℝ → ℝ := fun x =>
    deriv (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β) x with hCfun_def
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
    have hRcontOn : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
      hu_cont_Icc.mul (continuousOn_const.sub
        (continuousOn_const.mul
          (hu_cont_Icc.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcontOn 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hUxx_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) ∈
        intervalDomain.inside := hx
    have hpu := hsol.pde_u ht0 htT hmem
    have e_td : intervalDomain.timeDeriv u t
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      show deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) t = G x
      simp only [hG_def]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomain.laplacian (u t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = deriv (deriv U) x := rfl
    have e_cd : intervalDomain.chemotaxisDiv p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x := rfl
    have e_u : u t (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) =
        U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu
    rw [hR_def]
    linarith [hpu]
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv Vv) y = p.μ * Vv y - p.ν * U y ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) ∈
        intervalDomain.inside := hy
    have hpv := hsol.pde_v ht0 htT hxy
    have e_lap : intervalDomain.laplacian (v t)
        ⟨y, Set.Ioo_subset_Icc_self hy⟩ = deriv (deriv Vv) y := rfl
    have e_u : u t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) =
        U y := by
      rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    have e_v : v t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) =
        Vv y := by
      rw [hVv_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    rw [e_lap, e_u, e_v] at hpv
    linarith [hpv]
  set CL : ℝ :=
    0 * (0 * (1 + Vv 1) ^ (-p.β)) +
      U 1 * (-p.β * (1 + Vv 1) ^ (-p.β - 1) * (0 : ℝ) ^ 2 +
        (1 + Vv 1) ^ (-p.β) * (p.μ * Vv 1 - p.ν * U 1 ^ p.γ))
    with hCL_def
  have hCexpr : ∀ x ∈ Set.Ioo (0 : ℝ) 1, Cfun x =
      deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β)) +
        U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 +
          (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * U x ^ p.γ)) := by
    intro x hx
    have hUx : HasDerivAt U (deriv U x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
    have hVx : HasDerivAt Vv (deriv Vv x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).1
    have hVxx : HasDerivAt (deriv Vv) (deriv (deriv Vv) x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).2
    have hP' : HasDerivAt
        (fun y => deriv Vv y * (1 + Vv y) ^ (-p.β))
        (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 +
          (1 + Vv x) ^ (-p.β) * deriv (deriv Vv) x) x :=
      flux_integrand_hasDerivAt hVx hVxx (hpos_v x)
    have hFeq : (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β) =
        (fun y => U y * (deriv Vv y * (1 + Vv y) ^ (-p.β))) := by
      funext y
      rw [mul_div_assoc, Real.rpow_neg (hpos_v y).le, div_eq_mul_inv]
    have hCfx : Cfun x =
        deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β)) +
          U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 +
            (1 + Vv x) ^ (-p.β) * deriv (deriv Vv) x) := by
      simp only [hCfun_def]
      rw [hFeq]
      exact (hUx.mul hP').deriv
    rw [hCfx, hPDE_v x hx]
  have hU1L : Tendsto U (nhdsWithin 1 (Set.Iio 1)) (nhds (U 1)) := by
    have h := (hu_cont_Icc 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have hVv1L : Tendsto Vv (nhdsWithin 1 (Set.Iio 1)) (nhds (Vv 1)) := by
    have h := (hv_cont_Icc 1 h1Icc).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have h1Vv1L : Tendsto (fun x => 1 + Vv x) (nhdsWithin 1 (Set.Iio 1))
      (nhds (1 + Vv 1)) := hVv1L.const_add 1
  have hrpb : Tendsto (fun x => (1 + Vv x) ^ (-p.β))
      (nhdsWithin 1 (Set.Iio 1)) (nhds ((1 + Vv 1) ^ (-p.β))) :=
    h1Vv1L.rpow_const (Or.inl (ne_of_gt (hpos_v 1)))
  have hrpb1 : Tendsto (fun x => (1 + Vv x) ^ (-p.β - 1))
      (nhdsWithin 1 (Set.Iio 1)) (nhds ((1 + Vv 1) ^ (-p.β - 1))) :=
    h1Vv1L.rpow_const (Or.inl (ne_of_gt (hpos_v 1)))
  have hUg : Tendsto (fun x => U x ^ p.γ) (nhdsWithin 1 (Set.Iio 1))
      (nhds (U 1 ^ p.γ)) :=
    hU1L.rpow_const (Or.inl (ne_of_gt hU1_pos))
  have hexpr : Tendsto
      (fun x => deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β)) +
        U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2 +
          (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * U x ^ p.γ)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds CL) := by
    have hsum := (hNeuU1.mul (hNeuV1.mul hrpb)).add
      (hU1L.mul
        ((((tendsto_const_nhds (x := -p.β)).mul hrpb1).mul (hNeuV1.pow 2)).add
          (hrpb.mul ((hVv1L.const_mul p.μ).sub (hUg.const_mul p.ν)))))
    rw [hCL_def]
    exact hsum
  have hC_lim : Tendsto Cfun (nhdsWithin 1 (Set.Iio 1)) (nhds CL) := by
    refine hexpr.congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hCexpr x hx).symm
  let cActual : ℝ := U 1 * ((1 + Vv 1) ^ (-p.β) * (p.μ * q))
  have hfactor : p.μ * Vv 1 - p.ν * U 1 ^ p.γ ≤ -p.μ * q := by
    have hmul := mul_le_mul_of_nonneg_left hsignal p.hμ.le
    have hcancel : p.μ * (p.ν * U 1 ^ p.γ / p.μ) =
        p.ν * U 1 ^ p.γ := by field_simp [ne_of_gt p.hμ]
    rw [mul_sub, hcancel] at hmul
    linarith
  have hCL_le : CL ≤ -cActual := by
    have hden : 0 ≤ (1 + Vv 1) ^ (-p.β) :=
      Real.rpow_nonneg (by linarith [hv_nn 1] : 0 ≤ 1 + Vv 1) _
    have hinner := mul_le_mul_of_nonneg_left hfactor hden
    have houter := mul_le_mul_of_nonneg_left hinner hU1_pos.le
    rw [hCL_def]
    norm_num
    dsimp [cActual]
    nlinarith
  set Vlim : ℝ := G 1 - R 1 + p.χ₀ * CL with hVlim_def
  have hUxx_lim : Tendsto (deriv (deriv U)) (nhdsWithin 1 (Set.Iio 1))
      (nhds Vlim) := by
    refine ((hG_lim.sub hR_lim).add (hC_lim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hUxx_eq x hx).symm
  have hwcont : ContinuousWithinAt U (Set.Iic 1) 1 := by
    refine (hu_cont_Icc 1 h1Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0 : ℝ) 1 = Set.Ici (0 : ℝ) ∩ Set.Iic 1 := by
      ext z
      simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h01)) self_mem_nhdsWithin
  have hd1U : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt U (deriv U x) x := fun x hx =>
    (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
  have hd2U : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x := fun x hx =>
    (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).2
  have hII : Set.Ioo (1 - (1 : ℝ)) 1 = Set.Ioo (0 : ℝ) 1 := by rw [sub_self]
  have hVlim_nonpos : Vlim ≤ 0 :=
    Lemma31Closure.boundary_max_deriv2_llimit_nonpos (η := 1) h01 hwcont
      (by rw [hII]; exact fun x hx => hmaxlift x hx)
      (by rw [hII]; exact hd1U) (by rw [hII]; exact hd2U)
      hNeuU1 hUxx_lim
  have hG1 : G 1 = Vlim + R 1 - p.χ₀ * CL := by
    rw [hVlim_def]
    ring
  have hchem : -p.χ₀ * CL ≤ p.χ₀ * cActual := by
    have hmul := mul_le_mul_of_nonneg_left hCL_le (by linarith : 0 ≤ -p.χ₀)
    dsimp [cActual] at *
    nlinarith
  rw [show deriv (fun r => intervalDomainLift (u r) 1) t = G 1 from rfl, hG1]
  simp only [hR_def, hU_def, hVv_def]
  dsimp [cActual] at hchem
  nlinarith

#print axioms intervalDomain_boundary_max_point_right_strict_signal

end

end ShenWork.Paper3
