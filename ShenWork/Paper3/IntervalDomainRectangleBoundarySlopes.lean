import ShenWork.Paper3.IntervalDomainRectangleInteriorSlopes
import ShenWork.Paper2.IntervalLemma31Closure

/-!
# Boundary slope bounds for the interval rectangle argument

The parabolic equation is stated on the open interval, so its endpoint use
requires a one-sided limit argument.  We first prove the exact endpoint
balance, using the Neumann limits and the existing one-sided second-derivative
closure.  The concrete signal order bounds then give the rectangle slopes.
-/

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.PDE ShenWork.Paper2
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

private theorem boundary_weighted_factor_lower
    {β V z D : ℝ} (hβ : 0 ≤ β) (hV : 0 ≤ V)
    (hD : 0 ≤ D) (hz : -D ≤ z) :
    -D ≤ (1 + V) ^ (-β) * z := by
  have hφ0 : 0 ≤ (1 + V) ^ (-β) := Real.rpow_nonneg (by linarith) _
  have hφ1 : (1 + V) ^ (-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  by_cases hz0 : 0 ≤ z
  · have hzero : -D ≤ 0 := by linarith
    exact hzero.trans (mul_nonneg hφ0 hz0)
  · have hm := mul_le_mul_of_nonpos_right hφ1 (le_of_not_ge hz0)
    exact hz.trans (by simpa using hm)

private theorem boundary_weighted_factor_upper
    {β V z D : ℝ} (hβ : 0 ≤ β) (hV : 0 ≤ V)
    (hD : 0 ≤ D) (hz : z ≤ D) :
    (1 + V) ^ (-β) * z ≤ D := by
  have hφ0 : 0 ≤ (1 + V) ^ (-β) := Real.rpow_nonneg (by linarith) _
  have hφ1 : (1 + V) ^ (-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  by_cases hz0 : z ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hφ0 hz0).trans hD
  · have hm := mul_le_mul_of_nonneg_right hφ1 (le_of_not_ge hz0)
    have hmul : (1 + V) ^ (-β) * z ≤ z := by simpa using hm
    exact hmul.trans hz

private theorem boundary_weighted_factor_lower_of_weight
    {β V z D q : ℝ} (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hD : 0 ≤ D) (hφq : (1 + V) ^ (-β) ≤ q) (hz : -D ≤ z) :
    -q * D ≤ (1 + V) ^ (-β) * z := by
  have hφ0 : 0 ≤ (1 + V) ^ (-β) :=
    Real.rpow_nonneg (by linarith) _
  by_cases hz0 : 0 ≤ z
  · exact (by nlinarith [mul_nonneg hq hD] : -q * D ≤ 0).trans
      (mul_nonneg hφ0 hz0)
  · have hqz : q * z ≤ (1 + V) ^ (-β) * z := by
      simpa using mul_le_mul_of_nonpos_right hφq (le_of_not_ge hz0)
    have hDz : -q * D ≤ q * z := by
      have hm := mul_le_mul_of_nonneg_left hz hq
      nlinarith
    exact hDz.trans hqz

private theorem boundary_weighted_factor_upper_of_weight
    {β V z D q : ℝ} (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hD : 0 ≤ D) (hφq : (1 + V) ^ (-β) ≤ q) (hz : z ≤ D) :
    (1 + V) ^ (-β) * z ≤ q * D := by
  have hφ0 : 0 ≤ (1 + V) ^ (-β) :=
    Real.rpow_nonneg (by linarith) _
  by_cases hz0 : z ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hφ0 hz0).trans
      (mul_nonneg hq hD)
  · have hφz : (1 + V) ^ (-β) * z ≤ q * z := by
      simpa using mul_le_mul_of_nonneg_right hφq (le_of_not_ge hz0)
    exact hφz.trans (mul_le_mul_of_nonneg_left hz hq)

set_option maxHeartbeats 1600000 in
/-- Exact left-endpoint balance.  At a boundary maximum the time slope is at
most reaction minus the limiting chemotaxis term; at a boundary minimum the
reverse inequality holds. -/
theorem intervalDomain_rectangle_boundary_left_balance
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ((∀ y ∈ Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0) →
      deriv (fun r => intervalDomainLift (u r) 0) t ≤
        intervalDomainLift (u t) 0 *
            (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) -
          p.χ₀ * intervalDomainLift (u t) 0 *
            ((1 + intervalDomainLift (v t) 0) ^ (-p.β) *
              (p.μ * intervalDomainLift (v t) 0 -
                p.ν * (intervalDomainLift (u t) 0) ^ p.γ))) ∧
    ((∀ y ∈ Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y) →
      intervalDomainLift (u t) 0 *
            (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) -
          p.χ₀ * intervalDomainLift (u t) 0 *
            ((1 + intervalDomainLift (v t) 0) ^ (-p.β) *
              (p.μ * intervalDomainLift (v t) 0 -
                p.ν * (intervalDomainLift (u t) 0) ^ p.γ)) ≤
        deriv (fun r => intervalDomainLift (u r) 0) t) := by
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  set V : ℝ → ℝ := intervalDomainLift (v t) with hV_def
  have huC2 : ContDiffOn ℝ 2 U (Ioo (0 : ℝ) 1) := (hC2 t ht).1
  have hvC2 : ContDiffOn ℝ 2 V (Ioo (0 : ℝ) 1) := (hC2 t ht).2
  have huCont : ContinuousOn U (Icc (0 : ℝ) 1) :=
    (hClosed t ht).1.1.continuousOn
  have hvCont : ContinuousOn V (Icc (0 : ℝ) 1) :=
    (hClosed t ht).2.1.continuousOn
  have hNeuU : Tendsto (deriv U) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (hNeu t ht).1.1
  have hNeuV : Tendsto (deriv V) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (hNeu t ht).2.1
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hUpos : 0 < U 0 := by
    rw [hU_def, intervalDomainLift, dif_pos h0]
    exact hsol.u_pos' ht.1 ht.2
  have hvnn : ∀ y, 0 ≤ V y := by
    intro y
    rw [hV_def]
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht.1 ht.2
    · exact le_rfl
  have hposV : ∀ y, 0 < 1 + V y := fun y => by linarith [hvnn y]
  set G : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x => U x * (p.a - p.b * U x ^ p.α) with hR_def
  set Cfun : ℝ → ℝ := fun x =>
    deriv (fun y => U y * deriv V y / (1 + V y) ^ p.β) x with hCfun_def
  have hfilter : nhdsWithin (0 : ℝ) (Ioo 0 1) =
      nhdsWithin 0 (Ioi 0) := nhdsWithin_Ioo_eq_nhdsGT h01
  have hGlim : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds (G 0)) := by
    have hmaps : MapsTo (fun w => (t, w)) (Icc (0 : ℝ) 1)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := fun w hw => ⟨ht, hw⟩
    have hcomp : ContinuousOn G (Icc (0 : ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 0 h0).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  have hRlim : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds (R 0)) := by
    have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) :=
      huCont.mul (continuousOn_const.sub
        (continuousOn_const.mul
          (huCont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcont 0 h0).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
  have hUxxEq : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Ioo_subset_Icc_self hx⟩
    have hpde := hsol.pde_u ht.1 ht.2 (x := xp) hx
    have etd : intervalDomain.timeDeriv u t xp = G x := by
      show deriv (fun r => u r xp) t = G x
      simp only [hG_def]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    have elap : intervalDomain.laplacian (u t) xp = deriv (deriv U) x := rfl
    have echem : intervalDomain.chemotaxisDiv p (u t) (v t) xp = Cfun x := rfl
    have eu : u t xp = U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    rw [etd, elap, echem, eu] at hpde
    rw [hR_def]
    linarith
  have hVxxEq : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Ioo_subset_Icc_self hx⟩
    have hpde := hsol.pde_v ht.1 ht.2 (x := xp) hx
    have elap : intervalDomain.laplacian (v t) xp = deriv (deriv V) x := rfl
    have eu : u t xp = U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    have ev : v t xp = V x := by
      rw [hV_def, intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    rw [elap, eu, ev] at hpde
    linarith
  set CL : ℝ := U 0 * ((1 + V 0) ^ (-p.β) *
    (p.μ * V 0 - p.ν * U 0 ^ p.γ)) with hCL_def
  have hCexpr : ∀ x ∈ Ioo (0 : ℝ) 1,
      Cfun x =
        deriv U x * (deriv V x * (1 + V x) ^ (-p.β)) +
          U x * (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
            (1 + V x) ^ (-p.β) *
              (p.μ * V x - p.ν * U x ^ p.γ)) := by
    intro x hx
    have hUx := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).1
    have hVx := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hvC2 hx).1
    have hVxx := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hvC2 hx).2
    have hP : HasDerivAt
        (fun y => deriv V y * (1 + V y) ^ (-p.β))
        (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
          (1 + V x) ^ (-p.β) * deriv (deriv V) x) x :=
      flux_integrand_hasDerivAt hVx hVxx (hposV x)
    have hFeq : (fun y => U y * deriv V y / (1 + V y) ^ p.β) =
        (fun y => U y * (deriv V y * (1 + V y) ^ (-p.β))) := by
      funext y
      rw [mul_div_assoc, Real.rpow_neg (hposV y).le, div_eq_mul_inv]
    have hCx : Cfun x =
        deriv U x * (deriv V x * (1 + V x) ^ (-p.β)) +
          U x * (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
            (1 + V x) ^ (-p.β) * deriv (deriv V) x) := by
      simp only [hCfun_def]
      rw [hFeq]
      exact (hUx.mul hP).deriv
    rw [hCx, hVxxEq x hx]
  have hUlim : Tendsto U (nhdsWithin 0 (Ioi 0)) (nhds (U 0)) := by
    have h := (huCont 0 h0).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have hVlim : Tendsto V (nhdsWithin 0 (Ioi 0)) (nhds (V 0)) := by
    have h := (hvCont 0 h0).mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have h1Vlim : Tendsto (fun x => 1 + V x) (nhdsWithin 0 (Ioi 0))
      (nhds (1 + V 0)) := hVlim.const_add 1
  have hpowβ : Tendsto (fun x => (1 + V x) ^ (-p.β))
      (nhdsWithin 0 (Ioi 0)) (nhds ((1 + V 0) ^ (-p.β))) :=
    h1Vlim.rpow_const (Or.inl (ne_of_gt (hposV 0)))
  have hpowβ1 : Tendsto (fun x => (1 + V x) ^ (-p.β - 1))
      (nhdsWithin 0 (Ioi 0)) (nhds ((1 + V 0) ^ (-p.β - 1))) :=
    h1Vlim.rpow_const (Or.inl (ne_of_gt (hposV 0)))
  have hpowγ : Tendsto (fun x => U x ^ p.γ) (nhdsWithin 0 (Ioi 0))
      (nhds (U 0 ^ p.γ)) :=
    hUlim.rpow_const (Or.inl (ne_of_gt hUpos))
  have hexpr : Tendsto
      (fun x =>
        deriv U x * (deriv V x * (1 + V x) ^ (-p.β)) +
          U x * (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
            (1 + V x) ^ (-p.β) *
              (p.μ * V x - p.ν * U x ^ p.γ)))
      (nhdsWithin 0 (Ioi 0)) (nhds CL) := by
    have hsum := (hNeuU.mul (hNeuV.mul hpowβ)).add
      (hUlim.mul
        ((((tendsto_const_nhds (x := -p.β)).mul hpowβ1).mul
            (hNeuV.pow 2)).add
          (hpowβ.mul
            ((hVlim.const_mul p.μ).sub (hpowγ.const_mul p.ν)))))
    rw [hCL_def]
    simpa using hsum
  have hClim : Tendsto Cfun (nhdsWithin 0 (Ioi 0)) (nhds CL) := by
    refine hexpr.congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hCexpr x hx).symm
  set W : ℝ := G 0 - R 0 + p.χ₀ * CL with hW_def
  have hUxxLim : Tendsto (deriv (deriv U)) (nhdsWithin 0 (Ioi 0))
      (nhds W) := by
    refine ((hGlim.sub hRlim).add (hClim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hUxxEq x hx).symm
  have hUwithin : ContinuousWithinAt U (Ici 0) 0 := by
    refine (huCont 0 h0).mono_of_mem_nhdsWithin ?_
    have hIcc : Icc (0 : ℝ) 1 = Ici (0 : ℝ) ∩ Iic 1 := by
      ext z
      simp [mem_Icc, mem_Ici, mem_Iic]
    rw [hIcc]
    exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  have hd1 : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt U (deriv U x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).1
  have hd2 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).2
  have hG : G 0 = W + R 0 - p.χ₀ * CL := by
    rw [hW_def]
    ring
  constructor
  · intro hmax
    have hWle : W ≤ 0 :=
      Lemma31Closure.boundary_max_deriv2_rlimit_nonpos h01 hUwithin
        hmax hd1 hd2 hNeuU hUxxLim
    rw [show deriv (fun r => intervalDomainLift (u r) 0) t = G 0 from rfl,
      hG]
    simp only [hR_def, hCL_def, hU_def, hV_def]
    linarith
  · intro hmin
    have hWge : 0 ≤ W :=
      boundary_min_deriv2_rlimit_nonneg h01 hUwithin
        hmin hd1 hd2 hNeuU hUxxLim
    rw [show deriv (fun r => intervalDomainLift (u r) 0) t = G 0 from rfl,
      hG]
    simp only [hR_def, hCL_def, hU_def, hV_def]
    linarith

/-- Left-boundary maximum slope under a uniform sensitivity-weight bound. -/
theorem intervalDomain_rectangle_boundary_left_max_slope_with_weight
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (q : ℝ) (hq : 0 ≤ q)
    (hweight : (1 + intervalDomainLift (v t) 0) ^ (-p.β) ≤ q)
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      uMin ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0) :
    deriv (fun r => intervalDomainLift (u r) 0) t ≤
      intervalDomainLift (u t) 0 *
          (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) +
        p.χ₀ * intervalDomainLift (u t) 0 *
          (q * (p.ν * ((intervalDomainLift (u t) 0) ^ p.γ - uMin ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * ((intervalDomainLift (u t) 0) ^ p.γ -
                uMin ^ p.γ))) ^ 2)) := by
  let U := intervalDomainLift (u t) 0
  let V := intervalDomainLift (v t) 0
  let D := p.ν * (U ^ p.γ - uMin ^ p.γ)
  let L := unitIntervalResolverGradientOscillationConstant p * D
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hUpos : 0 < U := by
    dsimp [U]
    rw [intervalDomainLift, dif_pos h0]
    exact hsol.u_pos' ht.1 ht.2
  have hD : 0 ≤ D := by
    have hp := Real.rpow_le_rpow huMin (hlo 0 h0) p.hγ.le
    exact mul_nonneg p.hν.le (sub_nonneg.mpr hp)
  have hL : 0 ≤ L := mul_nonneg
    (unitIntervalResolverGradientOscillationConstant_nonneg p) hD
  have hsig := intervalDomain_solution_signal_bounds_of_population_box
    p hsol ht huMin hlo hhi 0 h0
  have hVnn : 0 ≤ V := by
    dsimp [V]
    rw [intervalDomainLift, dif_pos h0]
    exact hsol.v_nonneg ht.1 ht.2
  have hfactor : -D ≤ p.μ * V - p.ν * U ^ p.γ := by
    have hm := mul_le_mul_of_nonneg_left hsig.1 p.hμ.le
    have hc : p.μ * (p.ν * uMin ^ p.γ / p.μ) =
        p.ν * uMin ^ p.γ := by field_simp [ne_of_gt p.hμ]
    rw [hc] at hm
    dsimp [D, U, V]
    linarith
  have hweighted := boundary_weighted_factor_lower_of_weight
    hVnn hq hD (by simpa [V] using hweight) hfactor
  have hCL : -U * (q * D) ≤
      U * ((1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ)) := by
    have hm := mul_le_mul_of_nonneg_left hweighted hUpos.le
    nlinarith
  have hbal := (intervalDomain_rectangle_boundary_left_balance hsol ht).1
    (fun y hy => hhi y (Ioo_subset_Icc_self hy))
  have hchem := mul_le_mul_of_nonpos_left hCL (by linarith : -p.χ₀ ≤ 0)
  have hextra : 0 ≤ p.χ₀ * U * (q * (p.β * L ^ 2)) :=
    mul_nonneg (mul_nonneg hχ hUpos.le)
      (mul_nonneg hq (mul_nonneg p.hβ (sq_nonneg L)))
  change deriv (fun r => intervalDomainLift (u r) 0) t ≤
    U * (p.a - p.b * U ^ p.α) +
      p.χ₀ * U * (q * (D + p.β * L ^ 2))
  change deriv (fun r => intervalDomainLift (u r) 0) t ≤
    U * (p.a - p.b * U ^ p.α) -
      p.χ₀ * U * ((1 + V) ^ (-p.β) *
        (p.μ * V - p.ν * U ^ p.γ)) at hbal
  nlinarith

/-- Left-boundary maximum slope with the concrete interval resolver
constant. -/
theorem intervalDomain_rectangle_boundary_left_max_slope
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      uMin ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0) :
    deriv (fun r => intervalDomainLift (u r) 0) t ≤
      intervalDomainLift (u t) 0 *
          (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) +
        p.χ₀ * intervalDomainLift (u t) 0 *
          (p.ν * ((intervalDomainLift (u t) 0) ^ p.γ - uMin ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * ((intervalDomainLift (u t) 0) ^ p.γ -
                uMin ^ p.γ))) ^ 2) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hv : 0 ≤ intervalDomainLift (v t) 0 := by
    rw [intervalDomainLift, dif_pos h0]
    exact hsol.v_nonneg ht.1 ht.2
  have hweight : (1 + intervalDomainLift (v t) 0) ^ (-p.β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (neg_nonpos.mpr p.hβ)
  simpa using intervalDomain_rectangle_boundary_left_max_slope_with_weight
    (p := p) (T := T) (t := t) (uMin := uMin) (u := u) (v := v)
      1 zero_le_one hweight hχ hsol ht huMin hlo hhi

/-- Left-boundary minimum slope under a uniform sensitivity-weight bound. -/
theorem intervalDomain_rectangle_boundary_left_min_slope_with_weight
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (q : ℝ) (hq : 0 ≤ q)
    (hweight : (1 + intervalDomainLift (v t) 0) ^ (-p.β) ≤ q)
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * q * intervalDomainLift (u t) 0 *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) 0) ^ p.γ)) +
        intervalDomainLift (u t) 0 *
          (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) ≤
      deriv (fun r => intervalDomainLift (u r) 0) t := by
  let U := intervalDomainLift (u t) 0
  let V := intervalDomainLift (v t) 0
  let D := p.ν * (uMax ^ p.γ - U ^ p.γ)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hUpos : 0 < U := by
    dsimp [U]
    rw [intervalDomainLift, dif_pos h0]
    exact hsol.u_pos' ht.1 ht.2
  have hD : 0 ≤ D := by
    have hp := Real.rpow_le_rpow hUpos.le (hhi 0 h0) p.hγ.le
    exact mul_nonneg p.hν.le (sub_nonneg.mpr hp)
  have hsig := intervalDomain_solution_signal_bounds_of_population_box
    p hsol ht hUpos.le hlo hhi 0 h0
  have hVnn : 0 ≤ V := by
    dsimp [V]
    rw [intervalDomainLift, dif_pos h0]
    exact hsol.v_nonneg ht.1 ht.2
  have hfactor : p.μ * V - p.ν * U ^ p.γ ≤ D := by
    have hm := mul_le_mul_of_nonneg_left hsig.2.1 p.hμ.le
    have hc : p.μ * (p.ν * uMax ^ p.γ / p.μ) =
        p.ν * uMax ^ p.γ := by field_simp [ne_of_gt p.hμ]
    rw [hc] at hm
    dsimp [D, U, V]
    linarith
  have hweighted := boundary_weighted_factor_upper_of_weight
    hVnn hq hD (by simpa [V] using hweight) hfactor
  have hCL :
      U * ((1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ)) ≤
        U * (q * D) := mul_le_mul_of_nonneg_left hweighted hUpos.le
  have hbal := (intervalDomain_rectangle_boundary_left_balance hsol ht).2
    (fun y hy => hlo y (Ioo_subset_Icc_self hy))
  have hchem := mul_le_mul_of_nonpos_left hCL (by linarith : -p.χ₀ ≤ 0)
  change -p.χ₀ * q * U * D + U * (p.a - p.b * U ^ p.α) ≤
    deriv (fun r => intervalDomainLift (u r) 0) t
  change U * (p.a - p.b * U ^ p.α) -
      p.χ₀ * U * ((1 + V) ^ (-p.β) *
        (p.μ * V - p.ν * U ^ p.γ)) ≤
    deriv (fun r => intervalDomainLift (u r) 0) t at hbal
  nlinarith

/-- Left-boundary minimum slope. -/
theorem intervalDomain_rectangle_boundary_left_min_slope
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * intervalDomainLift (u t) 0 *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) 0) ^ p.γ)) +
        intervalDomainLift (u t) 0 *
          (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) ≤
      deriv (fun r => intervalDomainLift (u r) 0) t := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hv : 0 ≤ intervalDomainLift (v t) 0 := by
    rw [intervalDomainLift, dif_pos h0]
    exact hsol.v_nonneg ht.1 ht.2
  have hweight : (1 + intervalDomainLift (v t) 0) ^ (-p.β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (neg_nonpos.mpr p.hβ)
  simpa using intervalDomain_rectangle_boundary_left_min_slope_with_weight
    (p := p) (T := T) (t := t) (uMax := uMax) (u := u) (v := v)
      1 zero_le_one hweight hχ hsol ht hlo hhi

set_option maxHeartbeats 1600000 in
/-- Exact right-endpoint balance, dual to the left-endpoint result. -/
theorem intervalDomain_rectangle_boundary_right_balance
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ((∀ y ∈ Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1) →
      deriv (fun r => intervalDomainLift (u r) 1) t ≤
        intervalDomainLift (u t) 1 *
            (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) -
          p.χ₀ * intervalDomainLift (u t) 1 *
            ((1 + intervalDomainLift (v t) 1) ^ (-p.β) *
              (p.μ * intervalDomainLift (v t) 1 -
                p.ν * (intervalDomainLift (u t) 1) ^ p.γ))) ∧
    ((∀ y ∈ Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) 1 ≤ intervalDomainLift (u t) y) →
      intervalDomainLift (u t) 1 *
            (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) -
          p.χ₀ * intervalDomainLift (u t) 1 *
            ((1 + intervalDomainLift (v t) 1) ^ (-p.β) *
              (p.μ * intervalDomainLift (v t) 1 -
                p.ν * (intervalDomainLift (u t) 1) ^ p.γ)) ≤
        deriv (fun r => intervalDomainLift (u r) 1) t) := by
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  set V : ℝ → ℝ := intervalDomainLift (v t) with hV_def
  have huC2 : ContDiffOn ℝ 2 U (Ioo (0 : ℝ) 1) := (hC2 t ht).1
  have hvC2 : ContDiffOn ℝ 2 V (Ioo (0 : ℝ) 1) := (hC2 t ht).2
  have huCont : ContinuousOn U (Icc (0 : ℝ) 1) :=
    (hClosed t ht).1.1.continuousOn
  have hvCont : ContinuousOn V (Icc (0 : ℝ) 1) :=
    (hClosed t ht).2.1.continuousOn
  have hNeuU : Tendsto (deriv U) (nhdsWithin 1 (Iio 1)) (nhds 0) :=
    (hNeu t ht).1.2
  have hNeuV : Tendsto (deriv V) (nhdsWithin 1 (Iio 1)) (nhds 0) :=
    (hNeu t ht).2.2
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hUpos : 0 < U 1 := by
    rw [hU_def, intervalDomainLift, dif_pos h1]
    exact hsol.u_pos' ht.1 ht.2
  have hvnn : ∀ y, 0 ≤ V y := by
    intro y
    rw [hV_def]
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht.1 ht.2
    · exact le_rfl
  have hposV : ∀ y, 0 < 1 + V y := fun y => by linarith [hvnn y]
  set G : ℝ → ℝ := fun x =>
    deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x => U x * (p.a - p.b * U x ^ p.α) with hR_def
  set Cfun : ℝ → ℝ := fun x =>
    deriv (fun y => U y * deriv V y / (1 + V y) ^ p.β) x with hCfun_def
  have hfilter : nhdsWithin (1 : ℝ) (Ioo 0 1) =
      nhdsWithin 1 (Iio 1) := nhdsWithin_Ioo_eq_nhdsLT h01
  have hGlim : Tendsto G (nhdsWithin 1 (Iio 1)) (nhds (G 1)) := by
    have hmaps : MapsTo (fun w => (t, w)) (Icc (0 : ℝ) 1)
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := fun w hw => ⟨ht, hw⟩
    have hcomp : ContinuousOn G (Icc (0 : ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 1 h1).mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
  have hRlim : Tendsto R (nhdsWithin 1 (Iio 1)) (nhds (R 1)) := by
    have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) :=
      huCont.mul (continuousOn_const.sub
        (continuousOn_const.mul
          (huCont.rpow_const (fun _ _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcont 1 h1).mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
  have hUxxEq : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Ioo_subset_Icc_self hx⟩
    have hpde := hsol.pde_u ht.1 ht.2 (x := xp) hx
    have etd : intervalDomain.timeDeriv u t xp = G x := by
      show deriv (fun r => u r xp) t = G x
      simp only [hG_def]
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    have elap : intervalDomain.laplacian (u t) xp = deriv (deriv U) x := rfl
    have echem : intervalDomain.chemotaxisDiv p (u t) (v t) xp = Cfun x := rfl
    have eu : u t xp = U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    rw [etd, elap, echem, eu] at hpde
    rw [hR_def]
    linarith
  have hVxxEq : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Ioo_subset_Icc_self hx⟩
    have hpde := hsol.pde_v ht.1 ht.2 (x := xp) hx
    have elap : intervalDomain.laplacian (v t) xp = deriv (deriv V) x := rfl
    have eu : u t xp = U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    have ev : v t xp = V x := by
      rw [hV_def, intervalDomainLift, dif_pos (Ioo_subset_Icc_self hx)]
    rw [elap, eu, ev] at hpde
    linarith
  set CL : ℝ := U 1 * ((1 + V 1) ^ (-p.β) *
    (p.μ * V 1 - p.ν * U 1 ^ p.γ)) with hCL_def
  have hCexpr : ∀ x ∈ Ioo (0 : ℝ) 1,
      Cfun x =
        deriv U x * (deriv V x * (1 + V x) ^ (-p.β)) +
          U x * (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
            (1 + V x) ^ (-p.β) *
              (p.μ * V x - p.ν * U x ^ p.γ)) := by
    intro x hx
    have hUx := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).1
    have hVx := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hvC2 hx).1
    have hVxx := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hvC2 hx).2
    have hP : HasDerivAt
        (fun y => deriv V y * (1 + V y) ^ (-p.β))
        (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
          (1 + V x) ^ (-p.β) * deriv (deriv V) x) x :=
      flux_integrand_hasDerivAt hVx hVxx (hposV x)
    have hFeq : (fun y => U y * deriv V y / (1 + V y) ^ p.β) =
        (fun y => U y * (deriv V y * (1 + V y) ^ (-p.β))) := by
      funext y
      rw [mul_div_assoc, Real.rpow_neg (hposV y).le, div_eq_mul_inv]
    have hCx : Cfun x =
        deriv U x * (deriv V x * (1 + V x) ^ (-p.β)) +
          U x * (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
            (1 + V x) ^ (-p.β) * deriv (deriv V) x) := by
      simp only [hCfun_def]
      rw [hFeq]
      exact (hUx.mul hP).deriv
    rw [hCx, hVxxEq x hx]
  have hUlim : Tendsto U (nhdsWithin 1 (Iio 1)) (nhds (U 1)) := by
    have h := (huCont 1 h1).mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have hVlim : Tendsto V (nhdsWithin 1 (Iio 1)) (nhds (V 1)) := by
    have h := (hvCont 1 h1).mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have h1Vlim : Tendsto (fun x => 1 + V x) (nhdsWithin 1 (Iio 1))
      (nhds (1 + V 1)) := hVlim.const_add 1
  have hpowβ : Tendsto (fun x => (1 + V x) ^ (-p.β))
      (nhdsWithin 1 (Iio 1)) (nhds ((1 + V 1) ^ (-p.β))) :=
    h1Vlim.rpow_const (Or.inl (ne_of_gt (hposV 1)))
  have hpowβ1 : Tendsto (fun x => (1 + V x) ^ (-p.β - 1))
      (nhdsWithin 1 (Iio 1)) (nhds ((1 + V 1) ^ (-p.β - 1))) :=
    h1Vlim.rpow_const (Or.inl (ne_of_gt (hposV 1)))
  have hpowγ : Tendsto (fun x => U x ^ p.γ) (nhdsWithin 1 (Iio 1))
      (nhds (U 1 ^ p.γ)) :=
    hUlim.rpow_const (Or.inl (ne_of_gt hUpos))
  have hexpr : Tendsto
      (fun x =>
        deriv U x * (deriv V x * (1 + V x) ^ (-p.β)) +
          U x * (-p.β * (1 + V x) ^ (-p.β - 1) * (deriv V x) ^ 2 +
            (1 + V x) ^ (-p.β) *
              (p.μ * V x - p.ν * U x ^ p.γ)))
      (nhdsWithin 1 (Iio 1)) (nhds CL) := by
    have hsum := (hNeuU.mul (hNeuV.mul hpowβ)).add
      (hUlim.mul
        ((((tendsto_const_nhds (x := -p.β)).mul hpowβ1).mul
            (hNeuV.pow 2)).add
          (hpowβ.mul
            ((hVlim.const_mul p.μ).sub (hpowγ.const_mul p.ν)))))
    rw [hCL_def]
    simpa using hsum
  have hClim : Tendsto Cfun (nhdsWithin 1 (Iio 1)) (nhds CL) := by
    refine hexpr.congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hCexpr x hx).symm
  set W : ℝ := G 1 - R 1 + p.χ₀ * CL with hW_def
  have hUxxLim : Tendsto (deriv (deriv U)) (nhdsWithin 1 (Iio 1))
      (nhds W) := by
    refine ((hGlim.sub hRlim).add (hClim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hUxxEq x hx).symm
  have hUwithin : ContinuousWithinAt U (Iic 1) 1 := by
    refine (huCont 1 h1).mono_of_mem_nhdsWithin ?_
    have hIcc : Icc (0 : ℝ) 1 = Ici (0 : ℝ) ∩ Iic 1 := by
      ext z
      simp [mem_Icc, mem_Ici, mem_Iic]
    rw [hIcc]
    exact inter_mem
      (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h01)) self_mem_nhdsWithin
  have hd1 : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt U (deriv U x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).1
  have hd2 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hx).2
  have hII : Ioo (1 - (1 : ℝ)) 1 = Ioo (0 : ℝ) 1 := by rw [sub_self]
  have hG : G 1 = W + R 1 - p.χ₀ * CL := by
    rw [hW_def]
    ring
  constructor
  · intro hmax
    have hWle : W ≤ 0 :=
      Lemma31Closure.boundary_max_deriv2_llimit_nonpos (η := 1) h01 hUwithin
        (by rw [hII]; exact hmax) (by rw [hII]; exact hd1)
        (by rw [hII]; exact hd2) hNeuU hUxxLim
    rw [show deriv (fun r => intervalDomainLift (u r) 1) t = G 1 from rfl,
      hG]
    simp only [hR_def, hCL_def, hU_def, hV_def]
    linarith
  · intro hmin
    have hWge : 0 ≤ W :=
      boundary_min_deriv2_llimit_nonneg (η := 1) h01 hUwithin
        (by rw [hII]; exact hmin) (by rw [hII]; exact hd1)
        (by rw [hII]; exact hd2) hNeuU hUxxLim
    rw [show deriv (fun r => intervalDomainLift (u r) 1) t = G 1 from rfl,
      hG]
    simp only [hR_def, hCL_def, hU_def, hV_def]
    linarith

/-- Right-boundary maximum slope under a uniform sensitivity-weight bound. -/
theorem intervalDomain_rectangle_boundary_right_max_slope_with_weight
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (q : ℝ) (hq : 0 ≤ q)
    (hweight : (1 + intervalDomainLift (v t) 1) ^ (-p.β) ≤ q)
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      uMin ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1) :
    deriv (fun r => intervalDomainLift (u r) 1) t ≤
      intervalDomainLift (u t) 1 *
          (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) +
        p.χ₀ * intervalDomainLift (u t) 1 *
          (q * (p.ν * ((intervalDomainLift (u t) 1) ^ p.γ - uMin ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * ((intervalDomainLift (u t) 1) ^ p.γ -
                uMin ^ p.γ))) ^ 2)) := by
  let U := intervalDomainLift (u t) 1
  let V := intervalDomainLift (v t) 1
  let D := p.ν * (U ^ p.γ - uMin ^ p.γ)
  let L := unitIntervalResolverGradientOscillationConstant p * D
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hUpos : 0 < U := by
    dsimp [U]
    rw [intervalDomainLift, dif_pos h1]
    exact hsol.u_pos' ht.1 ht.2
  have hD : 0 ≤ D := by
    have hp := Real.rpow_le_rpow huMin (hlo 1 h1) p.hγ.le
    exact mul_nonneg p.hν.le (sub_nonneg.mpr hp)
  have hL : 0 ≤ L := mul_nonneg
    (unitIntervalResolverGradientOscillationConstant_nonneg p) hD
  have hsig := intervalDomain_solution_signal_bounds_of_population_box
    p hsol ht huMin hlo hhi 1 h1
  have hVnn : 0 ≤ V := by
    dsimp [V]
    rw [intervalDomainLift, dif_pos h1]
    exact hsol.v_nonneg ht.1 ht.2
  have hfactor : -D ≤ p.μ * V - p.ν * U ^ p.γ := by
    have hm := mul_le_mul_of_nonneg_left hsig.1 p.hμ.le
    have hc : p.μ * (p.ν * uMin ^ p.γ / p.μ) =
        p.ν * uMin ^ p.γ := by field_simp [ne_of_gt p.hμ]
    rw [hc] at hm
    dsimp [D, U, V]
    linarith
  have hweighted := boundary_weighted_factor_lower_of_weight
    hVnn hq hD (by simpa [V] using hweight) hfactor
  have hCL : -U * (q * D) ≤
      U * ((1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ)) := by
    have hm := mul_le_mul_of_nonneg_left hweighted hUpos.le
    nlinarith
  have hbal := (intervalDomain_rectangle_boundary_right_balance hsol ht).1
    (fun y hy => hhi y (Ioo_subset_Icc_self hy))
  have hchem := mul_le_mul_of_nonpos_left hCL (by linarith : -p.χ₀ ≤ 0)
  have hextra : 0 ≤ p.χ₀ * U * (q * (p.β * L ^ 2)) :=
    mul_nonneg (mul_nonneg hχ hUpos.le)
      (mul_nonneg hq (mul_nonneg p.hβ (sq_nonneg L)))
  change deriv (fun r => intervalDomainLift (u r) 1) t ≤
    U * (p.a - p.b * U ^ p.α) +
      p.χ₀ * U * (q * (D + p.β * L ^ 2))
  change deriv (fun r => intervalDomainLift (u r) 1) t ≤
    U * (p.a - p.b * U ^ p.α) -
      p.χ₀ * U * ((1 + V) ^ (-p.β) *
        (p.μ * V - p.ν * U ^ p.γ)) at hbal
  nlinarith

/-- Right-boundary maximum slope with the concrete interval resolver
constant. -/
theorem intervalDomain_rectangle_boundary_right_max_slope
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      uMin ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1) :
    deriv (fun r => intervalDomainLift (u r) 1) t ≤
      intervalDomainLift (u t) 1 *
          (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) +
        p.χ₀ * intervalDomainLift (u t) 1 *
          (p.ν * ((intervalDomainLift (u t) 1) ^ p.γ - uMin ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * ((intervalDomainLift (u t) 1) ^ p.γ -
                uMin ^ p.γ))) ^ 2) := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hv : 0 ≤ intervalDomainLift (v t) 1 := by
    rw [intervalDomainLift, dif_pos h1]
    exact hsol.v_nonneg ht.1 ht.2
  have hweight : (1 + intervalDomainLift (v t) 1) ^ (-p.β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (neg_nonpos.mpr p.hβ)
  simpa using intervalDomain_rectangle_boundary_right_max_slope_with_weight
    (p := p) (T := T) (t := t) (uMin := uMin) (u := u) (v := v)
      1 zero_le_one hweight hχ hsol ht huMin hlo hhi

/-- Right-boundary minimum slope under a uniform sensitivity-weight bound. -/
theorem intervalDomain_rectangle_boundary_right_min_slope_with_weight
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (q : ℝ) (hq : 0 ≤ q)
    (hweight : (1 + intervalDomainLift (v t) 1) ^ (-p.β) ≤ q)
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) 1 ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * q * intervalDomainLift (u t) 1 *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) 1) ^ p.γ)) +
        intervalDomainLift (u t) 1 *
          (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) ≤
      deriv (fun r => intervalDomainLift (u r) 1) t := by
  let U := intervalDomainLift (u t) 1
  let V := intervalDomainLift (v t) 1
  let D := p.ν * (uMax ^ p.γ - U ^ p.γ)
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hUpos : 0 < U := by
    dsimp [U]
    rw [intervalDomainLift, dif_pos h1]
    exact hsol.u_pos' ht.1 ht.2
  have hD : 0 ≤ D := by
    have hp := Real.rpow_le_rpow hUpos.le (hhi 1 h1) p.hγ.le
    exact mul_nonneg p.hν.le (sub_nonneg.mpr hp)
  have hsig := intervalDomain_solution_signal_bounds_of_population_box
    p hsol ht hUpos.le hlo hhi 1 h1
  have hVnn : 0 ≤ V := by
    dsimp [V]
    rw [intervalDomainLift, dif_pos h1]
    exact hsol.v_nonneg ht.1 ht.2
  have hfactor : p.μ * V - p.ν * U ^ p.γ ≤ D := by
    have hm := mul_le_mul_of_nonneg_left hsig.2.1 p.hμ.le
    have hc : p.μ * (p.ν * uMax ^ p.γ / p.μ) =
        p.ν * uMax ^ p.γ := by field_simp [ne_of_gt p.hμ]
    rw [hc] at hm
    dsimp [D, U, V]
    linarith
  have hweighted := boundary_weighted_factor_upper_of_weight
    hVnn hq hD (by simpa [V] using hweight) hfactor
  have hCL :
      U * ((1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ)) ≤
        U * (q * D) := mul_le_mul_of_nonneg_left hweighted hUpos.le
  have hbal := (intervalDomain_rectangle_boundary_right_balance hsol ht).2
    (fun y hy => hlo y (Ioo_subset_Icc_self hy))
  have hchem := mul_le_mul_of_nonpos_left hCL (by linarith : -p.χ₀ ≤ 0)
  change -p.χ₀ * q * U * D + U * (p.a - p.b * U ^ p.α) ≤
    deriv (fun r => intervalDomainLift (u r) 1) t
  change U * (p.a - p.b * U ^ p.α) -
      p.χ₀ * U * ((1 + V) ^ (-p.β) *
        (p.μ * V - p.ν * U ^ p.γ)) ≤
    deriv (fun r => intervalDomainLift (u r) 1) t at hbal
  nlinarith

/-- Right-boundary minimum slope. -/
theorem intervalDomain_rectangle_boundary_right_min_slope
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) 1 ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * intervalDomainLift (u t) 1 *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) 1) ^ p.γ)) +
        intervalDomainLift (u t) 1 *
          (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) ≤
      deriv (fun r => intervalDomainLift (u r) 1) t := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hv : 0 ≤ intervalDomainLift (v t) 1 := by
    rw [intervalDomainLift, dif_pos h1]
    exact hsol.v_nonneg ht.1 ht.2
  have hweight : (1 + intervalDomainLift (v t) 1) ^ (-p.β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (neg_nonpos.mpr p.hβ)
  simpa using intervalDomain_rectangle_boundary_right_min_slope_with_weight
    (p := p) (T := T) (t := t) (uMax := uMax) (u := u) (v := v)
      1 zero_le_one hweight hχ hsol ht hlo hhi

#print axioms intervalDomain_rectangle_boundary_left_balance
#print axioms intervalDomain_rectangle_boundary_left_max_slope
#print axioms intervalDomain_rectangle_boundary_left_min_slope
#print axioms intervalDomain_rectangle_boundary_right_balance
#print axioms intervalDomain_rectangle_boundary_right_max_slope
#print axioms intervalDomain_rectangle_boundary_right_min_slope
#print axioms intervalDomain_rectangle_boundary_left_max_slope_with_weight
#print axioms intervalDomain_rectangle_boundary_left_min_slope_with_weight
#print axioms intervalDomain_rectangle_boundary_right_max_slope_with_weight
#print axioms intervalDomain_rectangle_boundary_right_min_slope_with_weight

end

end ShenWork.Paper3
