/-
  Lemma 3.1 closure: wire the max-principle infrastructure into the
  `Lemma_3_1_intervalDomain` sorry in Statements.lean.

  The chain:
  1. From `IsPaper2ClassicalSolution`, extract F(t,x) = intervalDomainLift(u(t))(x)
  2. Show argmax slope bound: at any argmax x* of F(t,·) on [0,1],
     ∂ₜF(t,x*) ≤ 0 (interior_max_point_of_solution + boundary companion)
  3. Apply sliceMax_dini_of_argmax_bound → Dini condition for sSup
  4. Convert to supNorm via supNorm_eq_sSup_lift_image
  5. Apply supNorm_nonincreasing_of_dini → SupNormNonincreasingOn on Ioo
  6. Extend from Ioo to Ioc by continuity at right endpoint

  ## Boundary argmax (x = 0)

  The interior estimate `interior_max_point_of_solution` applies `pde_u` AT the
  point, which needs `x ∈ inside = Ioo 0 1`.  At the endpoint `x = 0` the abstract
  PDE / Laplacian are unavailable (the zero-extension lift is discontinuous at the
  endpoint, so the two-sided `deriv (deriv lift) 0` is junk).  The honest route is
  the same as `MinPersistenceAtoms.hbdry_left_chi0`: take the `x→0⁺` right-limit of
  the interior PDE.  Writing `G x := ∂ₜ(lift u)(x)`, `R` for the reaction and
  `C` for the chemotaxis divergence, the interior PDE reads
    `u_xx(x) = G x − R x + χ₀·C x`  on `(0,1)`,
  so `u_xx` has a right-limit `V = G 0 − R 0 + χ₀·CL` where `CL = lim_{x→0⁺} C x`.
  The boundary maximum 2nd-derivative test gives `V ≤ 0`, and the elliptic coupling
  `μ·v(0) ≤ ν·u(0)^γ` forces `CL ≤ 0`; with `χ₀ ≤ 0` this yields `G 0 ≤ R 0`,
  the clean Hamilton upper slope at the boundary.
-/
import ShenWork.Paper2.IntervalDomainMaxPointSolution
import ShenWork.Paper2.IntervalDomainSliceMaxDini
import ShenWork.Paper2.IntervalLemma31Heat
import ShenWork.Paper2.IntervalDomainSupNormMaxPrinciple
import ShenWork.Paper2.IntervalDomainBoundaryDeriv2
import ShenWork.Paper2.IntervalDomainBoundaryDeriv2Right
import ShenWork.Paper2.IntervalDomainFluxIntegrandDeriv
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.MaxPrincipleAtoms
open ShenWork.MinPersistenceAtoms
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.Lemma31Closure

/-- **Boundary (left) maximum 2nd-derivative test.**  Dual of
`boundary_min_deriv2_rlimit_nonneg` via `w ↦ −w`: a left-boundary maximum with
vanishing Neumann right-limit forces a nonpositive `w''` right-limit. -/
theorem boundary_max_deriv2_rlimit_nonpos
    {w : ℝ → ℝ} {η V : ℝ} (hη : 0 < η)
    (hwcont : ContinuousWithinAt w (Set.Ici 0) 0)
    (hmax : ∀ x ∈ Set.Ioo (0:ℝ) η, w x ≤ w 0)
    (hd1 : ∀ x ∈ Set.Ioo (0:ℝ) η, HasDerivAt w (deriv w x) x)
    (hd2 : ∀ x ∈ Set.Ioo (0:ℝ) η, HasDerivAt (deriv w) (deriv (deriv w) x) x)
    (hw'lim : Tendsto (deriv w) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hw''lim : Tendsto (deriv (deriv w)) (nhdsWithin 0 (Set.Ioi 0)) (nhds V)) :
    V ≤ 0 := by
  -- `deriv (fun y => -w y) = -deriv w` (function-level neg, matching `HasDerivAt.neg`).
  have hd1neg : deriv (fun y => -w y) = -deriv w := by
    funext y; exact deriv.neg
  have hd2neg : deriv (deriv (fun y => -w y)) = -deriv (deriv w) := by
    rw [hd1neg]; funext y; exact deriv.neg
  have key : 0 ≤ -V := by
    refine boundary_min_deriv2_rlimit_nonneg (w := fun y => -w y) (η := η) (V := -V)
      hη hwcont.neg (fun x hx => neg_le_neg (hmax x hx)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [hd1neg]; exact (hd1 x hx).neg
    · intro x hx
      rw [hd1neg, ((hd2 x hx).neg).deriv]; exact (hd2 x hx).neg
    · rw [hd1neg]
      simpa using hw'lim.neg
    · rw [hd2neg]
      exact hw''lim.neg
  linarith

/-- At ANY spatial argmax (interior OR boundary) of a classical solution
with χ₀ ≤ 0, the time derivative satisfies u_t ≤ u·(a − b·u^α).

For interior argmax: `interior_max_point_of_solution`.
For boundary argmax x = 0: the `x→0⁺` right-limit of the interior PDE, with the
boundary maximum 2nd-derivative test and the elliptic coupling. -/
theorem boundary_max_point_left
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmaxlift : ∀ y, intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0) :
    deriv (fun r => intervalDomainLift (u r) 0) t
      ≤ intervalDomainLift (u t) 0
        * (p.a - p.b * (intervalDomainLift (u t) 0) ^ p.α) := by
  have htmem : t ∈ Set.Ioo (0:ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  set Vv : ℝ → ℝ := intervalDomainLift (v t) with hVv_def
  have hu_c2 : ContDiffOn ℝ 2 U (Set.Ioo (0:ℝ) 1) := (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 Vv (Set.Ioo (0:ℝ) 1) := (hC2 t htmem).2
  have hu_cont_Icc : ContinuousOn U (Set.Icc (0:ℝ) 1) := (hClosed t htmem).1.1.continuousOn
  have hv_cont_Icc : ContinuousOn Vv (Set.Icc (0:ℝ) 1) := (hClosed t htmem).2.1.continuousOn
  have hNeuU0 : Tendsto (deriv U) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).1.1
  have hNeuV0 : Tendsto (deriv Vv) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).2.1
  have hNeuV1 : Tendsto (deriv Vv) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (hNeu t htmem).2.2
  have h0Icc : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h01 : (0:ℝ) < 1 := by norm_num
  -- Positivity / nonnegativity.
  have hu_pos : ∀ y, 0 < u t y := fun y => hsol.u_pos' ht0 htT
  have hU0_pos : 0 < U 0 := by
    rw [hU_def, intervalDomainLift, dif_pos h0Icc]; exact hu_pos _
  have hv_nn : ∀ y, 0 ≤ Vv y := by
    intro y; rw [hVv_def]; unfold intervalDomainLift; split_ifs with hy
    · exact hsol.v_nonneg ht0 htT
    · exact le_refl 0
  have hpos_v : ∀ y, (0:ℝ) < 1 + Vv y := fun y => by linarith [hv_nn y]
  have hU_le : ∀ y ∈ Set.Ioo (0:ℝ) 1, U y ≤ U 0 := fun y _ => hmaxlift y
  have hU_nonneg : ∀ y, 0 ≤ U y := by
    intro y; rw [hU_def]; unfold intervalDomainLift; split_ifs with hy
    · exact (hsol.u_pos' ht0 htT).le
    · exact le_refl 0
  -- Field notation matching `hbdry_left_chi0`.
  set G : ℝ → ℝ := fun x => deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x => U x * (p.a - p.b * (U x) ^ p.α) with hR_def
  set Cfun : ℝ → ℝ :=
    fun x => deriv (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β) x with hCfun_def
  have hfilter : nhdsWithin (0:ℝ) (Set.Ioo 0 1) = nhdsWithin 0 (Set.Ioi 0) :=
    nhdsWithin_Ioo_eq_nhdsGT h01
  -- `G` continuous at `0` along `0⁺` (conjunct 6, u-part).
  have hG_lim : Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds (G 0)) := by
    have hmaps : Set.MapsTo (fun w => (t, w)) (Set.Icc (0:ℝ) 1)
        (Set.Ioo (0:ℝ) T ×ˢ Set.Icc (0:ℝ) 1) := fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn G (Set.Icc (0:ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  -- reaction `R` continuous at `0` along `0⁺`.
  have hR_lim : Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds (R 0)) := by
    have hRcontOn : ContinuousOn R (Set.Icc (0:ℝ) 1) :=
      hu_cont_Icc.mul (continuousOn_const.sub (continuousOn_const.mul
        (hu_cont_Icc.rpow_const (fun x _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcontOn 0 h0Icc).mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  -- Interior PDE: `u_xx = G − R + χ₀·C` on `(0,1)`.
  have hUxx_eq : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hx
    have hpu := hsol.pde_u ht0 htT hmem
    have e_td : intervalDomain.timeDeriv u t ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      show deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) t = G x
      simp only [hG_def]; congr 1; funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomain.laplacian (u t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = deriv (deriv U) x := rfl
    have e_cd : intervalDomain.chemotaxisDiv p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x := rfl
    have e_u : u t (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu
    rw [hR_def]; linarith [hpu]
  -- Elliptic relation `v_xx = μ v − ν u^γ` on `(0,1)`.
  have hPDE_v : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv Vv) y = p.μ * Vv y - p.ν * (U y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hy
    have hpv := hsol.pde_v ht0 htT hxy
    have e_lap : intervalDomain.laplacian (v t)
        ⟨y, Set.Ioo_subset_Icc_self hy⟩ = deriv (deriv Vv) y := rfl
    have e_u : u t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) = U y := by
      rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    have e_v : v t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) = Vv y := by
      rw [hVv_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    rw [e_lap, e_u, e_v] at hpv
    linarith [hpv]
  -- Elliptic sup bound at `0`: `μ·v(0) ≤ ν·u(0)^γ`.
  set B : ℝ := p.ν * (U 0) ^ p.γ with hBdef
  have hd1V : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ Vv y := by
    intro y hy
    exact (hv_c2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hd2V : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (deriv Vv) y := by
    intro y hy
    exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).2).differentiableAt
  have hSrc : ∀ y ∈ Set.Ioo (0:ℝ) 1, |p.ν * (U y) ^ p.γ| ≤ B := by
    intro y hy
    have hpow : (U y) ^ p.γ ≤ (U 0) ^ p.γ :=
      Real.rpow_le_rpow (hU_nonneg y) (hU_le y hy) p.hγ.le
    have hnn : 0 ≤ p.ν * (U y) ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg (hU_nonneg y) _)
    rw [abs_of_nonneg hnn, hBdef]
    exact mul_le_mul_of_nonneg_left hpow p.hν.le
  have hv_bound := elliptic_sup_bound (w := Vv)
    (Src := fun y => p.ν * (U y) ^ p.γ) (μ := p.μ) (B := B) p.hμ hv_cont_Icc hd1V hd2V
    (by intro y hy; rw [hPDE_v y hy]) hSrc hNeuV0 hNeuV1
  have hμv0 : p.μ * Vv 0 ≤ B := by
    have := hv_bound 0 h0Icc
    rw [le_div_iff₀ p.hμ] at this; rw [mul_comm]; exact this
  -- The chemotaxis-divergence right-limit `CL`, and `CL ≤ 0`.
  set CL : ℝ :=
    0 * (0 * (1 + Vv 0) ^ (-p.β)) + U 0 *
      (-p.β * (1 + Vv 0) ^ (-p.β - 1) * (0:ℝ) ^ 2
        + (1 + Vv 0) ^ (-p.β) * (p.μ * Vv 0 - p.ν * (U 0) ^ p.γ)) with hCL_def
  -- Per-point expansion of the chemotaxis divergence on `(0,1)` (general,
  -- non-critical), with `v_xx` substituted from the elliptic PDE.
  have hCexpr : ∀ x ∈ Set.Ioo (0:ℝ) 1, Cfun x =
      deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β))
        + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * (U x) ^ p.γ)) := by
    intro x hx
    have hUx : HasDerivAt U (deriv U x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
    have hVx : HasDerivAt Vv (deriv Vv x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).1
    have hVxx : HasDerivAt (deriv Vv) (deriv (deriv Vv) x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).2
    have hP' : HasDerivAt (fun y => deriv Vv y * (1 + Vv y) ^ (-p.β))
        (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (deriv (deriv Vv) x)) x :=
      flux_integrand_hasDerivAt hVx hVxx (hpos_v x)
    have hFeq2 : (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β)
        = (fun y => U y * (deriv Vv y * (1 + Vv y) ^ (-p.β))) := by
      funext y
      rw [mul_div_assoc, Real.rpow_neg (hpos_v y).le, div_eq_mul_inv]
    have hmul := hUx.mul hP'
    have hCfx : Cfun x = deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β))
        + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (deriv (deriv Vv) x)) := by
      simp only [hCfun_def]
      rw [hFeq2]; exact hmul.deriv
    rw [hCfx, hPDE_v x hx]
  -- Continuity limits along `0⁺`.
  have hU0L : Tendsto U (nhdsWithin 0 (Set.Ioi 0)) (nhds (U 0)) := by
    have h := (hu_cont_Icc 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have hVv0L : Tendsto Vv (nhdsWithin 0 (Set.Ioi 0)) (nhds (Vv 0)) := by
    have h := (hv_cont_Icc 0 h0Icc).mono_left
      (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
    rwa [hfilter] at h
  have h1Vv0L : Tendsto (fun x => 1 + Vv x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (1 + Vv 0)) := hVv0L.const_add 1
  have hrpb : Tendsto (fun x => (1 + Vv x) ^ (-p.β)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 + Vv 0) ^ (-p.β))) := h1Vv0L.rpow_const (Or.inl (ne_of_gt (hpos_v 0)))
  have hrpb1 : Tendsto (fun x => (1 + Vv x) ^ (-p.β - 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 + Vv 0) ^ (-p.β - 1))) := h1Vv0L.rpow_const (Or.inl (ne_of_gt (hpos_v 0)))
  have hUg : Tendsto (fun x => (U x) ^ p.γ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((U 0) ^ p.γ)) := hU0L.rpow_const (Or.inl (ne_of_gt hU0_pos))
  have hexpr : Tendsto
      (fun x => deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β))
        + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * (U x) ^ p.γ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds CL) := by
    have t1 := hNeuU0.mul (hNeuV0.mul hrpb)
    have t2i1 := ((tendsto_const_nhds (x := -p.β)).mul hrpb1).mul (hNeuV0.pow 2)
    have t2i2 := hrpb.mul ((hVv0L.const_mul p.μ).sub (hUg.const_mul p.ν))
    have t2 := hU0L.mul (t2i1.add t2i2)
    have hsum := t1.add t2
    rw [hCL_def]
    exact hsum
  have hC_lim : Tendsto Cfun (nhdsWithin 0 (Set.Ioi 0)) (nhds CL) := by
    refine hexpr.congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hCexpr x hx).symm
  have hCL_nonpos : CL ≤ 0 := by
    have hcpos : (0:ℝ) < (1 + Vv 0) ^ (-p.β) := Real.rpow_pos_of_pos (hpos_v 0) _
    have hfac : p.μ * Vv 0 - p.ν * (U 0) ^ p.γ ≤ 0 := by rw [hBdef] at hμv0; linarith
    rw [hCL_def]
    have e2 : ((0:ℝ) ^ 2) = 0 := by norm_num
    rw [e2]
    have h2 : 0 ≤ U 0 * ((1 + Vv 0) ^ (-p.β) * (p.ν * (U 0) ^ p.γ - p.μ * Vv 0)) :=
      mul_nonneg hU0_pos.le (mul_nonneg hcpos.le (by linarith))
    nlinarith [h2]
  -- `u_xx` right-limit `V := G 0 − R 0 + χ₀·CL`.
  set Vlim : ℝ := G 0 - R 0 + p.χ₀ * CL with hVlim_def
  have hUxx_lim : Tendsto (deriv (deriv U)) (nhdsWithin 0 (Set.Ioi 0)) (nhds Vlim) := by
    refine ((hG_lim.sub hR_lim).add (hC_lim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx using (hUxx_eq x hx).symm
  -- Boundary maximum 2nd-derivative test ⇒ `Vlim ≤ 0`.
  have hwcont : ContinuousWithinAt U (Set.Ici 0) 0 := by
    refine (hu_cont_Icc 0 h0Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0:ℝ) 1 = Set.Ici (0:ℝ) ∩ Set.Iic 1 := by
      ext z; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h01))
  have hd1U : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (deriv U x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
  have hd2U : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).2
  have hVlim_nonpos : Vlim ≤ 0 :=
    boundary_max_deriv2_rlimit_nonpos h01 hwcont
      (fun x hx => hU_le x hx) hd1U hd2U hNeuU0 hUxx_lim
  -- Assemble: `G 0 = Vlim + R 0 − χ₀·CL ≤ R 0`.
  have hkey : 0 ≤ p.χ₀ * CL := by
    rw [← neg_mul_neg]; exact mul_nonneg (neg_nonneg.2 hχ) (neg_nonneg.2 hCL_nonpos)
  have hG0 : G 0 = Vlim + R 0 - p.χ₀ * CL := by rw [hVlim_def]; ring
  have hfinal : G 0 ≤ R 0 := by rw [hG0]; linarith [hVlim_nonpos, hkey]
  show G 0 ≤ U 0 * (p.a - p.b * (U 0) ^ p.α)
  calc G 0 ≤ R 0 := hfinal
    _ = U 0 * (p.a - p.b * (U 0) ^ p.α) := by simp only [hR_def]

/-- **Boundary (right) maximum 2nd-derivative test.**  Dual of
`boundary_min_deriv2_llimit_nonneg` via `w ↦ −w`. -/
theorem boundary_max_deriv2_llimit_nonpos
    {w : ℝ → ℝ} {η V : ℝ} (hη : 0 < η)
    (hwcont : ContinuousWithinAt w (Set.Iic 1) 1)
    (hmax : ∀ x ∈ Set.Ioo (1 - η) 1, w x ≤ w 1)
    (hd1 : ∀ x ∈ Set.Ioo (1 - η) 1, HasDerivAt w (deriv w x) x)
    (hd2 : ∀ x ∈ Set.Ioo (1 - η) 1, HasDerivAt (deriv w) (deriv (deriv w) x) x)
    (hw'lim : Tendsto (deriv w) (nhdsWithin 1 (Set.Iio 1)) (nhds 0))
    (hw''lim : Tendsto (deriv (deriv w)) (nhdsWithin 1 (Set.Iio 1)) (nhds V)) :
    V ≤ 0 := by
  have hd1neg : deriv (fun y => -w y) = -deriv w := by
    funext y; exact deriv.neg
  have hd2neg : deriv (deriv (fun y => -w y)) = -deriv (deriv w) := by
    rw [hd1neg]; funext y; exact deriv.neg
  have key : 0 ≤ -V := by
    refine boundary_min_deriv2_llimit_nonneg (w := fun y => -w y) (η := η) (V := -V)
      hη hwcont.neg (fun x hx => neg_le_neg (hmax x hx)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [hd1neg]; exact (hd1 x hx).neg
    · intro x hx
      rw [hd1neg, ((hd2 x hx).neg).deriv]; exact (hd2 x hx).neg
    · rw [hd1neg]
      simpa using hw'lim.neg
    · rw [hd2neg]
      exact hw''lim.neg
  linarith

/-- **Boundary max-point estimate at the right endpoint `x = 1`.**  Mirror of
`boundary_max_point_left` via the `x→1⁻` right-limit of the interior PDE. -/
theorem boundary_max_point_right
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmaxlift : ∀ y, intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1) :
    deriv (fun r => intervalDomainLift (u r) 1) t
      ≤ intervalDomainLift (u t) 1
        * (p.a - p.b * (intervalDomainLift (u t) 1) ^ p.α) := by
  have htmem : t ∈ Set.Ioo (0:ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, hNeu, hClosed, hJDt, _⟩ := hsol.regularity
  set U : ℝ → ℝ := intervalDomainLift (u t) with hU_def
  set Vv : ℝ → ℝ := intervalDomainLift (v t) with hVv_def
  have hu_c2 : ContDiffOn ℝ 2 U (Set.Ioo (0:ℝ) 1) := (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 Vv (Set.Ioo (0:ℝ) 1) := (hC2 t htmem).2
  have hu_cont_Icc : ContinuousOn U (Set.Icc (0:ℝ) 1) := (hClosed t htmem).1.1.continuousOn
  have hv_cont_Icc : ContinuousOn Vv (Set.Icc (0:ℝ) 1) := (hClosed t htmem).2.1.continuousOn
  have hNeuU1 : Tendsto (deriv U) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (hNeu t htmem).1.2
  have hNeuV0 : Tendsto (deriv Vv) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).2.1
  have hNeuV1 : Tendsto (deriv Vv) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (hNeu t htmem).2.2
  have h1Icc : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have h01 : (0:ℝ) < 1 := by norm_num
  have hu_pos : ∀ y, 0 < u t y := fun y => hsol.u_pos' ht0 htT
  have hU1_pos : 0 < U 1 := by
    rw [hU_def, intervalDomainLift, dif_pos h1Icc]; exact hu_pos _
  have hv_nn : ∀ y, 0 ≤ Vv y := by
    intro y; rw [hVv_def]; unfold intervalDomainLift; split_ifs with hy
    · exact hsol.v_nonneg ht0 htT
    · exact le_refl 0
  have hpos_v : ∀ y, (0:ℝ) < 1 + Vv y := fun y => by linarith [hv_nn y]
  have hU_le : ∀ y ∈ Set.Ioo (0:ℝ) 1, U y ≤ U 1 := fun y _ => hmaxlift y
  have hU_nonneg : ∀ y, 0 ≤ U y := by
    intro y; rw [hU_def]; unfold intervalDomainLift; split_ifs with hy
    · exact (hsol.u_pos' ht0 htT).le
    · exact le_refl 0
  set G : ℝ → ℝ := fun x => deriv (fun r => intervalDomainLift (u r) x) t with hG_def
  set R : ℝ → ℝ := fun x => U x * (p.a - p.b * (U x) ^ p.α) with hR_def
  set Cfun : ℝ → ℝ :=
    fun x => deriv (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β) x with hCfun_def
  have hfilter : nhdsWithin (1:ℝ) (Set.Ioo 0 1) = nhdsWithin 1 (Set.Iio 1) :=
    nhdsWithin_Ioo_eq_nhdsLT h01
  have hG_lim : Tendsto G (nhdsWithin 1 (Set.Iio 1)) (nhds (G 1)) := by
    have hmaps : Set.MapsTo (fun w => (t, w)) (Set.Icc (0:ℝ) 1)
        (Set.Ioo (0:ℝ) T ×ˢ Set.Icc (0:ℝ) 1) := fun w hw => ⟨htmem, hw⟩
    have hcomp : ContinuousOn G (Set.Icc (0:ℝ) 1) :=
      hJDt.1.comp (Continuous.continuousOn
        (by fun_prop : Continuous fun w : ℝ => (t, w))) hmaps
    rw [← hfilter]
    exact (hcomp 1 h1Icc).mono_left (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hR_lim : Tendsto R (nhdsWithin 1 (Set.Iio 1)) (nhds (R 1)) := by
    have hRcontOn : ContinuousOn R (Set.Icc (0:ℝ) 1) :=
      hu_cont_Icc.mul (continuousOn_const.sub (continuousOn_const.mul
        (hu_cont_Icc.rpow_const (fun x _ => Or.inr p.hα.le))))
    rw [← hfilter]
    exact (hRcontOn 1 h1Icc).mono_left (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  have hUxx_eq : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv U) x = G x - R x + p.χ₀ * Cfun x := by
    intro x hx
    have hmem : (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hx
    have hpu := hsol.pde_u ht0 htT hmem
    have e_td : intervalDomain.timeDeriv u t ⟨x, Set.Ioo_subset_Icc_self hx⟩ = G x := by
      show deriv (fun r => u r ⟨x, Set.Ioo_subset_Icc_self hx⟩) t = G x
      simp only [hG_def]; congr 1; funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    have e_lap : intervalDomain.laplacian (u t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = deriv (deriv U) x := rfl
    have e_cd : intervalDomain.chemotaxisDiv p (u t) (v t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ = Cfun x := rfl
    have e_u : u t (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomainPoint) = U x := by
      rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hx)]
    rw [e_td, e_lap, e_cd, e_u] at hpu
    rw [hR_def]; linarith [hpu]
  have hPDE_v : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv Vv) y = p.μ * Vv y - p.ν * (U y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hy
    have hpv := hsol.pde_v ht0 htT hxy
    have e_lap : intervalDomain.laplacian (v t)
        ⟨y, Set.Ioo_subset_Icc_self hy⟩ = deriv (deriv Vv) y := rfl
    have e_u : u t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) = U y := by
      rw [hU_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    have e_v : v t (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) = Vv y := by
      rw [hVv_def, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    rw [e_lap, e_u, e_v] at hpv
    linarith [hpv]
  set B : ℝ := p.ν * (U 1) ^ p.γ with hBdef
  have hd1V : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ Vv y := by
    intro y hy
    exact (hv_c2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hd2V : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (deriv Vv) y := by
    intro y hy
    exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).2).differentiableAt
  have hSrc : ∀ y ∈ Set.Ioo (0:ℝ) 1, |p.ν * (U y) ^ p.γ| ≤ B := by
    intro y hy
    have hpow : (U y) ^ p.γ ≤ (U 1) ^ p.γ :=
      Real.rpow_le_rpow (hU_nonneg y) (hU_le y hy) p.hγ.le
    have hnn : 0 ≤ p.ν * (U y) ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg (hU_nonneg y) _)
    rw [abs_of_nonneg hnn, hBdef]
    exact mul_le_mul_of_nonneg_left hpow p.hν.le
  have hv_bound := elliptic_sup_bound (w := Vv)
    (Src := fun y => p.ν * (U y) ^ p.γ) (μ := p.μ) (B := B) p.hμ hv_cont_Icc hd1V hd2V
    (by intro y hy; rw [hPDE_v y hy]) hSrc hNeuV0 hNeuV1
  have hμv1 : p.μ * Vv 1 ≤ B := by
    have := hv_bound 1 h1Icc
    rw [le_div_iff₀ p.hμ] at this; rw [mul_comm]; exact this
  set CL : ℝ :=
    0 * (0 * (1 + Vv 1) ^ (-p.β)) + U 1 *
      (-p.β * (1 + Vv 1) ^ (-p.β - 1) * (0:ℝ) ^ 2
        + (1 + Vv 1) ^ (-p.β) * (p.μ * Vv 1 - p.ν * (U 1) ^ p.γ)) with hCL_def
  have hCexpr : ∀ x ∈ Set.Ioo (0:ℝ) 1, Cfun x =
      deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β))
        + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * (U x) ^ p.γ)) := by
    intro x hx
    have hUx : HasDerivAt U (deriv U x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
    have hVx : HasDerivAt Vv (deriv Vv x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).1
    have hVxx : HasDerivAt (deriv Vv) (deriv (deriv Vv) x) x :=
      (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hx).2
    have hP' : HasDerivAt (fun y => deriv Vv y * (1 + Vv y) ^ (-p.β))
        (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (deriv (deriv Vv) x)) x :=
      flux_integrand_hasDerivAt hVx hVxx (hpos_v x)
    have hFeq2 : (fun y => U y * deriv Vv y / (1 + Vv y) ^ p.β)
        = (fun y => U y * (deriv Vv y * (1 + Vv y) ^ (-p.β))) := by
      funext y
      rw [mul_div_assoc, Real.rpow_neg (hpos_v y).le, div_eq_mul_inv]
    have hmul := hUx.mul hP'
    have hCfx : Cfun x = deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β))
        + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (deriv (deriv Vv) x)) := by
      simp only [hCfun_def]
      rw [hFeq2]; exact hmul.deriv
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
  have hrpb : Tendsto (fun x => (1 + Vv x) ^ (-p.β)) (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 + Vv 1) ^ (-p.β))) := h1Vv1L.rpow_const (Or.inl (ne_of_gt (hpos_v 1)))
  have hrpb1 : Tendsto (fun x => (1 + Vv x) ^ (-p.β - 1)) (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 + Vv 1) ^ (-p.β - 1))) := h1Vv1L.rpow_const (Or.inl (ne_of_gt (hpos_v 1)))
  have hUg : Tendsto (fun x => (U x) ^ p.γ) (nhdsWithin 1 (Set.Iio 1))
      (nhds ((U 1) ^ p.γ)) := hU1L.rpow_const (Or.inl (ne_of_gt hU1_pos))
  have hexpr : Tendsto
      (fun x => deriv U x * (deriv Vv x * (1 + Vv x) ^ (-p.β))
        + U x * (-p.β * (1 + Vv x) ^ (-p.β - 1) * (deriv Vv x) ^ 2
          + (1 + Vv x) ^ (-p.β) * (p.μ * Vv x - p.ν * (U x) ^ p.γ)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds CL) := by
    have t1 := hNeuU1.mul (hNeuV1.mul hrpb)
    have t2i1 := ((tendsto_const_nhds (x := -p.β)).mul hrpb1).mul (hNeuV1.pow 2)
    have t2i2 := hrpb.mul ((hVv1L.const_mul p.μ).sub (hUg.const_mul p.ν))
    have t2 := hU1L.mul (t2i1.add t2i2)
    have hsum := t1.add t2
    rw [hCL_def]
    exact hsum
  have hC_lim : Tendsto Cfun (nhdsWithin 1 (Set.Iio 1)) (nhds CL) := by
    refine hexpr.congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hCexpr x hx).symm
  have hCL_nonpos : CL ≤ 0 := by
    have hcpos : (0:ℝ) < (1 + Vv 1) ^ (-p.β) := Real.rpow_pos_of_pos (hpos_v 1) _
    have hfac : p.μ * Vv 1 - p.ν * (U 1) ^ p.γ ≤ 0 := by rw [hBdef] at hμv1; linarith
    rw [hCL_def]
    have e2 : ((0:ℝ) ^ 2) = 0 := by norm_num
    rw [e2]
    have h2 : 0 ≤ U 1 * ((1 + Vv 1) ^ (-p.β) * (p.ν * (U 1) ^ p.γ - p.μ * Vv 1)) :=
      mul_nonneg hU1_pos.le (mul_nonneg hcpos.le (by linarith))
    nlinarith [h2]
  set Vlim : ℝ := G 1 - R 1 + p.χ₀ * CL with hVlim_def
  have hUxx_lim : Tendsto (deriv (deriv U)) (nhdsWithin 1 (Set.Iio 1)) (nhds Vlim) := by
    refine ((hG_lim.sub hR_lim).add (hC_lim.const_mul p.χ₀)).congr' ?_
    rw [← hfilter]
    filter_upwards [self_mem_nhdsWithin] with x hx using (hUxx_eq x hx).symm
  have hwcont : ContinuousWithinAt U (Set.Iic 1) 1 := by
    refine (hu_cont_Icc 1 h1Icc).mono_of_mem_nhdsWithin ?_
    have hIcc_eq : Set.Icc (0:ℝ) 1 = Set.Ici (0:ℝ) ∩ Set.Iic 1 := by
      ext z; simp [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    rw [hIcc_eq]
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h01))
      self_mem_nhdsWithin
  have hd1U : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt U (deriv U x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).1
  have hd2U : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    fun x hx => (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hx).2
  have hII : Set.Ioo (1 - (1:ℝ)) 1 = Set.Ioo (0:ℝ) 1 := by rw [sub_self]
  have hVlim_nonpos : Vlim ≤ 0 :=
    boundary_max_deriv2_llimit_nonpos (w := U) (η := 1) (V := Vlim) h01 hwcont
      (by rw [hII]; exact fun x hx => hU_le x hx)
      (by rw [hII]; exact hd1U)
      (by rw [hII]; exact hd2U)
      hNeuU1 hUxx_lim
  have hkey : 0 ≤ p.χ₀ * CL := by
    rw [← neg_mul_neg]; exact mul_nonneg (neg_nonneg.2 hχ) (neg_nonneg.2 hCL_nonpos)
  have hG1 : G 1 = Vlim + R 1 - p.χ₀ * CL := by rw [hVlim_def]; ring
  have hfinal : G 1 ≤ R 1 := by rw [hG1]; linarith [hVlim_nonpos, hkey]
  show G 1 ≤ U 1 * (p.a - p.b * (U 1) ^ p.α)
  calc G 1 ≤ R 1 := hfinal
    _ = U 1 * (p.a - p.b * (U 1) ^ p.α) := by simp only [hR_def]

/-- At ANY spatial argmax (interior OR boundary) of a classical solution
with χ₀ ≤ 0, the time derivative satisfies u_t ≤ u·(a − b·u^α). -/
theorem max_point_slope_bound
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmax : ∀ y, u t y ≤ u t x) :
    intervalDomain.timeDeriv u t x
      ≤ intervalDomainLift (u t) x.1
        * (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
  rcases lt_or_eq_of_le x.2.1 with h0 | h0
  · rcases lt_or_eq_of_le x.2.2 with h1 | h1
    · exact interior_max_point_of_solution hχ hsol ht0 htT ⟨h0, h1⟩ hmax
    · -- Boundary x = 1: reduce to `boundary_max_point_right`.
      have hx11 : x.1 = 1 := h1
      have hmaxlift : ∀ y, intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1 := by
        intro y
        have hlift1 : intervalDomainLift (u t) 1 = u t x := by
          rw [intervalDomainLift,
            dif_pos (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_refl _⟩)]
          exact congrArg (u t) (Subtype.ext hx11.symm)
        rw [hlift1]
        unfold intervalDomainLift
        split_ifs with hy
        · exact hmax ⟨y, hy⟩
        · exact (hsol.u_pos' ht0 htT (x := x)).le
      have hbmr := boundary_max_point_right hχ hsol ht0 htT hmaxlift
      have htd : intervalDomain.timeDeriv u t x
          = deriv (fun r => intervalDomainLift (u r) 1) t := by
        show deriv (fun s => u s x) t = deriv (fun r => intervalDomainLift (u r) 1) t
        congr 1; funext r
        rw [intervalDomainLift,
          dif_pos (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_refl _⟩)]
        exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
      rw [hx11, htd]
      exact hbmr
  · -- Boundary x = 0: reduce to `boundary_max_point_left`.
    have hx10 : x.1 = 0 := h0.symm
    have hmaxlift : ∀ y, intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0 := by
      intro y
      have hlift0 : intervalDomainLift (u t) 0 = u t x := by
        rw [intervalDomainLift,
          dif_pos (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl _, zero_le_one⟩)]
        exact congrArg (u t) (Subtype.ext hx10.symm)
      rw [hlift0]
      unfold intervalDomainLift
      split_ifs with hy
      · exact hmax ⟨y, hy⟩
      · exact (hsol.u_pos' ht0 htT (x := x)).le
    have hbml := boundary_max_point_left hχ hsol ht0 htT hmaxlift
    have htd : intervalDomain.timeDeriv u t x
        = deriv (fun r => intervalDomainLift (u r) 0) t := by
      show deriv (fun s => u s x) t = deriv (fun r => intervalDomainLift (u r) 0) t
      congr 1; funext r
      rw [intervalDomainLift,
        dif_pos (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl _, zero_le_one⟩)]
      exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
    rw [hx10, htd]
    exact hbml

/-- **Dini → monotonicity core.**  From a per-spatial-argmax nonpositive time
slope on `(0,T)`, the sup-norm trajectory is nonincreasing on `(0,T)`.  Wires
`sliceMax_dini_of_argmax_bound` (Kp = 0) → `supNorm_nonincreasing_of_dini`,
discharging the slice-regularity hypotheses from the regularity conjuncts and
the sup-norm/`sSup`-image bridge. -/
theorem supNorm_nonincr_core
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hub : ∀ s ∈ Set.Ioo (0:ℝ) T, ∀ xs ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u s) xs
          = sSup (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        deriv (fun r => intervalDomainLift (u r) xs) s ≤ 0) :
    SupNormNonincreasingOn intervalDomain u (Set.Ioo (0:ℝ) T) := by
  obtain ⟨_, hTimeReg, _, _, _, hdF6, hSol7⟩ := hsol.regularity
  set F : ℝ → ℝ → ℝ := fun t y => intervalDomainLift (u t) y with hF_def
  have hsupeq : ∀ s ∈ Set.Ioo (0:ℝ) T,
      intervalDomainSupNorm (u s) = sSup (F s '' Set.Icc (0:ℝ) 1) :=
    fun s hs => supNorm_eq_sSup_lift_image (fun q => (hsol.u_pos' hs.1 hs.2).le)
  have hFwin : ∀ {a b : ℝ}, Set.Icc a b ⊆ Set.Ioo (0:ℝ) T →
      ContinuousOn (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) :=
    fun hsub => hSol7.1.mono (Set.prod_mono hsub (le_refl _))
  -- Continuity of the sup-norm on `(0,T)` via local `sliceMax_continuousOn`.
  have hcont : ContinuousOn (fun t => intervalDomainSupNorm (u t)) (Set.Ioo (0:ℝ) T) := by
    have hSSup : ContinuousOn (fun t => sSup (F t '' Set.Icc (0:ℝ) 1))
        (Set.Ioo (0:ℝ) T) := by
      intro x hx
      have ha_pos : 0 < x / 2 := by linarith [hx.1]
      have hb_T : (x + T) / 2 < T := by linarith [hx.2]
      have hax : x / 2 < x := by linarith [hx.1]
      have hxb : x < (x + T) / 2 := by linarith [hx.2]
      have hsub : Set.Icc (x / 2) ((x + T) / 2) ⊆ Set.Ioo (0:ℝ) T := fun s hs =>
        ⟨lt_of_lt_of_le ha_pos hs.1, lt_of_le_of_lt hs.2 hb_T⟩
      exact ((sliceMax_continuousOn (hFwin hsub)) x ⟨hax.le, hxb.le⟩).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hax hxb))
    exact hSSup.congr hsupeq
  -- The one-sided Dini condition.
  have hDini : ∀ x ∈ Set.Ioo (0:ℝ) T, ∀ r : ℝ, 0 < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (intervalDomainSupNorm (u z) - intervalDomainSupNorm (u x)) < r := by
    intro x hx r hr
    have ha_pos : 0 < x / 2 := by linarith [hx.1]
    have hb_T : (x + T) / 2 < T := by linarith [hx.2]
    have hax : x / 2 ≤ x := by linarith [hx.1]
    have hxb : x < (x + T) / 2 := by linarith [hx.2]
    have hsub : Set.Icc (x / 2) ((x + T) / 2) ⊆ Set.Ioo (0:ℝ) T := fun s hs =>
      ⟨lt_of_lt_of_le ha_pos hs.1, lt_of_le_of_lt hs.2 hb_T⟩
    have hFab := hFwin hsub
    have hslice_cont : ∀ y ∈ Set.Icc (0:ℝ) 1,
        ContinuousOn (fun r => F r y) (Set.Icc (x / 2) ((x + T) / 2)) := by
      intro y hy
      have hmaps : Set.MapsTo (fun r => (r, y)) (Set.Icc (x / 2) ((x + T) / 2))
          (Set.Icc (x / 2) ((x + T) / 2) ×ˢ Set.Icc (0:ℝ) 1) := fun w hw => ⟨hw, hy⟩
      exact hFab.comp (Continuous.continuousOn (by fun_prop)) hmaps
    have hslice_diff : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo (x / 2) ((x + T) / 2),
        HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s := by
      intro y hy s hs
      have hsInt : s ∈ Set.Ioo (0:ℝ) T := hsub (Set.Ioo_subset_Icc_self hs)
      have hfun : (fun r => F r y) = fun r => u r ⟨y, hy⟩ := by
        funext r
        show intervalDomainLift (u r) y = u r ⟨y, hy⟩
        rw [intervalDomainLift, dif_pos hy]
      rw [hfun]
      exact ((hTimeReg ⟨y, hy⟩ s hsInt).1.1).hasDerivAt
    have hdFc : ContinuousOn
        (Function.uncurry (fun s y => deriv (fun r => F r y) s))
        (Set.Icc (x / 2) ((x + T) / 2) ×ˢ Set.Icc (0:ℝ) 1) :=
      hdF6.1.mono (Set.prod_mono hsub (le_refl _))
    have hbnd : ∀ s ∈ Set.Icc (x / 2) ((x + T) / 2), ∀ xs ∈ Set.Icc (0:ℝ) 1,
        F s xs = sSup (F s '' Set.Icc (0:ℝ) 1) →
        deriv (fun r => F r xs) s ≤ (0:ℝ) * sSup (F s '' Set.Icc (0:ℝ) 1) := by
      intro s hs xs hxs hargmax
      rw [zero_mul]
      exact hub s (hsub hs) xs hxs hargmax
    have hdini := sliceMax_dini_of_argmax_bound (Kp := 0) hFab hslice_cont hslice_diff
      (sliceMax_continuousOn hFab) hdFc hbnd x ⟨hax, hxb⟩ r (by rw [zero_mul]; exact hr)
    have hev : ∀ᶠ z in nhdsWithin x (Set.Ioi x), z ∈ Set.Ioo (0:ℝ) T := by
      have hmem : Set.Ioo x T ∈ nhdsWithin x (Set.Ioi x) := by
        rw [← Set.Ioi_inter_Iio]
        exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.2)
      filter_upwards [hmem] with z hz
      exact ⟨lt_trans hx.1 hz.1, hz.2⟩
    refine (hdini.and_eventually hev).mono ?_
    rintro z ⟨hzlt, hzmem⟩
    rw [← hsupeq z hzmem, ← hsupeq x hx] at hzlt
    exact hzlt
  exact ShenWork.Paper2.Lemma31Heat.supNorm_nonincreasing_of_dini hcont hDini

/-- The above-capacity branch of Lemma 3.1 for the interval domain. -/
theorem lemma31_above_capacity
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T)
    (hsup : (p.a / p.b) ^ (1 / p.α) < intervalDomain.supNorm (u t₀)) :
    SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t₀) := by
  -- Non-increasing on Ioo(0, t₀) via the same Dini argument as lemma31_zero,
  -- using max_point_slope_bound with the above-capacity reaction bound.
  have hIoo : SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) t₀) :=
    supNorm_nonincr_core p hχ hsol ht₀T
  -- Extend from Ioo to Ioc: for t₁, t₂ ∈ Ioc with t₁ ≤ t₂, need supNorm(t₂) ≤ supNorm(t₁).
  intro t₁ ht₁ t₂ ht₂ hle
  rcases eq_or_lt_of_le ht₂.2 with ht₂eq | ht₂lt
  · -- t₂ = t₀: limit argument.
    rcases eq_or_lt_of_le ht₁.2 with ht₁eq | ht₁lt
    · rw [← ht₂eq, ← ht₁eq]
    · -- t₁ < t₀ = t₂: supNorm continuous on [t₁, t₀], non-increasing on (t₁, t₀).
      -- By continuity at t₀, supNorm(t₀) ≤ supNorm(t₁).
      sorry
  · -- Both in Ioo.
    rcases eq_or_lt_of_le ht₁.2 with ht₁eq | ht₁lt
    · linarith
    · exact hIoo t₁ ⟨ht₁.1, ht₁lt⟩ t₂ ⟨ht₂.1, ht₂lt⟩ hle

/-- The a=b=0 branch of Lemma 3.1 for the interval domain. -/
theorem lemma31_zero
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T) := by
  refine supNorm_nonincr_core hsol ?_
  intro s hs xs hxs hargmax
  -- The spatial argmax point.
  have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
    intro y
    have hcontU : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0:ℝ) 1) := by
      obtain ⟨_, _, _, _, hClosed, _, _⟩ := hsol.regularity
      exact (hClosed s hs).1.1.continuousOn
    have hbdd : BddAbove (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
    have huy : u s y = intervalDomainLift (u s) y.1 := by
      rw [intervalDomainLift,
        dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 from y.2), Subtype.coe_eta]
    have huq : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
      rw [intervalDomainLift, dif_pos hxs]
    rw [huy, huq, hargmax]
    exact le_csSup hbdd (Set.mem_image_of_mem _ y.2)
  have hsl := max_point_slope_bound hχ hsol hs.1 hs.2 hmax
  have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩
      = deriv (fun r => intervalDomainLift (u r) xs) s := by
    show deriv (fun r => u r ⟨xs, hxs⟩) s = deriv (fun r => intervalDomainLift (u r) xs) s
    congr 1; funext r; rw [intervalDomainLift, dif_pos hxs]
  rw [htd, ha, hb] at hsl
  simpa using hsl

end ShenWork.Paper2.Lemma31Closure
