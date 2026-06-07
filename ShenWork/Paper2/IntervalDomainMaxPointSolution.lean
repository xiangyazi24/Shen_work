/-
  Lemma 3.1 (above-capacity / parabolic MAXIMUM principle): the interior
  max-point estimate from a classical solution.

  Mirror of `MinPersistenceAtoms.interior_min_point_of_solution`, but CLEANER:
  at an interior spatial argmax `x*` of `u(t,·)` the chemotaxis divergence is
  `≤ 0` (no `fluxCoeffConst` correction).  The reason is the ELLIPTIC COUPLING
  the naive "obstruction" argument misses: `u(x*) = M = sup u` is exactly where
  `u^γ` is maximal, so the elliptic max-principle bound
  `v ≤ ν M^γ / μ`  (`MinPersistenceAtoms.elliptic_sup_bound`)
  pins `μ·v(x*) ≤ ν·u(x*)^γ`, forcing
  `v_xx(x*) = μ v(x*) − ν u(x*)^γ ≤ 0`,
  hence `chemDiv(x*) = u(x*)·[(1+v)^{−β}v_xx − β(1+v)^{−β−1}v_x²] ≤ 0`.
  Combined with `u_xx(x*) ≤ 0` and `χ₀ ≤ 0`:
    `u_t(t,x*) ≤ u(x*)·(a − b·u(x*)^α)`,
  the clean Hamilton upper slope.  (At the argMIN this coupling does NOT help —
  `u` is small there — which is why the min boundary case was genuinely
  obstructed for `χ₀ < 0`.  The maximum is the easy side.)

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChemDivCritical
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 Filter Topology
open ShenWork.MinPersistenceAtoms
  (elliptic_sup_bound deriv2_nonpos_of_isLocalMax chemDiv_at_critical
   contDiffOn_two_hasDerivAt_pair)

noncomputable section

namespace ShenWork.MaxPrincipleAtoms

/-- The zero-extension lift evaluated at an interior real point. -/
private theorem lift_eq_interior (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- The zero-extension lift attains a local maximum (over `ℝ`) at an interior
spatial argmax. -/
theorem intervalDomainLift_isLocalMax_of_argmax
    {u : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hmax : ∀ y, u y ≤ u x) (hint : x.1 ∈ Set.Ioo (0:ℝ) 1) :
    IsLocalMax (intervalDomainLift u) x.1 := by
  have hxIcc : x.1 ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hint
  have hlift_x : intervalDomainLift u x.1 = u x := by
    rw [intervalDomainLift, dif_pos hxIcc]; congr
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Set.Ioo (0:ℝ) 1, isOpen_Ioo.mem_nhds hint, fun y hy => ?_⟩
  have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
  rw [hlift_x, intervalDomainLift, dif_pos hyIcc]
  exact hmax ⟨y, hyIcc⟩

/-- **Vanishing spatial derivative at an interior argmax.** -/
theorem interior_argmax_deriv_zero
    {u : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hmax : ∀ y, u y ≤ u x) (hint : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hdiff : DifferentiableAt ℝ (intervalDomainLift u) x.1) :
    HasDerivAt (intervalDomainLift u) 0 x.1 := by
  have hlm := intervalDomainLift_isLocalMax_of_argmax hmax hint
  have hz : deriv (intervalDomainLift u) x.1 = 0 := hlm.deriv_eq_zero
  have := hdiff.hasDerivAt
  rwa [hz] at this

/-- **Nonpositive second derivative at an interior argmax.** -/
theorem interior_argmax_deriv2_nonpos
    {u : intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hmax : ∀ y, u y ≤ u x) (hint : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Ioo (0:ℝ) 1)) :
    deriv (deriv (intervalDomainLift u)) x.1 ≤ 0 := by
  have hlm := intervalDomainLift_isLocalMax_of_argmax hmax hint
  have hdiff_ev : ∀ᶠ y in nhds x.1, DifferentiableAt ℝ (intervalDomainLift u) y := by
    filter_upwards [isOpen_Ioo.mem_nhds hint] with y hy
    exact (hu_c2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hy)
  have hf'' := (contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hint).2
  exact deriv2_nonpos_of_isLocalMax hlm hdiff_ev hf''

/-- **Flux coefficient `≤ 0` when `v_xx ≤ 0`.**  Both summands of the
critical-point flux coefficient `G = −β(1+v)^{−β−1}v_x² + (1+v)^{−β}v_xx`
are nonpositive: the first because `β, (1+v)^{−β−1}, v_x² ≥ 0`, the second
because `(1+v)^{−β} > 0` and `v_xx ≤ 0`. -/
theorem flux_coeff_nonpos
    {β v vx vxx : ℝ} (hβ : 0 ≤ β) (hv_nn : 0 ≤ v) (hvxx : vxx ≤ 0) :
    -β * (1 + v) ^ (-β - 1) * vx ^ 2 + (1 + v) ^ (-β) * vxx ≤ 0 := by
  have hpos : (0:ℝ) < 1 + v := by linarith
  have ht1 : -β * (1 + v) ^ (-β - 1) * vx ^ 2 ≤ 0 := by
    have h1 : 0 ≤ β * ((1 + v) ^ (-β - 1) * vx ^ 2) :=
      mul_nonneg hβ (mul_nonneg (Real.rpow_pos_of_pos hpos _).le (sq_nonneg vx))
    have heq : -β * (1 + v) ^ (-β - 1) * vx ^ 2
        = -(β * ((1 + v) ^ (-β - 1) * vx ^ 2)) := by ring
    rw [heq]; linarith
  have ht2 : (1 + v) ^ (-β) * vxx ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_pos_of_pos hpos _).le hvxx
  linarith

/-- **Max-point PDE estimate (abstract form).**  At a spatial argmax (so
`uxx ≤ 0`) where the chemotaxis flux is `≤ 0`, with `χ₀ ≤ 0`, the parabolic
time derivative obeys the clean Hamilton upper slope `uT ≤ m·(a − b·m^α)`. -/
theorem max_point_estimate
    {χ₀ a b α m uxx cd uT : ℝ}
    (hχ : χ₀ ≤ 0) (huxx : uxx ≤ 0) (hcd_nonpos : cd ≤ 0)
    (hpde : uT = uxx - χ₀ * cd + m * (a - b * m ^ α)) :
    uT ≤ m * (a - b * m ^ α) := by
  have h1 : 0 ≤ χ₀ * cd := by
    have h := mul_nonneg (neg_nonneg.2 hχ) (neg_nonneg.2 hcd_nonpos)
    rwa [neg_mul_neg] at h
  rw [hpde]; linarith

/-- **Interior max-point estimate from a classical solution.**  At an interior
spatial argmax `x*` of `u(t,·)`, with `χ₀ ≤ 0`, the parabolic time derivative
obeys the clean reaction-only bound
`u_t(t,x*) ≤ u(x*)·(a − b·u(x*)^α)`.  The chemotaxis term has a definite sign
at the max via the elliptic coupling. -/
theorem interior_max_point_of_solution
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hmax : ∀ y, u t y ≤ u t x) :
    intervalDomain.timeDeriv u t x
      ≤ intervalDomainLift (u t) x.1
        * (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
  have htmem : t ∈ Set.Ioo (0:ℝ) T := ⟨ht0, htT⟩
  -- 7-conjunct `intervalDomainClassicalRegularity`: c1 = spatial C² (Ioo),
  -- c4 = interior Neumann, c5 = closed-Icc C² + endpoint Neumann.
  obtain ⟨hC2, _, _, hNeu, hClosed, _, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0:ℝ) 1) :=
    (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0:ℝ) 1) :=
    (hC2 t htmem).2
  have hv_cont : ContinuousOn (intervalDomainLift (v t)) (Set.Icc (0:ℝ) 1) :=
    (hClosed t htmem).2.1.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (hNeu t htmem).2.2
  -- Positivity / nonnegativity.
  have hu_pos : ∀ y, 0 < u t y := fun y => hsol.u_pos' ht0 htT
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact hsol.v_nonneg ht0 htT
    · exact le_refl 0
  have hux_lift : intervalDomainLift (u t) x.1 = u t x := by
    rw [lift_eq_interior (u t) hint]
    exact congrArg (u t) (Subtype.ext rfl)
  have hM_nonneg : 0 ≤ intervalDomainLift (u t) x.1 := by
    rw [hux_lift]; exact (hu_pos x).le
  -- `u ≤ u(x*)` on the interior (argmax).
  have hu_le_int : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      intervalDomainLift (u t) y ≤ intervalDomainLift (u t) x.1 := by
    intro y hy
    rw [lift_eq_interior (u t) hy, hux_lift]
    exact hmax _
  have hu_nonneg_int : ∀ y ∈ Set.Ioo (0:ℝ) 1, 0 ≤ intervalDomainLift (u t) y := by
    intro y hy; rw [lift_eq_interior (u t) hy]; exact (hu_pos _).le
  -- Elliptic identity from `pde_v`: `v_xx = μ v − ν u^γ`.
  have hPDE_v : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y
        = p.μ * intervalDomainLift (v t) y
          - p.ν * (intervalDomainLift (u t) y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hy
    have hpv := hsol.pde_v ht0 htT hxy
    rw [lift_eq_interior (v t) hy, lift_eq_interior (u t) hy]
    have hlap : intervalDomain.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        = deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  -- Elliptic sup bound: `v ≤ ν·u(x*)^γ / μ` on `[0,1]`.
  set B : ℝ := p.ν * (intervalDomainLift (u t) x.1) ^ p.γ with hBdef
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
  have hd1 : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift (v t)) y := by
    intro y hy
    exact (hv_c2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hy)
  have hd2 : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y := by
    intro y hy
    exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).2).differentiableAt
  have hSrc : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      |p.ν * (intervalDomainLift (u t) y) ^ p.γ| ≤ B := by
    intro y hy
    have huy_nn : 0 ≤ intervalDomainLift (u t) y := hu_nonneg_int y hy
    have huy_le : intervalDomainLift (u t) y ≤ intervalDomainLift (u t) x.1 :=
      hu_le_int y hy
    have hpow : (intervalDomainLift (u t) y) ^ p.γ
        ≤ (intervalDomainLift (u t) x.1) ^ p.γ :=
      Real.rpow_le_rpow huy_nn huy_le p.hγ.le
    have hnn : 0 ≤ p.ν * (intervalDomainLift (u t) y) ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg huy_nn _)
    rw [abs_of_nonneg hnn, hBdef]
    exact mul_le_mul_of_nonneg_left hpow p.hν.le
  have hv_bound := elliptic_sup_bound (w := intervalDomainLift (v t))
    (Src := fun y => p.ν * (intervalDomainLift (u t) y) ^ p.γ)
    (μ := p.μ) (B := B) p.hμ hv_cont hd1 hd2 hPDE_v hSrc hNeu0 hNeu1
  have hvx_le : intervalDomainLift (v t) x.1 ≤ B / p.μ :=
    hv_bound x.1 (Set.Ioo_subset_Icc_self hint)
  have hμv_le : p.μ * intervalDomainLift (v t) x.1 ≤ B := by
    rw [mul_comm]; exact (le_div_iff₀ p.hμ).mp hvx_le
  -- `v_xx(x*) = μ v(x*) − ν u(x*)^γ = μ v(x*) − B ≤ 0`.
  have hvxx_nonpos : deriv (deriv (intervalDomainLift (v t))) x.1 ≤ 0 := by
    rw [hPDE_v x.1 hint, ← hBdef]
    linarith [hμv_le]
  -- Chemotaxis divergence at the critical point.
  have hux0 := interior_argmax_deriv_zero hmax hint
    ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hint).1.differentiableAt)
  have hvpair := contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hint
  have hcd := chemDiv_at_critical (p := p) (u := u t) (v := v t) (x := x)
    hux0 hvpair.1 hvpair.2 hv_nn
  have hG_nonpos := flux_coeff_nonpos (β := p.β)
    (v := intervalDomainLift (v t) x.1)
    (vx := deriv (intervalDomainLift (v t)) x.1)
    (vxx := deriv (deriv (intervalDomainLift (v t))) x.1)
    p.hβ (hv_nn x.1) hvxx_nonpos
  have hcd_nonpos : intervalDomainChemotaxisDiv p (u t) (v t) x ≤ 0 := by
    rw [hcd]
    exact mul_nonpos_of_nonneg_of_nonpos (hu_nonneg_int x.1 hint) hG_nonpos
  -- Second-derivative test for `u`.
  have huxx := interior_argmax_deriv2_nonpos hmax hint hu_c2
  -- PDE value relation.
  have hpde' : intervalDomain.timeDeriv u t x
      = deriv (deriv (intervalDomainLift (u t))) x.1
        - p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x
        + intervalDomainLift (u t) x.1
            * (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
    rw [hux_lift]; exact hsol.pde_u ht0 htT hint
  exact max_point_estimate hχ huxx hcd_nonpos hpde'

end ShenWork.MaxPrincipleAtoms
