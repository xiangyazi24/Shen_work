/-
  B2 (MinPersistence): interior min-point estimate from a classical solution.

  The Phase-A capstone: projects the `IsPaper2ClassicalSolution` conjuncts
  (spatial `C²`, `pde_v` elliptic identity, Neumann endpoints, positivity,
  `v ≥ 0`, the `pde_u` PDE) at an interior time/argmin into
  `min_point_estimate_interior`, yielding
    `−K·u(t,x*) ≤ u_t(t,x*)`,   `K := |χ₀|·K₁(νM'^γ) + b·M'^α`,
  the slab-independent Hamilton slope.  The `u`-sup bound `|u(t,·)| ≤ M'`
  (the `hSupNorm`/regimeBound output) is taken as a hypothesis.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPointInterior
import ShenWork.Paper2.IntervalDomainVSliceBounds
import ShenWork.Paper2.IntervalDomainInteriorArgmin
import ShenWork.Paper2.IntervalDomainInteriorDeriv2
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- The zero-extension lift evaluated at an interior real point. -/
private theorem lift_eq_interior (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- **Interior min-point estimate from a classical solution.** -/
theorem interior_min_point_of_solution_allChi
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint} {M' : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hmin : ∀ y, u t x ≤ u t y)
    (hM' : 0 ≤ M')
    (hu_bd : ∀ y, |intervalDomainLift (u t) y| ≤ M') :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α) * (u t x)
      ≤ intervalDomain.timeDeriv u t x := by
  have htmem : t ∈ Set.Ioo (0:ℝ) T := ⟨ht0, htT⟩
  obtain ⟨h3, _, _, h6, h7, _, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0:ℝ) 1) :=
    (h3 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0:ℝ) 1) :=
    (h3 t htmem).2
  have hv_cont : ContinuousOn (intervalDomainLift (v t)) (Set.Icc (0:ℝ) 1) :=
    (h7 t htmem).2.1.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (h6 t htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (h6 t htmem).2.2
  -- Positivity / nonnegativity.
  have hu_pos : ∀ y, 0 < u t y := fun y => hsol.u_pos' ht0 htT
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact hsol.v_nonneg ht0 htT
    · exact le_refl 0
  have hu_nonneg_int : ∀ y ∈ Set.Ioo (0:ℝ) 1, 0 ≤ intervalDomainLift (u t) y := by
    intro y hy; rw [lift_eq_interior (u t) hy]; exact (hu_pos _).le
  have hu_le_int : ∀ y ∈ Set.Ioo (0:ℝ) 1, intervalDomainLift (u t) y ≤ M' :=
    fun y _ => le_trans (le_abs_self _) (hu_bd y)
  -- Elliptic identity from `pde_v`.
  have hPDE_v : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y
        = p.μ * intervalDomainLift (v t) y
          - p.ν * (intervalDomainLift (u t) y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hy
    have hpv := hsol.pde_v ht0 htT hxy
    rw [lift_eq_interior (v t) hy, lift_eq_interior (u t) hy]
    -- `laplacian (v t) ⟨y⟩ = deriv² (lift (v t)) y` definitionally.
    have hlap : intervalDomain.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        = deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  -- v-slice coefficient bounds.
  have hvb := v_slice_coeff_bounds (p := p) (u := u t) (v := v t) (M' := M')
    hM' hv_c2 hv_cont hv_nn hu_nonneg_int hu_le_int hPDE_v hNeu0 hNeu1
  -- Pointwise data at `x`.
  have hux := interior_argmin_deriv_zero hmin hint
    ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hint).1.differentiableAt)
  have hvpair := contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hint
  have huxx := interior_argmin_deriv2_nonneg hmin hint hu_c2
  have hux_lift : intervalDomainLift (u t) x.1 = u t x := by
    rw [lift_eq_interior (u t) hint]
    exact congrArg (u t) (Subtype.ext rfl)
  -- PDE relation.
  have hpde := hsol.pde_u ht0 htT hint
  have hpde' : intervalDomain.timeDeriv u t x
      = deriv (deriv (intervalDomainLift (u t))) x.1
        - p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x
        + intervalDomainLift (u t) x.1
            * (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
    rw [hux_lift]; exact hpde
  -- Assemble.
  have hmain := min_point_estimate_interior_allChi (p := p) (u := u t) (v := v t) (x := x)
    (M' := M') (uT := intervalDomain.timeDeriv u t x)
    hux hvpair.1 hvpair.2 hv_nn hM'
    (hvb.1 x.1 hint) (hvb.2 x.1 hint)
    (hu_nonneg_int x.1 hint) (hu_le_int x.1 hint)
    huxx hpde'
  rwa [hux_lift] at hmain

/-- Compatibility wrapper for the former nonpositive-sensitivity API. -/
theorem interior_min_point_of_solution
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint} {M' : ℝ}
    (_hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0:ℝ) 1)
    (hmin : ∀ y, u t x ≤ u t y)
    (hM' : 0 ≤ M')
    (hu_bd : ∀ y, |intervalDomainLift (u t) y| ≤ M') :
    -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α) * (u t x)
      ≤ intervalDomain.timeDeriv u t x :=
  interior_min_point_of_solution_allChi hsol ht0 htT hint hmin hM' hu_bd

end ShenWork.MinPersistenceAtoms
