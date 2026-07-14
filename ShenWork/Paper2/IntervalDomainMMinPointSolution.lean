/-
  Interior minimum estimate for faithful general-m classical solutions.
-/
import ShenWork.Paper2.IntervalDomainMChemDivCritical
import ShenWork.Paper2.IntervalDomainVSliceBounds
import ShenWork.Paper2.IntervalDomainInteriorArgmin
import ShenWork.Paper2.IntervalDomainInteriorDeriv2
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 Filter Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMMinPersistence

private theorem lift_eq_interior (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- Interior minimum estimate projected from a faithful general-`m` classical
solution, retaining its positive linear growth. -/
theorem interior_min_point_of_solution_M_allChi_with_growth
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint} {M : ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hmin : ∀ y, u t x ≤ u t y)
    (hM : 0 ≤ M)
    (hu_bd : ∀ y, |intervalDomainLift (u t) y| ≤ M) :
    generalMMinGrowthRate p M * u t x ≤ intervalDomain.timeDeriv u t x := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨h3, _, _, h6, h7, _, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Set.Ioo (0 : ℝ) 1) := (h3 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t))
      (Set.Ioo (0 : ℝ) 1) := (h3 t htmem).2
  have hv_cont : ContinuousOn (intervalDomainLift (v t))
      (Set.Icc (0 : ℝ) 1) := (h7 t htmem).2.1.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (h6 t htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (h6 t htmem).2.2
  have hu_pos : ∀ y, 0 < u t y := fun y => hsol.u_pos' ht0 htT
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hu_nonneg_int : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ intervalDomainLift (u t) y := by
    intro y hy
    rw [lift_eq_interior (u t) hy]
    exact (hu_pos _).le
  have hu_le_int : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ M :=
    fun y _ => (le_abs_self _).trans (hu_bd y)
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y =
        p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) ∈
        intervalDomainM.inside := hy
    have hpv := hsol.pde_v ht0 htT hxy
    rw [lift_eq_interior (v t) hy, lift_eq_interior (u t) hy]
    have hlap : intervalDomainM.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) =
          deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hvb := ShenWork.MinPersistenceAtoms.v_slice_coeff_bounds
    (p := p) (u := u t) (v := v t) (M' := M)
    hM hv_c2 hv_cont hv_nn hu_nonneg_int hu_le_int hPDE_v hNeu0 hNeu1
  have hux := ShenWork.MinPersistenceAtoms.interior_argmin_deriv_zero
    hmin hint
      ((ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
        isOpen_Ioo hu_c2 hint).1.differentiableAt)
  have hvpair := ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
    isOpen_Ioo hv_c2 hint
  have huxx := ShenWork.MinPersistenceAtoms.interior_argmin_deriv2_nonneg
    hmin hint hu_c2
  have hux_lift : intervalDomainLift (u t) x.1 = u t x := by
    rw [lift_eq_interior (u t) hint]
    exact congrArg (u t) (Subtype.ext rfl)
  have hpde := hsol.pde_u ht0 htT hint
  have hpde' : intervalDomain.timeDeriv u t x =
      deriv (deriv (intervalDomainLift (u t))) x.1 -
        p.χ₀ * intervalDomainChemotaxisDivM p (u t) (v t) x +
        intervalDomainLift (u t) x.1 *
          (p.a - p.b * intervalDomainLift (u t) x.1 ^ p.α) := by
    rw [hux_lift]
    exact hpde
  have hmain := min_point_estimate_interior_M_allChi_with_growth
    (p := p) (u := u t) (v := v t) (x := x)
    (M := M) (uT := intervalDomain.timeDeriv u t x)
    hm hux hvpair.1 hvpair.2 hv_nn hM
    (hvb.1 x.1 hint) (hvb.2 x.1 hint)
    (by simpa [hux_lift] using hu_pos x) (hu_le_int x.1 hint)
    huxx hpde'
  rwa [hux_lift] at hmain

/-- Historical interior minimum estimate with the nonnegative linear reaction
discarded. -/
theorem interior_min_point_of_solution_M_allChi
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint} {M : ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hmin : ∀ y, u t x ≤ u t y)
    (hM : 0 ≤ M)
    (hu_bd : ∀ y, |intervalDomainLift (u t) y| ≤ M) :
    -generalMMinSlopeConst p M * u t x ≤ intervalDomain.timeDeriv u t x := by
  have hgrowth := interior_min_point_of_solution_M_allChi_with_growth
    hm hsol ht0 htT hint hmin hM hu_bd
  unfold generalMMinGrowthRate at hgrowth
  nlinarith [mul_nonneg p.ha (hsol.u_pos' ht0 htT (x := x)).le]

/-- Interior minimum estimate in the exact Hamilton-bound shape. -/
theorem hbound_interior_M_allChi_with_growth
    {p : CM2Params} {T s M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_bd : ∀ y, |intervalDomainLift (u s) y| ≤ M)
    {ys : ℝ} (hys_int : ys ∈ Set.Ioo (0 : ℝ) 1)
    (hargmin : intervalDomainLift (u s) ys =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1)) :
    generalMMinGrowthRate p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) ys) s := by
  let x : intervalDomainPoint := ⟨ys, Set.Ioo_subset_Icc_self hys_int⟩
  have hlift_x : intervalDomainLift (u s) ys = u s x := by
    rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hys_int)]
  have husx_eq : u s x =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
    rw [← hlift_x]
    exact hargmin
  have hslice_cont : ContinuousOn (intervalDomainLift (u s))
      (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 s ⟨hs0, hsT⟩).1.1.continuousOn
  have hbdd : BddBelow
      (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hslice_cont).bddBelow
  have hmin : ∀ z : intervalDomainPoint, u s x ≤ u s z := by
    intro z
    have hz_lift : intervalDomainLift (u s) z.1 = u s z := by
      simp only [intervalDomainLift, Subtype.coe_eta]
      exact dif_pos z.2
    rw [husx_eq, ← hz_lift]
    exact csInf_le hbdd (Set.mem_image_of_mem _ z.2)
  have hmp := interior_min_point_of_solution_M_allChi_with_growth
    hm hsol hs0 hsT hys_int hmin hM hu_bd
  have htd_eq : intervalDomain.timeDeriv u s x =
      deriv (fun r => intervalDomainLift (u r) ys) s := by
    have hfun : (fun r => u r x) =
        (fun r => intervalDomainLift (u r) ys) := by
      funext r
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hys_int)]
    show deriv (fun r => u r x) s = _
    rw [hfun]
  rw [htd_eq, husx_eq] at hmp
  exact hmp

/-- Historical interior Hamilton bound with the nonnegative linear reaction
discarded. -/
theorem hbound_interior_M_allChi
    {p : CM2Params} {T s M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM : 0 ≤ M)
    (hu_bd : ∀ y, |intervalDomainLift (u s) y| ≤ M)
    {ys : ℝ} (hys_int : ys ∈ Set.Ioo (0 : ℝ) 1)
    (hargmin : intervalDomainLift (u s) ys =
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1)) :
    -generalMMinSlopeConst p M *
        sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
      deriv (fun r => intervalDomainLift (u r) ys) s := by
  have hgrowth := hbound_interior_M_allChi_with_growth hm hsol hs0 hsT hM
    hu_bd hys_int hargmin
  have hmin_nonneg : 0 ≤
      sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
    rw [← hargmin]
    have hysIcc : ys ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hys_int
    simpa [intervalDomainLift, hysIcc] using
      (hsol.u_pos'
        (x := (⟨ys, hysIcc⟩ : intervalDomainPoint)) hs0 hsT).le
  unfold generalMMinGrowthRate at hgrowth
  nlinarith [mul_nonneg p.ha hmin_nonneg]

section AxiomAudit

#print axioms interior_min_point_of_solution_M_allChi_with_growth
#print axioms interior_min_point_of_solution_M_allChi
#print axioms hbound_interior_M_allChi_with_growth
#print axioms hbound_interior_M_allChi

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMMinPersistence
