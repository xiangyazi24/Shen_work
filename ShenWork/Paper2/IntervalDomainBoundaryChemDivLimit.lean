/-
  Endpoint chemotaxis-divergence limits for the boundary min-persistence
  reducer.

  The literal endpoint value of `intervalDomain.chemotaxisDiv` is a derivative
  of the zero extension, so this file proves the needed one-sided interior
  limits through the closed-slab physical representative from the H1 route.
-/
import ShenWork.Paper2.IntervalDomainBoundaryHboundChiNonpos
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
import ShenWork.Paper2.IntervalDomainVSliceBounds

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

noncomputable section

namespace ShenWork.MinPersistenceAtoms

private theorem lift_eq_interior (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

private theorem nhdsWithin_Ioo_left_neBot :
    (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩)

private theorem nhdsWithin_Ioo_right_neBot :
    (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩)

private theorem v_reaction_left_abs_le
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M') :
    |p.μ * intervalDomainLift (v s) 0
        - p.ν * (intervalDomainLift (u s) 0) ^ p.γ|
      ≤ 2 * (p.ν * M' ^ p.γ) := by
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  obtain ⟨h3, _, _, h6, h7, _, _⟩ := hsol.regularity
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v s)) (Set.Ioo (0 : ℝ) 1) :=
    (h3 s htmem).2
  have hu_c2_closed : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    (h7 s htmem).1.1
  have hv_c2_closed : ContDiffOn ℝ 2 (intervalDomainLift (v s)) (Set.Icc (0 : ℝ) 1) :=
    (h7 s htmem).2.1
  have hu_cont_closed : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    hu_c2_closed.continuousOn
  have hv_cont_closed : ContinuousOn (intervalDomainLift (v s)) (Set.Icc (0 : ℝ) 1) :=
    hv_c2_closed.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v s)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (h6 s htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v s)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (h6 s htmem).2.2
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v s) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg hs0 hsT
    · exact le_refl 0
  have hu_nonneg_int :
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ intervalDomainLift (u s) y := by
    intro y hy
    rw [lift_eq_interior (u s) hy]
    exact (hsol.u_pos' hs0 hsT).le
  have hu_le_int :
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, intervalDomainLift (u s) y ≤ M' := by
    intro y hy
    rw [lift_eq_interior (u s) hy]
    exact hu_le ⟨y, Set.Ioo_subset_Icc_self hy⟩
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v s))) y
        = p.μ * intervalDomainLift (v s) y
          - p.ν * (intervalDomainLift (u s) y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hy
    have hpv := hsol.pde_v hs0 hsT hxy
    rw [lift_eq_interior (v s) hy, lift_eq_interior (u s) hy]
    have hlap : intervalDomain.laplacian (v s)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        = deriv (deriv (intervalDomainLift (v s))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hvb := v_slice_coeff_bounds (p := p) (u := u s) (v := v s) (M' := M')
    hM' hv_c2 hv_cont_closed hv_nn hu_nonneg_int hu_le_int hPDE_v hNeu0 hNeu1
  set F : ℝ → ℝ := fun y =>
    p.μ * intervalDomainLift (v s) y
      - p.ν * (intervalDomainLift (u s) y) ^ p.γ with hF_def
  have hu_pos_Icc :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u s) y := by
    intro y hy
    rw [intervalDomainLift, dif_pos hy]
    exact hsol.u_pos' hs0 hsT
  have hpow_cont :
      ContinuousOn (fun y => (intervalDomainLift (u s) y) ^ p.γ)
        (Set.Icc (0 : ℝ) 1) :=
    hu_cont_closed.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hu_pos_Icc y hy)))
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    rw [hF_def]
    exact (hv_cont_closed.const_mul p.μ).sub (hpow_cont.const_mul p.ν)
  have hF_tend : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
      (nhds (F 0)) :=
    (hF_cont 0 ⟨le_rfl, zero_le_one⟩).mono_left
      (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot :=
    nhdsWithin_Ioo_left_neBot
  have hev : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1),
      |F y| ≤ 2 * (p.ν * M' ^ p.γ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hvxx := hvb.2 y hy
    have hpde := hPDE_v y hy
    simpa [hF_def, hpde] using hvxx
  simpa [hF_def] using le_of_tendsto hF_tend.abs hev

private theorem v_reaction_right_abs_le
    {p : CM2Params} {T s M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) (hM' : 0 ≤ M')
    (hu_le : ∀ x : intervalDomainPoint, u s x ≤ M') :
    |p.μ * intervalDomainLift (v s) 1
        - p.ν * (intervalDomainLift (u s) 1) ^ p.γ|
      ≤ 2 * (p.ν * M' ^ p.γ) := by
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  obtain ⟨h3, _, _, h6, h7, _, _⟩ := hsol.regularity
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v s)) (Set.Ioo (0 : ℝ) 1) :=
    (h3 s htmem).2
  have hu_c2_closed : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    (h7 s htmem).1.1
  have hv_c2_closed : ContDiffOn ℝ 2 (intervalDomainLift (v s)) (Set.Icc (0 : ℝ) 1) :=
    (h7 s htmem).2.1
  have hu_cont_closed : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    hu_c2_closed.continuousOn
  have hv_cont_closed : ContinuousOn (intervalDomainLift (v s)) (Set.Icc (0 : ℝ) 1) :=
    hv_c2_closed.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v s)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := (h6 s htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v s)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := (h6 s htmem).2.2
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v s) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg hs0 hsT
    · exact le_refl 0
  have hu_nonneg_int :
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ intervalDomainLift (u s) y := by
    intro y hy
    rw [lift_eq_interior (u s) hy]
    exact (hsol.u_pos' hs0 hsT).le
  have hu_le_int :
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, intervalDomainLift (u s) y ≤ M' := by
    intro y hy
    rw [lift_eq_interior (u s) hy]
    exact hu_le ⟨y, Set.Ioo_subset_Icc_self hy⟩
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v s))) y
        = p.μ * intervalDomainLift (v s) y
          - p.ν * (intervalDomainLift (u s) y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hy
    have hpv := hsol.pde_v hs0 hsT hxy
    rw [lift_eq_interior (v s) hy, lift_eq_interior (u s) hy]
    have hlap : intervalDomain.laplacian (v s)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        = deriv (deriv (intervalDomainLift (v s))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hvb := v_slice_coeff_bounds (p := p) (u := u s) (v := v s) (M' := M')
    hM' hv_c2 hv_cont_closed hv_nn hu_nonneg_int hu_le_int hPDE_v hNeu0 hNeu1
  set F : ℝ → ℝ := fun y =>
    p.μ * intervalDomainLift (v s) y
      - p.ν * (intervalDomainLift (u s) y) ^ p.γ with hF_def
  have hu_pos_Icc :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u s) y := by
    intro y hy
    rw [intervalDomainLift, dif_pos hy]
    exact hsol.u_pos' hs0 hsT
  have hpow_cont :
      ContinuousOn (fun y => (intervalDomainLift (u s) y) ^ p.γ)
        (Set.Icc (0 : ℝ) 1) :=
    hu_cont_closed.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hu_pos_Icc y hy)))
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    rw [hF_def]
    exact (hv_cont_closed.const_mul p.μ).sub (hpow_cont.const_mul p.ν)
  have hF_tend : Tendsto F (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1))
      (nhds (F 1)) :=
    (hF_cont 1 ⟨zero_le_one, le_rfl⟩).mono_left
      (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)
  haveI : (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot :=
    nhdsWithin_Ioo_right_neBot
  have hev : ∀ᶠ y in nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1),
      |F y| ≤ 2 * (p.ν * M' ^ p.γ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hvxx := hvb.2 y hy
    have hpde := hPDE_v y hy
    simpa [hF_def, hpde] using hvxx
  simpa [hF_def] using le_of_tendsto hF_tend.abs hev

private theorem boundaryChemDivReal_eq_physicalRep_eventually_left
    {p : CM2Params} {T s : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    (fun y : ℝ => boundaryChemDivReal p (u s) (v s) y)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)]
    (fun y : ℝ => liftChemotaxisDivPhysicalRep p u v s y) := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  have h := lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior
    (p := p) (T := T) (u := u) (v := v) hsol htmem hy
  simpa [boundaryChemDivReal, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    using h

private theorem boundaryChemDivReal_eq_physicalRep_eventually_right
    {p : CM2Params} {T s : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    (fun y : ℝ => boundaryChemDivReal p (u s) (v s) y)
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)]
    (fun y : ℝ => liftChemotaxisDivPhysicalRep p u v s y) := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  have h := lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior
    (p := p) (T := T) (u := u) (v := v) hsol htmem hy
  simpa [boundaryChemDivReal, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    using h

set_option maxHeartbeats 8000000 in
-- Reusing the closed-slab physical representative continuity theorem triggers
-- a large reducibility check for the fixed-time slice.
private theorem physicalRep_tendsto_left
    {p : CM2Params} {T s : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    Tendsto (fun y : ℝ => liftChemotaxisDivPhysicalRep p u v s y)
      (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))
      (nhds (liftChemotaxisDivPhysicalRep p u v s 0)) := by
  have hcont2 :=
    liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) (a := s) (b := s)
      hsol hs0 le_rfl hsT
  have hslice : ContinuousOn (fun y : ℝ => liftChemotaxisDivPhysicalRep p u v s y)
      (Set.Icc (0 : ℝ) 1) := by
    have hmap : Set.MapsTo (fun y : ℝ => (s, y)) (Set.Icc (0 : ℝ) 1)
        (Set.Icc s s ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro y hy
      exact ⟨⟨le_rfl, le_rfl⟩, hy⟩
    exact hcont2.comp (Continuous.continuousOn (by fun_prop : Continuous fun y : ℝ => (s, y)))
      hmap
  exact (hslice 0 ⟨le_rfl, zero_le_one⟩).mono_left
    (nhdsWithin_mono 0 Set.Ioo_subset_Icc_self)

set_option maxHeartbeats 8000000 in
-- Same fixed-time slice of the physical representative continuity theorem at
-- the right endpoint.
private theorem physicalRep_tendsto_right
    {p : CM2Params} {T s : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    Tendsto (fun y : ℝ => liftChemotaxisDivPhysicalRep p u v s y)
      (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1))
      (nhds (liftChemotaxisDivPhysicalRep p u v s 1)) := by
  have hcont2 :=
    liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) (a := s) (b := s)
      hsol hs0 le_rfl hsT
  have hslice : ContinuousOn (fun y : ℝ => liftChemotaxisDivPhysicalRep p u v s y)
      (Set.Icc (0 : ℝ) 1) := by
    have hmap : Set.MapsTo (fun y : ℝ => (s, y)) (Set.Icc (0 : ℝ) 1)
        (Set.Icc s s ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro y hy
      exact ⟨⟨le_rfl, le_rfl⟩, hy⟩
    exact hcont2.comp (Continuous.continuousOn (by fun_prop : Continuous fun y : ℝ => (s, y)))
      hmap
  exact (hslice 1 ⟨zero_le_one, le_rfl⟩).mono_left
    (nhdsWithin_mono 1 Set.Ioo_subset_Icc_self)

private theorem physicalRep_left_eq_endpoint_factor
    {p : CM2Params} {T s : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    let m := intervalDomainLift (u s) 0
    let r := p.μ * intervalDomainLift (v s) 0
      - p.ν * (intervalDomainLift (u s) 0) ^ p.γ
    let gchem :=
      -p.β * (1 + intervalDomainLift (v s) 0) ^ (-p.β - 1) * (0 : ℝ) ^ 2
        + (1 + intervalDomainLift (v s) 0) ^ (-p.β) * r
    liftChemotaxisDivPhysicalRep p u v s 0 = m * gchem := by
  intro m r gchem
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  have hdu0 : deriv (intervalDomainLift (u s)) 0 = 0 :=
    intervalDomain_dx_u_left_neumann (params := p) (T := T) (u := u) (v := v)
      hsol htmem
  have hdv0 : deriv (intervalDomainLift (v s)) 0 = 0 :=
    intervalDomain_dx_v_left_neumann (params := p) (T := T) (u := u) (v := v)
      hsol htmem
  have hv0_nonneg : 0 ≤ intervalDomainLift (v s) 0 := by
    rw [intervalDomainLift, dif_pos ⟨le_rfl, zero_le_one⟩]
    exact hsol.v_nonneg hs0 hsT
  have hbase_pos : 0 < 1 + intervalDomainLift (v s) 0 := by linarith
  have hneg :
      (1 + intervalDomainLift (v s) 0) ^ (-p.β) =
        ((1 + intervalDomainLift (v s) 0) ^ p.β)⁻¹ :=
    Real.rpow_neg hbase_pos.le p.β
  unfold liftChemotaxisDivPhysicalRep
  rw [hdu0, hdv0]
  simp [m, r, gchem, div_eq_mul_inv, hneg]
  ring

private theorem physicalRep_right_eq_endpoint_factor
    {p : CM2Params} {T s : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    let m := intervalDomainLift (u s) 1
    let r := p.μ * intervalDomainLift (v s) 1
      - p.ν * (intervalDomainLift (u s) 1) ^ p.γ
    let gchem :=
      -p.β * (1 + intervalDomainLift (v s) 1) ^ (-p.β - 1) * (0 : ℝ) ^ 2
        + (1 + intervalDomainLift (v s) 1) ^ (-p.β) * r
    liftChemotaxisDivPhysicalRep p u v s 1 = m * gchem := by
  intro m r gchem
  have htmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  have hreg := hsol.regularity
  have hdu1 : deriv (intervalDomainLift (u s)) 1 = 0 :=
    (hreg.2.2.2.2.1 s htmem).1.2.2
  have hdv1 : deriv (intervalDomainLift (v s)) 1 = 0 :=
    (hreg.2.2.2.2.1 s htmem).2.2.2
  have hv1_nonneg : 0 ≤ intervalDomainLift (v s) 1 := by
    rw [intervalDomainLift, dif_pos ⟨zero_le_one, le_rfl⟩]
    exact hsol.v_nonneg hs0 hsT
  have hbase_pos : 0 < 1 + intervalDomainLift (v s) 1 := by linarith
  have hneg :
      (1 + intervalDomainLift (v s) 1) ^ (-p.β) =
        ((1 + intervalDomainLift (v s) 1) ^ p.β)⁻¹ :=
    Real.rpow_neg hbase_pos.le p.β
  unfold liftChemotaxisDivPhysicalRep
  rw [hdu1, hdv1]
  simp [m, r, gchem, div_eq_mul_inv, hneg]
  ring

theorem boundaryChemDivLeftLimitBound_of_classicalSolution
    (p : CM2Params) :
    BoundaryChemDivLeftLimitBound p := by
  intro T s M' u v hsol hs0 hsT hM' hu_le
  let r : ℝ := p.μ * intervalDomainLift (v s) 0
    - p.ν * (intervalDomainLift (u s) 0) ^ p.γ
  let gchem : ℝ :=
    -p.β * (1 + intervalDomainLift (v s) 0) ^ (-p.β - 1) * (0 : ℝ) ^ 2
      + (1 + intervalDomainLift (v s) 0) ^ (-p.β) * r
  refine ⟨gchem, ?_, ?_⟩
  · have hv0_nonneg : 0 ≤ intervalDomainLift (v s) 0 := by
      rw [intervalDomainLift, dif_pos ⟨le_rfl, zero_le_one⟩]
      exact hsol.v_nonneg hs0 hsT
    have hr_bd : |r| ≤ 2 * (p.ν * M' ^ p.γ) := by
      simpa [r] using
        v_reaction_left_abs_le (p := p) (T := T) (s := s) (M' := M')
          (u := u) (v := v) hsol hs0 hsT hM' hu_le
    have hB_nonneg : 0 ≤ p.ν * M' ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM' _)
    have hzero_bd : |(0 : ℝ)| ≤ 2 * (p.ν * M' ^ p.γ) := by
      rw [abs_zero]
      nlinarith
    simpa [gchem, r] using
      flux_coeff_bound (β := p.β) (v := intervalDomainLift (v s) 0)
        (vx := (0 : ℝ)) (vxx := r) (B := p.ν * M' ^ p.γ)
        p.hβ hB_nonneg hv0_nonneg hzero_bd hr_bd
  · have hrep := physicalRep_tendsto_left (p := p) (T := T) (s := s)
      (u := u) (v := v) hsol hs0 hsT
    have heq := boundaryChemDivReal_eq_physicalRep_eventually_left
      (p := p) (T := T) (s := s) (u := u) (v := v) hsol hs0 hsT
    have hfac := physicalRep_left_eq_endpoint_factor
      (p := p) (T := T) (s := s) (u := u) (v := v)
      hsol hs0 hsT
    rw [hfac] at hrep
    simpa [gchem, r] using Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hrep

theorem boundaryChemDivRightLimitBound_of_classicalSolution
    (p : CM2Params) :
    BoundaryChemDivRightLimitBound p := by
  intro T s M' u v hsol hs0 hsT hM' hu_le
  let r : ℝ := p.μ * intervalDomainLift (v s) 1
    - p.ν * (intervalDomainLift (u s) 1) ^ p.γ
  let gchem : ℝ :=
    -p.β * (1 + intervalDomainLift (v s) 1) ^ (-p.β - 1) * (0 : ℝ) ^ 2
      + (1 + intervalDomainLift (v s) 1) ^ (-p.β) * r
  refine ⟨gchem, ?_, ?_⟩
  · have hv1_nonneg : 0 ≤ intervalDomainLift (v s) 1 := by
      rw [intervalDomainLift, dif_pos ⟨zero_le_one, le_rfl⟩]
      exact hsol.v_nonneg hs0 hsT
    have hr_bd : |r| ≤ 2 * (p.ν * M' ^ p.γ) := by
      simpa [r] using
        v_reaction_right_abs_le (p := p) (T := T) (s := s) (M' := M')
          (u := u) (v := v) hsol hs0 hsT hM' hu_le
    have hB_nonneg : 0 ≤ p.ν * M' ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM' _)
    have hzero_bd : |(0 : ℝ)| ≤ 2 * (p.ν * M' ^ p.γ) := by
      rw [abs_zero]
      nlinarith
    simpa [gchem, r] using
      flux_coeff_bound (β := p.β) (v := intervalDomainLift (v s) 1)
        (vx := (0 : ℝ)) (vxx := r) (B := p.ν * M' ^ p.γ)
        p.hβ hB_nonneg hv1_nonneg hzero_bd hr_bd
  · have hrep := physicalRep_tendsto_right (p := p) (T := T) (s := s)
      (u := u) (v := v) hsol hs0 hsT
    have heq := boundaryChemDivReal_eq_physicalRep_eventually_right
      (p := p) (T := T) (s := s) (u := u) (v := v) hsol hs0 hsT
    have hfac := physicalRep_right_eq_endpoint_factor
      (p := p) (T := T) (s := s) (u := u) (v := v)
      hsol hs0 hsT
    rw [hfac] at hrep
    simpa [gchem, r] using Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hrep

theorem boundaryChemDivEndpointLimitBounds_of_classicalSolution
    (p : CM2Params) :
    BoundaryChemDivEndpointLimitBounds p where
  left := boundaryChemDivLeftLimitBound_of_classicalSolution p
  right := boundaryChemDivRightLimitBound_of_classicalSolution p

end ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper2.BFormPositiveDatumLocal

theorem boundaryMinPersistenceWindowEndpointBounds_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    BoundaryMinPersistenceWindowEndpointBounds p :=
  boundaryMinPersistenceWindowEndpointBounds_of_chemDivEndpointLimits
    p hχ ha hb
    (ShenWork.MinPersistenceAtoms.boundaryChemDivEndpointLimitBounds_of_classicalSolution p)

theorem boundaryMinPersistenceWindowBound_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    BoundaryMinPersistenceWindowBound p :=
  boundaryMinPersistenceWindowBound_of_endpointBounds
    (boundaryMinPersistenceWindowEndpointBounds_chiNonpos p hχ ha hb)

/-- Base B-form quantitative local existence with the general-chi windowed
boundary persistence producer supplied internally. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary_window_chiNonpos_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_boundary_window_of_BForm
    p hχ ha hb hα_ge hγ_ge_one hPF
    (boundaryMinPersistenceWindowBound_chiNonpos p hχ ha hb)
    hBForm

/-- Base B-form quantitative local existence with Picard-limit restart and the
general-chi windowed boundary persistence producer supplied internally. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_chiNonpos_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_of_BForm
    p hχ ha hb hα_ge hγ_ge_one hPLF
    (boundaryMinPersistenceWindowBound_chiNonpos p hχ ha hb)
    hBForm

/-- Base B-form headline with Picard restart and the general-chi windowed
boundary persistence producer supplied internally. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_from_quant p hχ ha hb hγ_ge_one hBForm
    (quantitativeLocalExistence_of_picardFrontier_boundary_window_chiNonpos_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPF hBForm)

/-- Base B-form headline with Picard-limit restart and the general-chi windowed
boundary persistence producer supplied internally. -/
theorem paper2_theorem_1_1_general_chi_bform_from_picardLimitFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHyp p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_from_quant p hχ ha hb hγ_ge_one hBForm
    (quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_chiNonpos_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hBForm)

end ShenWork.Paper2.BFormPositiveDatumLocal

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Negative-part B-form quantitative local existence with the general-chi
windowed boundary persistence producer supplied internally. -/
theorem quantitativeLocalExistence_of_picardFrontier_boundary_window_chiNonpos_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardFrontier_boundary_window_of_BForm
    p hχ ha hb hα_ge hγ_ge_one hPF
    (ShenWork.Paper2.BFormPositiveDatumLocal.boundaryMinPersistenceWindowBound_chiNonpos
      p hχ ha hb)
    hPerDatum

/-- Negative-part B-form quantitative local existence with Picard-limit restart
and the general-chi windowed boundary persistence producer supplied internally. -/
theorem quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_chiNonpos_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_of_BForm
    p hχ ha hb hα_ge hγ_ge_one hPLF
    (ShenWork.Paper2.BFormPositiveDatumLocal.boundaryMinPersistenceWindowBound_chiNonpos
      p hχ ha hb)
    hPerDatum

/-- Negative-part B-form headline with Picard restart and the general-chi
windowed boundary persistence producer supplied internally. -/
theorem paper2_theorem_1_1_general_chi_bform_negpart_from_picardFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart_from_quant
    p hχ ha hb hγ_ge_one hPerDatum
    (quantitativeLocalExistence_of_picardFrontier_boundary_window_chiNonpos_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPF hPerDatum)

/-- Negative-part B-form headline with Picard-limit restart and the general-chi
windowed boundary persistence producer supplied internally. -/
theorem
    paper2_theorem_1_1_general_chi_bform_negpart_from_picardLimitFrontier_boundary_window_of_BForm
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPositiveLocalFrontier p)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_negpart_from_quant
    p hχ ha hb hγ_ge_one hPerDatum
    (quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_chiNonpos_of_BForm
      p hχ ha hb hα_ge hγ_ge_one hPLF hPerDatum)

end ShenWork.Paper2.BFormPositiveDatumNegPart
