import ShenWork.Paper3.IntervalDomainPersistenceLiminfBounds
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomain_infValue_v_isCoboundedUnder_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (v t)) := by
  rcases hsol.bounded with ⟨M, hM⟩
  set M0 : ℝ := max M 0
  set B : ℝ := p.ν * M0 ^ p.γ
  have hceil :
      ∀ᶠ t in atTop, intervalDomain.infValue (v t) ≤ B / p.μ := by
    filter_upwards [hM, eventually_ge_atTop (1 : ℝ)] with t hMt ht1
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hTpos : 0 < t + 1 := by linarith
    have hclass := hsol.classical.classical (T := t + 1) hTpos
    have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htpos, by linarith⟩
    obtain ⟨h3, _, _, h6, h7, _, _⟩ := hclass.regularity
    have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0 : ℝ) 1) :=
      (h3 t htmem).2
    have hv_cont : ContinuousOn (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) :=
      (h7 t htmem).2.1.continuousOn
    have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := (h6 t htmem).2.1
    have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := (h6 t htmem).2.2
    have hd1 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (intervalDomainLift (v t)) y := by
      intro y hy
      exact (hv_c2.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hy)
    have hd2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y := by
      intro y hy
      exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hy).2).differentiableAt
    have hPDE : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        deriv (deriv (intervalDomainLift (v t))) y =
          p.μ * intervalDomainLift (v t) y -
            p.ν * (intervalDomainLift (u t) y) ^ p.γ := by
      intro y hy
      let xy : intervalDomain.Point := ⟨y, Set.Ioo_subset_Icc_self hy⟩
      have hpv := hclass.pde_v htpos (by linarith : t < t + 1) (x := xy) hy
      have hlap : intervalDomain.laplacian (v t) xy =
          deriv (deriv (intervalDomainLift (v t))) y := rfl
      have hv_eq : intervalDomainLift (v t) y = v t xy := by
        rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
      have hu_eq : intervalDomainLift (u t) y = u t xy := by
        rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
      rw [hlap, ← hv_eq, ← hu_eq] at hpv
      linarith [hpv]
    have hSrc : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |p.ν * (intervalDomainLift (u t) y) ^ p.γ| ≤ B := by
      intro y hy
      let xy : intervalDomain.Point := ⟨y, Set.Ioo_subset_Icc_self hy⟩
      have hu_eq : intervalDomainLift (u t) y = u t xy := by
        rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
      have hu_nn : 0 ≤ intervalDomainLift (u t) y := by
        rw [hu_eq]
        exact (hclass.u_pos' htpos (by linarith : t < t + 1) (x := xy)).le
      have habsM : |intervalDomainLift (u t) y| ≤ M :=
        (abs_lift_le_supNorm hclass htmem (Set.Ioo_subset_Icc_self hy)).trans hMt
      have hu_le : intervalDomainLift (u t) y ≤ M0 :=
        (le_trans (le_abs_self _) habsM).trans (le_max_left _ _)
      have hpow : (intervalDomainLift (u t) y) ^ p.γ ≤ M0 ^ p.γ :=
        Real.rpow_le_rpow hu_nn hu_le p.hγ.le
      have hnn : 0 ≤ p.ν * (intervalDomainLift (u t) y) ^ p.γ :=
        mul_nonneg p.hν.le (Real.rpow_nonneg hu_nn _)
      simpa [B, abs_of_nonneg hnn] using
        mul_le_mul_of_nonneg_left hpow p.hν.le
    have hv_bound := elliptic_sup_bound (w := intervalDomainLift (v t))
      (Src := fun y => p.ν * (intervalDomainLift (u t) y) ^ p.γ)
      (μ := p.μ) (B := B) p.hμ hv_cont hd1 hd2 hPDE hSrc hNeu0 hNeu1
    let x0 : intervalDomain.Point := ⟨0, by exact ⟨le_rfl, by norm_num⟩⟩
    have hv0 : v t x0 ≤ B / p.μ := by
      have hv0_lift : intervalDomainLift (v t) 0 = v t x0 := by
        simp [intervalDomainLift, x0]
      simpa [hv0_lift] using hv_bound 0 (by exact ⟨le_rfl, by norm_num⟩)
    change sInf (Set.range (v t)) ≤ B / p.μ
    have hbdd : BddBelow (Set.range (v t)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨x, rfl⟩
      exact hclass.v_nonneg htpos (by linarith : t < t + 1) (x := x)
    exact (csInf_le hbdd ⟨x0, rfl⟩).trans hv0
  exact isCoboundedUnder_ge_of_eventually_le atTop hceil
end
end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.intervalDomain_infValue_v_isCoboundedUnder_of_positiveGlobalBoundedSolution
