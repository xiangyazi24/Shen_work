import ShenWork.Paper3.Statements
import ShenWork.Paper2.IntervalDomainC2Extraction

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.MinPersistenceAtoms (contDiffOn_two_hasDerivAt_pair)

namespace ShenWork.Paper3

noncomputable section

private theorem deriv_neg_right_of_deriv2_neg_of_pivot
    {w : ℝ → ℝ} {a eta : ℝ} (_heta : 0 < eta)
    (hd1 : ∀ y ∈ Set.Ioo a (a + eta), DifferentiableAt ℝ (deriv w) y)
    (hd2neg : ∀ y ∈ Set.Ioo a (a + eta), deriv (deriv w) y < 0)
    (hpivot : Filter.Tendsto (deriv w) (nhdsWithin a (Set.Ioi a)) (nhds 0)) :
    ∀ y ∈ Set.Ioo a (a + eta), deriv w y < 0 := by
  have hanti : ∀ z y, a < z → z < y → y < a + eta → deriv w y < deriv w z := by
    intro z y hz hzy hy
    have hstrict : StrictAntiOn (deriv w) (Set.Icc z y) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · intro r hr
        exact ((hd1 r ⟨lt_of_lt_of_le hz hr.1,
          lt_of_le_of_lt hr.2 hy⟩).continuousAt).continuousWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        exact hd2neg r ⟨lt_trans hz hr.1, lt_trans hr.2 hy⟩
    exact hstrict (Set.left_mem_Icc.mpr hzy.le)
      (Set.right_mem_Icc.mpr hzy.le) hzy
  intro y hy
  set y' : ℝ := a + (y - a) / 2 with hy'_def
  have hay' : a < y' := by
    have := hy.1
    simp only [hy'_def]
    linarith
  have hy'y : y' < y := by
    have := hy.1
    simp only [hy'_def]
    linarith
  have hy'_nonpos : deriv w y' ≤ 0 := by
    apply ge_of_tendsto hpivot
    filter_upwards [Ioo_mem_nhdsGT hay'] with z hz
    exact (hanti z y' hz.1 hz.2 (lt_trans hy'y hy.2)).le
  exact lt_of_lt_of_le (hanti y' y hay' hy'y hy.2) hy'_nonpos

private theorem deriv_pos_left_of_deriv2_neg_of_pivot
    {w : ℝ → ℝ} {b eta : ℝ} (_heta : 0 < eta)
    (hd1 : ∀ y ∈ Set.Ioo (b - eta) b, DifferentiableAt ℝ (deriv w) y)
    (hd2neg : ∀ y ∈ Set.Ioo (b - eta) b, deriv (deriv w) y < 0)
    (hpivot : Filter.Tendsto (deriv w) (nhdsWithin b (Set.Iio b)) (nhds 0)) :
    ∀ y ∈ Set.Ioo (b - eta) b, 0 < deriv w y := by
  have hanti : ∀ z y, b - eta < z → z < y → y < b → deriv w y < deriv w z := by
    intro z y hz hzy hy
    have hstrict : StrictAntiOn (deriv w) (Set.Icc z y) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · intro r hr
        exact ((hd1 r ⟨lt_of_lt_of_le hz hr.1,
          lt_of_le_of_lt hr.2 hy⟩).continuousAt).continuousWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        exact hd2neg r ⟨lt_trans hz hr.1, lt_trans hr.2 hy⟩
    exact hstrict (Set.left_mem_Icc.mpr hzy.le)
      (Set.right_mem_Icc.mpr hzy.le) hzy
  intro y hy
  set y' : ℝ := b - (b - y) / 2 with hy'_def
  have hyy' : y < y' := by
    have := hy.2
    simp only [hy'_def]
    linarith
  have hy'b : y' < b := by
    have := hy.2
    simp only [hy'_def]
    linarith
  have hy'_nonneg : 0 ≤ deriv w y' := by
    apply le_of_tendsto hpivot
    filter_upwards [Ioo_mem_nhdsLT hy'b] with z hz
    exact (hanti y' z (lt_trans hy.1 hyy') hz.1 hz.2).le
  exact lt_of_le_of_lt hy'_nonneg (hanti y y' hy.1 hyy' hy'b)

set_option maxHeartbeats 800000 in
-- The proof splits the compact-interval minimum into both endpoints and the interior.
theorem interval_elliptic_lower_bound_of_source_ge
    {V Src : ℝ → ℝ} {mu c0 : ℝ} (hmu : 0 < mu)
    (hcont : ContinuousOn V (Set.Icc (0 : ℝ) 1))
    (hd2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (deriv V) y)
    (hPDE : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv V) y = mu * V y - Src y)
    (hSrc : ∀ y ∈ Set.Ioo (0 : ℝ) 1, c0 ≤ Src y)
    (hNeu0 : Filter.Tendsto (deriv V) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hNeu1 : Filter.Tendsto (deriv V) (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, c0 / mu ≤ V x := by
  obtain ⟨x0, hx0_mem, hx0_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ hcont
  suffices hmin : c0 / mu ≤ V x0 by
    intro x hx
    exact le_trans hmin (hx0_min hx)
  by_contra hlt
  push Not at hlt
  have hneg_at : ∀ y ∈ Set.Ioo (0 : ℝ) 1, V y < c0 / mu →
      deriv (deriv V) y < 0 := by
    intro y hy hVy
    rw [hPDE y hy]
    have h1 : mu * V y < c0 := by
      have := (lt_div_iff₀ hmu).mp hVy
      linarith
    linarith [hSrc y hy]
  have hev : ∀ᶠ y in nhdsWithin x0 (Set.Icc (0 : ℝ) 1), V y < c0 / mu :=
    (hcont x0 hx0_mem).eventually_lt_const hlt
  rw [Filter.eventually_iff, mem_nhdsWithin] at hev
  obtain ⟨U, hU_open, hx0U, hUsub⟩ := hev
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hU_open x0 hx0U
  have hlt_near : ∀ y, |y - x0| < eps → y ∈ Set.Icc (0 : ℝ) 1 →
      V y < c0 / mu := by
    intro y hyeps hy01
    apply hUsub
    refine ⟨hball ?_, hy01⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hyeps
  rcases lt_or_eq_of_le hx0_mem.1 with h0x | h0x
  · rcases lt_or_eq_of_le hx0_mem.2 with hx1 | hx1
    · have hx0_in : x0 ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0x, hx1⟩
      set eta : ℝ := min (eps / 2) ((1 - x0) / 2) with heta_def
      have heta : 0 < eta := lt_min (by linarith) (by linarith)
      have hsub : Set.Ioo x0 (x0 + eta) ⊆ Set.Ioo (0 : ℝ) 1 := by
        intro y hy
        have h1 : eta ≤ (1 - x0) / 2 := min_le_right _ _
        exact ⟨lt_trans h0x hy.1, by linarith [hy.2]⟩
      have hd2neg : ∀ y ∈ Set.Ioo x0 (x0 + eta), deriv (deriv V) y < 0 := by
        intro y hy
        apply hneg_at y (hsub hy)
        apply hlt_near
        · rw [abs_sub_lt_iff]
          have h1 : eta ≤ eps / 2 := min_le_left _ _
          constructor <;> linarith [hy.1, hy.2, heps]
        · exact Set.Ioo_subset_Icc_self (hsub hy)
      have hmin_loc : IsLocalMin V x0 := by
        have hnhds : Set.Icc (0 : ℝ) 1 ∈ nhds x0 := Icc_mem_nhds h0x hx1
        exact Filter.eventually_of_mem hnhds (fun y hy => hx0_min hy)
      have hderiv0 : deriv V x0 = 0 := hmin_loc.deriv_eq_zero
      have hpivot : Filter.Tendsto (deriv V) (nhdsWithin x0 (Set.Ioi x0))
          (nhds 0) := by
        rw [← hderiv0]
        exact ((hd2 x0 hx0_in).continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      have hdneg := deriv_neg_right_of_deriv2_neg_of_pivot heta
        (fun y hy => hd2 y (hsub hy)) hd2neg hpivot
      have hicc_sub : Set.Icc x0 (x0 + eta / 2) ⊆ Set.Icc (0 : ℝ) 1 := by
        intro y hy
        have h1 : eta ≤ (1 - x0) / 2 := min_le_right _ _
        exact ⟨le_trans hx0_mem.1 hy.1, by linarith [hy.2]⟩
      have hanti_v : StrictAntiOn V (Set.Icc x0 (x0 + eta / 2)) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
          (hcont.mono hicc_sub)
        intro y hy
        rw [interior_Icc] at hy
        exact hdneg y ⟨hy.1, by linarith [hy.2]⟩
      have hlt' : V (x0 + eta / 2) < V x0 :=
        hanti_v (Set.left_mem_Icc.mpr (by linarith))
          (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
      have hge : V x0 ≤ V (x0 + eta / 2) :=
        hx0_min (hicc_sub (Set.right_mem_Icc.mpr (by linarith)))
      linarith
    · subst hx1
      set eta : ℝ := min (eps / 2) ((1 : ℝ) / 2) with heta_def
      have heta : 0 < eta := lt_min (by linarith) (by norm_num)
      have hsub : Set.Ioo (1 - eta) 1 ⊆ Set.Ioo (0 : ℝ) 1 := by
        intro y hy
        have h1 : eta ≤ (1 : ℝ) / 2 := min_le_right _ _
        exact ⟨by linarith [hy.1], hy.2⟩
      have hd2neg : ∀ y ∈ Set.Ioo (1 - eta) 1, deriv (deriv V) y < 0 := by
        intro y hy
        apply hneg_at y (hsub hy)
        apply hlt_near
        · rw [abs_sub_lt_iff]
          have h1 : eta ≤ eps / 2 := min_le_left _ _
          constructor <;> linarith [hy.1, hy.2, heps]
        · exact Set.Ioo_subset_Icc_self (hsub hy)
      have hdpos := deriv_pos_left_of_deriv2_neg_of_pivot heta
        (fun y hy => hd2 y (hsub hy)) hd2neg hNeu1
      have hicc_sub : Set.Icc (1 - eta / 2) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
        intro y hy
        have h1 : eta ≤ (1 : ℝ) / 2 := min_le_right _ _
        exact ⟨by linarith [hy.1], hy.2⟩
      have hmono_v : StrictMonoOn V (Set.Icc (1 - eta / 2) 1) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
          (hcont.mono hicc_sub)
        intro y hy
        rw [interior_Icc] at hy
        exact hdpos y ⟨by linarith [hy.1], hy.2⟩
      have hlt' : V (1 - eta / 2) < V 1 :=
        hmono_v (Set.left_mem_Icc.mpr (by linarith))
          (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
      have hge : V 1 ≤ V (1 - eta / 2) :=
        hx0_min (hicc_sub (Set.left_mem_Icc.mpr (by linarith)))
      linarith
  · have h0x' : x0 = 0 := h0x.symm
    subst h0x'
    set eta : ℝ := min (eps / 2) ((1 : ℝ) / 2) with heta_def
    have heta : 0 < eta := lt_min (by linarith) (by norm_num)
    have hsub : Set.Ioo (0 : ℝ) (0 + eta) ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro y hy
      have h1 : eta ≤ (1 : ℝ) / 2 := min_le_right _ _
      exact ⟨hy.1, by linarith [hy.2]⟩
    have hd2neg : ∀ y ∈ Set.Ioo (0 : ℝ) (0 + eta),
        deriv (deriv V) y < 0 := by
      intro y hy
      apply hneg_at y (hsub hy)
      apply hlt_near
      · rw [abs_sub_lt_iff]
        have h1 : eta ≤ eps / 2 := min_le_left _ _
        constructor <;> linarith [hy.1, hy.2, heps]
      · exact Set.Ioo_subset_Icc_self (hsub hy)
    have hdneg := deriv_neg_right_of_deriv2_neg_of_pivot heta
      (fun y hy => hd2 y (hsub hy)) hd2neg hNeu0
    have hicc_sub : Set.Icc (0 : ℝ) (0 + eta / 2) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro y hy
      have h1 : eta ≤ (1 : ℝ) / 2 := min_le_right _ _
      exact ⟨hy.1, by linarith [hy.2]⟩
    have hanti_v : StrictAntiOn V (Set.Icc (0 : ℝ) (0 + eta / 2)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
        (hcont.mono hicc_sub)
      intro y hy
      rw [interior_Icc] at hy
      exact hdneg y ⟨hy.1, by linarith [hy.2]⟩
    have hlt' : V (0 + eta / 2) < V 0 :=
      hanti_v (Set.left_mem_Icc.mpr (by linarith))
        (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
    have hge : V 0 ≤ V (0 + eta / 2) :=
      hx0_min (hicc_sub (Set.right_mem_Icc.mpr (by linarith)))
    linarith

private theorem lift_eq_interior (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

theorem intervalDomain_classical_v_lower_of_u_lower_at_time
    {p : CM2Params} {T t deltaU : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hdelta : 0 < deltaU)
    (hu : ∀ x : intervalDomainPoint, deltaU ≤ u t x) :
    ∀ x : intervalDomainPoint, p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have hclosed := hreg.2.2.2.2.1 t ht
  obtain ⟨_hu_closed, hv_closed⟩ := hclosed
  obtain ⟨hv_c2, _hv_deriv0, _hv_deriv1⟩ := hv_closed
  have hneu := hreg.2.2.2.1 t ht
  obtain ⟨_hneu_u, hneu_v⟩ := hneu
  obtain ⟨hNeu0, hNeu1⟩ := hneu_v
  have hv_cont : ContinuousOn (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) :=
    hv_c2.continuousOn
  have hd2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y := by
    intro y hy
    exact
      ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo
        (hv_c2.mono Set.Ioo_subset_Icc_self) hy).2).differentiableAt
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y
        = p.μ * intervalDomainLift (v t) y
          - p.ν * (intervalDomainLift (u t) y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomain.inside := hy
    have hpv := hsol.pde_v ht.1 ht.2 hxy
    rw [lift_eq_interior (v t) hy, lift_eq_interior (u t) hy]
    have hlap : intervalDomain.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        = deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hSrc : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      p.ν * deltaU ^ p.γ ≤ p.ν * (intervalDomainLift (u t) y) ^ p.γ := by
    intro y hy
    have hyu : deltaU ≤ intervalDomainLift (u t) y := by
      rw [lift_eq_interior (u t) hy]
      exact hu ⟨y, Set.Ioo_subset_Icc_self hy⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hdelta.le hyu p.hγ.le) p.hν.le
  have hlower := interval_elliptic_lower_bound_of_source_ge
    (V := intervalDomainLift (v t))
    (Src := fun y => p.ν * (intervalDomainLift (u t) y) ^ p.γ)
    (mu := p.μ) (c0 := p.ν * deltaU ^ p.γ)
    p.hμ hv_cont hd2 hPDE_v hSrc hNeu0 hNeu1
  intro x
  have hx := hlower x.1 x.2
  have hconst :
      (p.ν * deltaU ^ p.γ) / p.μ
        = p.ν / p.μ * deltaU ^ p.γ := by
    ring
  rw [hconst] at hx
  simpa [intervalDomainLift, x.2] using hx

theorem intervalDomain_eventually_v_lower_of_eventually_u_lower
    {p : CM2Params} {deltaU : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hdelta : 0 < deltaU)
    (hu : ∀ᶠ t in atTop, ∀ x : intervalDomainPoint, deltaU ≤ u t x) :
    ∀ᶠ t in atTop,
      ∀ x : intervalDomainPoint, p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
  filter_upwards [hu, eventually_gt_atTop (0 : ℝ)] with t hUt ht0
  have hclass : IsPaper2ClassicalSolution intervalDomain p (t + 1) u v :=
    hsol.1 (t + 1) (by linarith)
  have ht : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨ht0, by linarith⟩
  exact intervalDomain_classical_v_lower_of_u_lower_at_time
    hclass ht hdelta hUt

end

end ShenWork.Paper3
