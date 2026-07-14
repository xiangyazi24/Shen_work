import ShenWork.Paper3.IntervalDomainPersistenceGeneralMSupport
import ShenWork.Paper3.IntervalDomainPersistenceVCobounds

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

private theorem lift_eq_interior_M (f : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- The elliptic `v` equation is unchanged by the faithful `u^m` flux, so a
pointwise lower bound for `u` gives the same pointwise lower bound for `v`. -/
theorem intervalDomainM_classical_v_lower_of_u_lower_at_time
    {p : CM2Params} {T t deltaU : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hdelta : 0 < deltaU)
    (hu : ∀ x : intervalDomainPoint, deltaU ≤ u t x) :
    ∀ x : intervalDomainPoint, p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have hclosed := hreg.2.2.2.2.1 t ht
  obtain ⟨_, hv_closed⟩ := hclosed
  obtain ⟨hv_c2, _, _⟩ := hv_closed
  have hneu := hreg.2.2.2.1 t ht
  obtain ⟨_, hneu_v⟩ := hneu
  obtain ⟨hNeu0, hNeu1⟩ := hneu_v
  have hv_cont : ContinuousOn (intervalDomainLift (v t))
      (Set.Icc (0 : ℝ) 1) := hv_c2.continuousOn
  have hd2 : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y := by
    intro y hy
    exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo
      (hv_c2.mono Set.Ioo_subset_Icc_self) hy).2).differentiableAt
  have hPDE_v : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y =
        p.μ * intervalDomainLift (v t) y -
          p.ν * (intervalDomainLift (u t) y) ^ p.γ := by
    intro y hy
    have hxy : (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint)
        ∈ intervalDomainM.inside := hy
    have hpv := hsol.pde_v ht.1 ht.2 hxy
    rw [lift_eq_interior_M (v t) hy, lift_eq_interior_M (u t) hy]
    have hlap : intervalDomainM.laplacian (v t)
        (⟨y, Set.Ioo_subset_Icc_self hy⟩ : intervalDomainPoint) =
        deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hSrc : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      p.ν * deltaU ^ p.γ ≤ p.ν * (intervalDomainLift (u t) y) ^ p.γ := by
    intro y hy
    have hyu : deltaU ≤ intervalDomainLift (u t) y := by
      rw [lift_eq_interior_M (u t) hy]
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
  have hconst : (p.ν * deltaU ^ p.γ) / p.μ =
      p.ν / p.μ * deltaU ^ p.γ := by ring
  rw [hconst] at hx
  simpa [intervalDomainLift, x.2] using hx

theorem intervalDomainM_eventually_v_lower_of_eventually_u_lower
    {p : CM2Params} {deltaU : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hdelta : 0 < deltaU)
    (hu : ∀ᶠ t in atTop, ∀ x : intervalDomainPoint, deltaU ≤ u t x) :
    ∀ᶠ t in atTop,
      ∀ x : intervalDomainPoint, p.ν / p.μ * deltaU ^ p.γ ≤ v t x := by
  filter_upwards [hu, eventually_gt_atTop (0 : ℝ)] with t hUt ht0
  have hclass : IsPaper2ClassicalSolution intervalDomainM p (t + 1) u v :=
    hsol.1 (t + 1) (by linarith)
  exact intervalDomainM_classical_v_lower_of_u_lower_at_time hclass
    ⟨ht0, by linarith⟩ hdelta hUt

theorem intervalDomainM_infValue_v_isCoboundedUnder
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomainM.infValue (v t)) := by
  rcases hsol.bounded with ⟨M, hM⟩
  set M0 : ℝ := max M 0
  set B : ℝ := p.ν * M0 ^ p.γ
  have hceil : ∀ᶠ t in atTop, intervalDomainM.infValue (v t) ≤ B / p.μ := by
    filter_upwards [hM, eventually_ge_atTop (1 : ℝ)] with t hMt ht1
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hclass := hsol.classical.classical (T := t + 1) (by linarith)
    have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htpos, by linarith⟩
    obtain ⟨hOpen, _, _, hNeu, hClosed, _, _⟩ := hclass.regularity
    have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t))
        (Set.Ioo (0 : ℝ) 1) := (hOpen t htmem).2
    have hv_cont : ContinuousOn (intervalDomainLift (v t))
        (Set.Icc (0 : ℝ) 1) := (hClosed t htmem).2.1.continuousOn
    have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := (hNeu t htmem).2.1
    have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := (hNeu t htmem).2.2
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
      have hpv := ShenWork.Paper2.IsPaper2ClassicalSolution.pde_v
        (D := intervalDomainM) hclass htpos (by linarith : t < t + 1)
          (x := xy) hy
      have hlap : intervalDomainM.laplacian (v t) xy =
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
        exact (ShenWork.Paper2.IsPaper2ClassicalSolution.u_pos'
          (D := intervalDomainM) hclass htpos
            (by linarith : t < t + 1) (x := xy)).le
      have habsM : |intervalDomainLift (u t) y| ≤ M :=
        (intervalDomainM_abs_lift_le_supNorm hclass htmem
          (Set.Ioo_subset_Icc_self hy)).trans hMt
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
    let x0 : intervalDomain.Point := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    have hv0 : v t x0 ≤ B / p.μ := by
      have hv0_lift : intervalDomainLift (v t) 0 = v t x0 := by
        simp [intervalDomainLift, x0]
      simpa [hv0_lift] using hv_bound 0 ⟨le_rfl, zero_le_one⟩
    change sInf (Set.range (v t)) ≤ B / p.μ
    have hbdd : BddBelow (Set.range (v t)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨x, rfl⟩
      exact ShenWork.Paper2.IsPaper2ClassicalSolution.v_nonneg
        (D := intervalDomainM) hclass htpos
          (by linarith : t < t + 1) (x := x)
    exact (csInf_le hbdd ⟨x0, rfl⟩).trans hv0
  exact isCoboundedUnder_ge_of_eventually_le atTop hceil

theorem intervalDomainM_liminf_v_ge_of_strict_u_liminf_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {θ δ : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hδ : 0 < δ)
    (hu_bdd : IsBoundedUnder GE.ge atTop
      (fun t => intervalDomainM.infValue (u t)))
    (hv_cobdd : IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomainM.infValue (v t)))
    (hθ : θ ≤ liminfInfValue intervalDomainM u) (hδθ : δ < θ) :
    p.ν / p.μ * δ ^ p.γ ≤ liminfInfValue intervalDomainM v := by
  have hδ_liminf : δ < liminfInfValue intervalDomainM u :=
    lt_of_lt_of_le hδθ hθ
  have hu_inf : ∀ᶠ t in atTop, δ < intervalDomainM.infValue (u t) :=
    eventually_lt_of_lt_liminf hδ_liminf hu_bdd
  have hlowerM : EventuallyLowerBound intervalDomainM u δ :=
    ⟨hδ, hu_inf.mono (fun _ ht => le_of_lt ht)⟩
  have hlowerLegacy : EventuallyLowerBound intervalDomain u δ := by
    simpa [EventuallyLowerBound, intervalDomain, intervalDomainM] using hlowerM
  have hu_point : ∀ᶠ t in atTop,
      ∀ x : intervalDomain.Point, δ ≤ u t x :=
    intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound hlowerLegacy
  have hv_point : ∀ᶠ t in atTop,
      ∀ x : intervalDomain.Point, p.ν / p.μ * δ ^ p.γ ≤ v t x :=
    intervalDomainM_eventually_v_lower_of_eventually_u_lower hsol hδ hu_point
  have hVpos : 0 < p.ν / p.μ * δ ^ p.γ :=
    mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hδ _)
  have hvLowerLegacy : EventuallyLowerBound intervalDomain v
      (p.ν / p.μ * δ ^ p.γ) :=
    intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
      hVpos hv_point
  have hvLowerM : EventuallyLowerBound intervalDomainM v
      (p.ν / p.μ * δ ^ p.γ) := by
    simpa [EventuallyLowerBound, intervalDomain, intervalDomainM] using
      hvLowerLegacy
  exact liminf_ge_of_eventuallyLowerBound hv_cobdd hvLowerM

theorem intervalDomainM_liminf_v_ge_of_u_liminf_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {θ : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hθpos : 0 < θ)
    (hθ : θ ≤ liminfInfValue intervalDomainM u) :
    p.ν / p.μ * θ ^ p.γ ≤ liminfInfValue intervalDomainM v := by
  let φ : ℝ → ℝ := fun y => p.ν / p.μ * y ^ p.γ
  have hcont : ContinuousAt φ θ := by
    dsimp [φ]
    exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt hθpos))).const_mul _
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hnear_event : ∀ᶠ y in 𝓝 θ, |φ y - φ θ| < ε :=
    hcont.eventually (Metric.ball_mem_nhds (φ θ) hε)
  rw [Metric.eventually_nhds_iff] at hnear_event
  rcases hnear_event with ⟨η, hηpos, hη⟩
  set d : ℝ := min (θ / 2) (η / 2) with hd_def
  have hdpos : 0 < d := by simp [hd_def, hθpos, hηpos]
  set δ : ℝ := θ - d with hδ_def
  have hδpos : 0 < δ := by
    have hd_le : d ≤ θ / 2 := by simp [hd_def]
    linarith
  have hδθ : δ < θ := by simp [hδ_def, hdpos]
  have hdist : dist δ θ < η := by
    rw [Real.dist_eq]
    have hd_le : d ≤ η / 2 := by simp [hd_def]
    have habs : |δ - θ| = d := by
      rw [hδ_def]
      simp [abs_of_nonneg hdpos.le]
    rw [habs]
    linarith
  have hclose : |φ δ - φ θ| < ε := hη (y := δ) hdist
  have hstrict := intervalDomainM_liminf_v_ge_of_strict_u_liminf_lower
    (p := p) (u := u) (v := v) (θ := θ) (δ := δ)
    hsol hδpos (intervalDomainM_infValue_isBoundedUnder hsol)
      (intervalDomainM_infValue_v_isCoboundedUnder hsol) hθ hδθ
  have hφ_le : φ θ ≤ φ δ + ε := by
    have := (abs_lt.mp hclose).1
    linarith
  dsimp [φ] at hstrict hφ_le ⊢
  linarith

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_classical_v_lower_of_u_lower_at_time
#print axioms ShenWork.Paper3.intervalDomainM_eventually_v_lower_of_eventually_u_lower
#print axioms ShenWork.Paper3.intervalDomainM_infValue_v_isCoboundedUnder
#print axioms ShenWork.Paper3.intervalDomainM_liminf_v_ge_of_u_liminf_lower
