/-
  Phase C (MinPersistence): the Dini hypothesis from the min-point bound.

  Assembles `sliceMin_diff_le_slope` (per-step time-MVT) + `sliceMin_cluster_argmin`
  (sequential compactness) + the min-point estimate `−Kp·m ≤ ∂ₛF` at argmins
  into the right-lower-Dini hypothesis that `hamilton_lower_bound` consumes:

    ∀ x ∈ [a,b), ∀ r > Kp·m(x), ∃ᶠ z→x⁺, (z−x)⁻¹·(m x − m z) < r.

  Combined with `hamilton_lower_bound`, this yields the Grönwall lower bound
  `m(a)·e^{−Kp(t−a)} ≤ m(t)` — the Hamilton trick — completing the analytic
  core of `ClassicalMinPersistence` (modulo the min-point bound `hbound`,
  = `interior_min_point_of_solution` at interior argmins + the boundary
  assembly at endpoint argmins).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainSliceMinSlope
import ShenWork.Paper2.IntervalDomainClusterArgmin

open Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

set_option maxHeartbeats 1000000 in
/-- **The Dini hypothesis from the min-point bound.**  `m t := sInf (F t '' [0,1])`. -/
theorem sliceMin_dini_of_argmin_bound
    {F : ℝ → ℝ → ℝ} {a b Kp : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hslice_cont : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ContinuousOn (fun r => F r y) (Set.Icc a b))
    (hslice_diff : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s)
    (hm_cont : ContinuousOn (fun t => sInf (F t '' Set.Icc (0:ℝ) 1))
      (Set.Icc a b))
    (hdF_cont : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => F r y) s))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hbound : ∀ s ∈ Set.Icc a b, ∀ xs ∈ Set.Icc (0:ℝ) 1,
      F s xs = sInf (F s '' Set.Icc (0:ℝ) 1) →
      -Kp * sInf (F s '' Set.Icc (0:ℝ) 1) ≤ deriv (fun r => F r xs) s) :
    ∀ x ∈ Set.Ico a b, ∀ r : ℝ,
      Kp * sInf (F x '' Set.Icc (0:ℝ) 1) < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (sInf (F x '' Set.Icc (0:ℝ) 1)
          - sInf (F z '' Set.Icc (0:ℝ) 1)) < r := by
  intro x hx r hr
  set m : ℝ → ℝ := fun t => sInf (F t '' Set.Icc (0:ℝ) 1) with hm_def
  by_contra hcon
  rw [not_frequently] at hcon
  have hev : ∀ᶠ z in nhdsWithin x (Set.Ioi x), r ≤ (z - x)⁻¹ * (m x - m z) := by
    filter_upwards [hcon] with z hz using le_of_not_gt hz
  obtain ⟨c0, hc0_gt, hc0_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hxb : x < b := hx.2
  have hxa : a ≤ x := hx.1
  set c : ℝ := min c0 b with hc_def
  have hxc : x < c := lt_min hc0_gt hxb
  have hcb : c ≤ b := min_le_right c0 b
  have hcc0 : c ≤ c0 := min_le_left c0 b
  set zs : ℕ → ℝ := fun n => x + (c - x) / (n + 2) with hzs_def
  have hcx_pos : 0 < c - x := by linarith
  have hzs_gt : ∀ n, x < zs n := fun n => by
    simp only [hzs_def]; have : 0 < (c - x) / ((n:ℝ) + 2) := by positivity
    linarith
  have hzs_lt : ∀ n, zs n < c := fun n => by
    simp only [hzs_def]
    have hlt : (c - x) / ((n : ℝ) + 2) < c - x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hcx_pos, (by positivity : (0:ℝ) ≤ (n:ℝ))]
    linarith
  have hzs_memIcc : ∀ n, zs n ∈ Set.Icc a b := fun n =>
    ⟨le_trans hxa (hzs_gt n).le, le_trans (hzs_lt n).le hcb⟩
  have hzs_memIoo : ∀ n, zs n ∈ Set.Ioo x c0 := fun n =>
    ⟨hzs_gt n, lt_of_lt_of_le (hzs_lt n) hcc0⟩
  have hzs_lim : Tendsto zs atTop (nhds x) := by
    have h0 : Tendsto (fun n : ℕ => (c - x) / ((n:ℝ) + 2)) atTop (nhds 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hzs_def] using (tendsto_const_nhds.add h0)
  have hxIcc : x ∈ Set.Icc a b := ⟨hxa, hxb.le⟩
  -- Per-step: `∃ ξ_n, xz_n` argmin with `∂ₛF(ξ_n, xz_n) ≤ −r`.
  have hstep : ∀ n, ∃ ξ xz, ξ ∈ Set.Ioo x (zs n) ∧ xz ∈ Set.Icc (0:ℝ) 1 ∧
      F (zs n) xz = m (zs n) ∧ deriv (fun w => F w xz) ξ ≤ -r := by
    intro n
    obtain ⟨ξ, hξ_mem, xz, hxz_mem, hxz_argmin, hslope⟩ := sliceMin_diff_le_slope
      (hzs_memIcc n) hxIcc (hzs_gt n) hF
      (fun y hy => (hslice_cont y hy).mono (Set.Icc_subset_Icc hxa
        (le_trans (hzs_lt n).le hcb)))
      (fun y hy s hs => hslice_diff y hy s
        ⟨lt_of_le_of_lt hxa hs.1, lt_of_lt_of_le hs.2 (le_trans (hzs_lt n).le hcb)⟩)
    rw [show sInf (F x '' Set.Icc (0:ℝ) 1) = m x from rfl,
      show sInf (F (zs n) '' Set.Icc (0:ℝ) 1) = m (zs n) from rfl] at hslope
    refine ⟨ξ, xz, hξ_mem, hxz_mem, hxz_argmin, ?_⟩
    have hzx_pos : 0 < zs n - x := by linarith [hzs_gt n]
    have hr_le : r ≤ (zs n - x)⁻¹ * (m x - m (zs n)) := hc0_sub (hzs_memIoo n)
    have h2 : r * (zs n - x) ≤ m x - m (zs n) := by
      rw [inv_mul_eq_div, le_div_iff₀ hzx_pos] at hr_le
      exact hr_le
    have h3 : r * (zs n - x) ≤ (x - zs n) * deriv (fun w => F w xz) ξ :=
      le_trans h2 hslope
    have h3' : r * (zs n - x) ≤ -((zs n - x) * deriv (fun w => F w xz) ξ) := by
      have heq : (x - zs n) * deriv (fun w => F w xz) ξ
          = -((zs n - x) * deriv (fun w => F w xz) ξ) := by ring
      rw [← heq]; exact h3
    have h4 : (zs n - x) * deriv (fun w => F w xz) ξ ≤ (zs n - x) * (-r) := by
      have heq2 : (zs n - x) * (-r) = -(r * (zs n - x)) := by ring
      rw [heq2]; linarith [h3']
    exact le_of_mul_le_mul_left h4 hzx_pos
  choose ξs xzs hξ_mem hxz_mem hxz_argmin hkey using hstep
  -- Cluster point of argmins is an argmin of `F x`.
  obtain ⟨xstar, φ, hφ_mono, hxstar_mem, hFx_eq, hxz_lim⟩ :=
    sliceMin_cluster_argmin hxIcc hF hm_cont hzs_memIcc hzs_lim hxz_mem hxz_argmin
  -- `ξ_{φk} → x` by squeezing in `(x, z_{φk})`.
  have hξ_lim : Tendsto (fun k => ξs (φ k)) atTop (nhds x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (hzs_lim.comp hφ_mono.tendsto_atTop)
      (fun k => (hξ_mem (φ k)).1.le) (fun k => (hξ_mem (φ k)).2.le)
  -- Paired sequence `(ξ_{φk}, xz_{φk}) → (x, xstar)` in the slab.
  have hpair_lim : Tendsto (fun k => (ξs (φ k), xzs (φ k))) atTop
      (nhds (x, xstar)) := hξ_lim.prodMk_nhds hxz_lim
  have hpair_mem : ∀ k, (ξs (φ k), xzs (φ k))
      ∈ Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1 := fun k =>
    ⟨⟨le_trans hxa (hξ_mem (φ k)).1.le,
        le_trans (hξ_mem (φ k)).2.le (le_trans (hzs_lt (φ k)).le hcb)⟩,
      hxz_mem (φ k)⟩
  -- `∂ₛF(ξ_{φk}, xz_{φk}) → ∂ₛF(x, xstar)` (joint continuity).
  have hdF_lim : Tendsto (fun k => deriv (fun w => F w (xzs (φ k))) (ξs (φ k)))
      atTop (nhds (deriv (fun w => F w xstar) x)) := by
    have hcwa : ContinuousWithinAt
        (Function.uncurry (fun s y => deriv (fun w => F w y) s))
        (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) (x, xstar) :=
      hdF_cont (x, xstar) ⟨hxIcc, hxstar_mem⟩
    exact hcwa.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpair_lim, Filter.Eventually.of_forall hpair_mem⟩)
  -- The limit is `≤ −r`.
  have hle : deriv (fun w => F w xstar) x ≤ -r :=
    le_of_tendsto hdF_lim (Filter.Eventually.of_forall (fun k => hkey (φ k)))
  -- But the min-point bound gives `−Kp·m x ≤ ∂ₛF(x, xstar)`.
  have hge : -Kp * m x ≤ deriv (fun w => F w xstar) x := by
    have := hbound x hxIcc xstar hxstar_mem hFx_eq
    rwa [show sInf (F x '' Set.Icc (0:ℝ) 1) = m x from rfl] at this
  -- Contradiction with `Kp·m x < r`.
  have hcontra : r ≤ Kp * m x := by nlinarith [hle, hge]
  exact absurd hr (not_lt.mpr hcontra)

end ShenWork.MinPersistenceAtoms
