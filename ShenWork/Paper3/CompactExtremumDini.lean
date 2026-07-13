import ShenWork.Paper2.IntervalDomainSliceMinDini

/-!
# Compact-extremum Dini bounds with nonlinear scalar right-hand sides

The older interval Danskin lemmas specialize the extremum slope to `K * M`.
The rectangle argument needs the same compactness theorem with an arbitrary
time-dependent scalar bound.  This file keeps the analytic core generic.
-/

open Set Filter Topology

namespace ShenWork.Paper3

noncomputable section

open ShenWork.MinPersistenceAtoms

set_option maxHeartbeats 1000000 in
/-- A lower bound `g(s)` for every exact argmin time slope gives the
right-lower Dini inequality for the spatial minimum. -/
theorem sliceMin_dini_of_argmin_lowerBound
    {F : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hslice_cont : ∀ y ∈ Icc (0 : ℝ) 1,
      ContinuousOn (fun r => F r y) (Icc a b))
    (hslice_diff : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s)
    (hm_cont : ContinuousOn (fun t => sInf (F t '' Icc (0 : ℝ) 1))
      (Icc a b))
    (hdF_cont : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => F r y) s))
      (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hbound : ∀ s ∈ Icc a b, ∀ xs ∈ Icc (0 : ℝ) 1,
      F s xs = sInf (F s '' Icc (0 : ℝ) 1) →
      g s ≤ deriv (fun r => F r xs) s) :
    ∀ x ∈ Ico a b, ∀ r : ℝ, -g x < r →
      ∃ᶠ z in nhdsWithin x (Ioi x),
        (z - x)⁻¹ *
          (sInf (F x '' Icc (0 : ℝ) 1) -
            sInf (F z '' Icc (0 : ℝ) 1)) < r := by
  intro x hx r hr
  set m : ℝ → ℝ := fun t => sInf (F t '' Icc (0 : ℝ) 1) with hm_def
  by_contra hcon
  rw [not_frequently] at hcon
  have hev : ∀ᶠ z in nhdsWithin x (Ioi x),
      r ≤ (z - x)⁻¹ * (m x - m z) := by
    filter_upwards [hcon] with z hz using le_of_not_gt hz
  obtain ⟨c0, hc0_gt, hc0_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set c : ℝ := min c0 b with hc_def
  have hxc : x < c := lt_min hc0_gt hx.2
  have hcb : c ≤ b := min_le_right c0 b
  have hcc0 : c ≤ c0 := min_le_left c0 b
  set zs : ℕ → ℝ := fun n => x + (c - x) / (n + 2) with hzs_def
  have hcx : 0 < c - x := by linarith
  have hzs_gt : ∀ n, x < zs n := fun n => by
    simp only [hzs_def]
    have : 0 < (c - x) / ((n : ℝ) + 2) := by positivity
    linarith
  have hzs_lt : ∀ n, zs n < c := fun n => by
    simp only [hzs_def]
    have hlt : (c - x) / ((n : ℝ) + 2) < c - x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hcx, (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    linarith
  have hzs_mem : ∀ n, zs n ∈ Icc a b := fun n =>
    ⟨le_trans hx.1 (hzs_gt n).le, le_trans (hzs_lt n).le hcb⟩
  have hzs_mem0 : ∀ n, zs n ∈ Ioo x c0 := fun n =>
    ⟨hzs_gt n, lt_of_lt_of_le (hzs_lt n) hcc0⟩
  have hzs_lim : Tendsto zs atTop (nhds x) := by
    have h0 : Tendsto (fun n : ℕ => (c - x) / ((n : ℝ) + 2))
        atTop (nhds 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hzs_def] using tendsto_const_nhds.add h0
  have hxIcc : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
  have hstep : ∀ n, ∃ ξ xs,
      ξ ∈ Ioo x (zs n) ∧ xs ∈ Icc (0 : ℝ) 1 ∧
        F (zs n) xs = m (zs n) ∧
        deriv (fun w => F w xs) ξ ≤ -r := by
    intro n
    obtain ⟨ξ, hξ, xs, hxs, harg, hslope⟩ := sliceMin_diff_le_slope
      (hzs_mem n) hxIcc (hzs_gt n) hF
      (fun y hy => (hslice_cont y hy).mono
        (Icc_subset_Icc hx.1
          (le_trans (hzs_lt n).le hcb)))
      (fun y hy s hs => hslice_diff y hy s
        ⟨lt_of_le_of_lt hx.1 hs.1,
          lt_of_lt_of_le hs.2 (le_trans (hzs_lt n).le hcb)⟩)
    rw [show sInf (F x '' Icc (0 : ℝ) 1) = m x from rfl,
      show sInf (F (zs n) '' Icc (0 : ℝ) 1) = m (zs n) from rfl] at hslope
    refine ⟨ξ, xs, hξ, hxs, harg, ?_⟩
    have hzx : 0 < zs n - x := by linarith [hzs_gt n]
    have hrle : r ≤ (zs n - x)⁻¹ * (m x - m (zs n)) :=
      hc0_sub (hzs_mem0 n)
    have h2 : r * (zs n - x) ≤ m x - m (zs n) := by
      rw [inv_mul_eq_div, le_div_iff₀ hzx] at hrle
      exact hrle
    have h3 : r * (zs n - x) ≤
        (x - zs n) * deriv (fun w => F w xs) ξ := h2.trans hslope
    have h4 : (zs n - x) * deriv (fun w => F w xs) ξ ≤
        (zs n - x) * (-r) := by
      nlinarith
    exact le_of_mul_le_mul_left h4 hzx
  choose ξs xss hξ hxs harg hkey using hstep
  obtain ⟨xstar, φ, hφ, hxstar, hFx, hxs_lim⟩ :=
    sliceMin_cluster_argmin hxIcc hF hm_cont hzs_mem hzs_lim hxs harg
  have hξ_lim : Tendsto (fun k => ξs (φ k)) atTop (nhds x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (hzs_lim.comp hφ.tendsto_atTop)
      (fun k => (hξ (φ k)).1.le) (fun k => (hξ (φ k)).2.le)
  have hpair_lim : Tendsto (fun k => (ξs (φ k), xss (φ k))) atTop
      (nhds (x, xstar)) := hξ_lim.prodMk_nhds hxs_lim
  have hpair_mem : ∀ k, (ξs (φ k), xss (φ k)) ∈
      Icc a b ×ˢ Icc (0 : ℝ) 1 := fun k =>
    ⟨⟨le_trans hx.1 (hξ (φ k)).1.le,
        le_trans (hξ (φ k)).2.le
          (le_trans (hzs_lt (φ k)).le hcb)⟩, hxs (φ k)⟩
  have hdF_lim : Tendsto
      (fun k => deriv (fun w => F w (xss (φ k))) (ξs (φ k))) atTop
      (nhds (deriv (fun w => F w xstar) x)) := by
    have hc := hdF_cont (x, xstar) ⟨hxIcc, hxstar⟩
    exact hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpair_lim, Eventually.of_forall hpair_mem⟩)
  have hle : deriv (fun w => F w xstar) x ≤ -r :=
    le_of_tendsto hdF_lim (Eventually.of_forall fun k => hkey (φ k))
  have hge : g x ≤ deriv (fun w => F w xstar) x :=
    hbound x hxIcc xstar hxstar hFx
  have : r ≤ -g x := by linarith
  exact (not_lt_of_ge this) hr

private theorem sInf_neg_image {S : Set ℝ}
    (hne : S.Nonempty) (hbdd : BddAbove S) :
    sInf ((fun x => -x) '' S) = -sSup S := by
  have hb : BddBelow ((fun x => -x) '' S) := by
    obtain ⟨B, hB⟩ := hbdd
    exact ⟨-B, by rintro y ⟨z, hz, rfl⟩; linarith [hB hz]⟩
  have hne' := hne.image (fun x => -x)
  apply le_antisymm
  · have hub : ∀ z ∈ S, z ≤ -sInf ((fun x => -x) '' S) := by
      intro z hz
      have h := csInf_le hb ⟨z, hz, rfl⟩
      linarith
    have h := csSup_le hne hub
    linarith
  · apply le_csInf hne'
    rintro _ ⟨z, hz, rfl⟩
    have h := le_csSup hbdd hz
    linarith

private theorem sInf_neg_slice
    {F : ℝ → ℝ → ℝ} {a b t : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Icc a b ×ˢ Icc (0 : ℝ) 1)) (ht : t ∈ Icc a b) :
    sInf ((fun y => -F t y) '' Icc (0 : ℝ) 1) =
      -sSup (F t '' Icc (0 : ℝ) 1) := by
  have hmap : ContinuousOn (fun y => (t, y)) (Icc (0 : ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcont : ContinuousOn (F t) (Icc (0 : ℝ) 1) :=
    hF.comp hmap (fun y hy => ⟨ht, hy⟩)
  have hcompact := isCompact_Icc.image_of_continuousOn hcont
  have himage : (fun y => -F t y) '' Icc (0 : ℝ) 1 =
      (fun z : ℝ => -z) '' (F t '' Icc (0 : ℝ) 1) := by
    rw [Set.image_image]
  rw [himage]
  exact sInf_neg_image ((nonempty_Icc.mpr zero_le_one).image _) hcompact.bddAbove

/-- An upper bound `g(s)` for every exact argmax time slope gives the
right-upper Dini inequality for the spatial maximum. -/
theorem sliceMax_dini_of_argmax_upperBound
    {F : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hslice_cont : ∀ y ∈ Icc (0 : ℝ) 1,
      ContinuousOn (fun r => F r y) (Icc a b))
    (hslice_diff : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s)
    (hM_cont : ContinuousOn (fun t => sSup (F t '' Icc (0 : ℝ) 1))
      (Icc a b))
    (hdF_cont : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => F r y) s))
      (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hbound : ∀ s ∈ Icc a b, ∀ xs ∈ Icc (0 : ℝ) 1,
      F s xs = sSup (F s '' Icc (0 : ℝ) 1) →
      deriv (fun r => F r xs) s ≤ g s) :
    ∀ x ∈ Ico a b, ∀ r : ℝ, g x < r →
      ∃ᶠ z in nhdsWithin x (Ioi x),
        (z - x)⁻¹ *
          (sSup (F z '' Icc (0 : ℝ) 1) -
            sSup (F x '' Icc (0 : ℝ) 1)) < r := by
  set G : ℝ → ℝ → ℝ := fun s y => -F s y with hG_def
  have hGder : ∀ y s,
      deriv (fun r => G r y) s = -deriv (fun r => F r y) s := by
    intro y s
    exact deriv.neg
  have hGsInf : ∀ {s}, s ∈ Icc a b →
      sInf (G s '' Icc (0 : ℝ) 1) =
        -sSup (F s '' Icc (0 : ℝ) 1) := by
    intro s hs
    exact sInf_neg_slice hF hs
  have hGF : ContinuousOn (Function.uncurry G)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    have heq : Function.uncurry G = fun q => -(Function.uncurry F) q := by
      funext q
      simp [G, Function.uncurry]
    rw [heq]
    exact hF.neg
  have hGslice : ∀ y ∈ Icc (0 : ℝ) 1,
      ContinuousOn (fun r => G r y) (Icc a b) := by
    intro y hy
    exact (hslice_cont y hy).neg
  have hGdiff : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => G r y) (deriv (fun r => G r y) s) s := by
    intro y hy s hs
    have h := (hslice_diff y hy s hs).neg
    rw [hGder y s]
    exact h
  have hGmin : ContinuousOn (fun s => sInf (G s '' Icc (0 : ℝ) 1))
      (Icc a b) := by
    exact hM_cont.neg.congr (fun s hs => hGsInf hs)
  have hGd : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => G r y) s))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    have heq : EqOn
        (Function.uncurry (fun s y => deriv (fun r => G r y) s))
        (fun q => -(Function.uncurry
          (fun s y => deriv (fun r => F r y) s)) q)
        (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
      rintro ⟨s, y⟩ _
      simp only [Function.uncurry, hGder]
    exact hdF_cont.neg.congr heq
  have hGbnd : ∀ s ∈ Icc a b, ∀ xs ∈ Icc (0 : ℝ) 1,
      G s xs = sInf (G s '' Icc (0 : ℝ) 1) →
      -g s ≤ deriv (fun r => G r xs) s := by
    intro s hs xs hxs harg
    rw [hGsInf hs] at harg
    have hargF : F s xs = sSup (F s '' Icc (0 : ℝ) 1) := by
      simp only [G] at harg
      linarith
    have hb := hbound s hs xs hxs hargF
    rw [hGder]
    linarith
  have hmin := sliceMin_dini_of_argmin_lowerBound
    hGF hGslice hGdiff hGmin hGd hGbnd
  intro x hx r hr
  have hfreq := hmin x hx r (by simpa using hr)
  have hxIcc : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
  have hev : ∀ᶠ z in nhdsWithin x (Ioi x), z ∈ Icc a b := by
    have hmem : Ioo x b ∈ nhdsWithin x (Ioi x) := by
      rw [← Ioi_inter_Iio]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.2)
    filter_upwards [hmem] with z hz
    exact ⟨le_trans hx.1 hz.1.le, hz.2.le⟩
  refine (hfreq.and_eventually hev).mono ?_
  rintro z ⟨hz, hzmem⟩
  rw [hGsInf hxIcc, hGsInf hzmem] at hz
  convert hz using 1 <;> ring

set_option maxHeartbeats 1000000 in
/-- Compact-type form of the nonlinear argmax Dini theorem.  This supports
finite sums and products of compact spatial choice types, as needed for a
clamped max/min log-gap in the rectangle argument. -/
theorem compactMax_dini_of_argmax_upperBound
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K] [Nonempty K]
    {F : ℝ → K → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ (Set.univ : Set K)))
    (hslice_cont : ∀ q : K, ContinuousOn (fun r => F r q) (Icc a b))
    (hslice_diff : ∀ q : K, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => F r q) (deriv (fun r => F r q) s) s)
    (hM_cont : ContinuousOn
      (fun t => sSup (F t '' (Set.univ : Set K))) (Icc a b))
    (hdF_cont : ContinuousOn
      (Function.uncurry (fun s q => deriv (fun r => F r q) s))
      (Icc a b ×ˢ (Set.univ : Set K)))
    (hbound : ∀ s ∈ Icc a b, ∀ q : K,
      F s q = sSup (F s '' (Set.univ : Set K)) →
      deriv (fun r => F r q) s ≤ g s) :
    ∀ x ∈ Ico a b, ∀ r : ℝ, g x < r →
      ∃ᶠ z in nhdsWithin x (Ioi x),
        (z - x)⁻¹ *
          (sSup (F z '' (Set.univ : Set K)) -
            sSup (F x '' (Set.univ : Set K))) < r := by
  intro x hx r hr
  set M : ℝ → ℝ := fun t => sSup (F t '' (Set.univ : Set K)) with hM_def
  by_contra hcon
  rw [not_frequently] at hcon
  have hev : ∀ᶠ z in nhdsWithin x (Ioi x),
      r ≤ (z - x)⁻¹ * (M z - M x) := by
    filter_upwards [hcon] with z hz using le_of_not_gt hz
  obtain ⟨c0, hc0_gt, hc0_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set c : ℝ := min c0 b with hc_def
  have hxc : x < c := lt_min hc0_gt hx.2
  have hcb : c ≤ b := min_le_right c0 b
  have hcc0 : c ≤ c0 := min_le_left c0 b
  set zs : ℕ → ℝ := fun n => x + (c - x) / (n + 2) with hzs_def
  have hcx : 0 < c - x := by linarith
  have hzs_gt : ∀ n, x < zs n := fun n => by
    simp only [hzs_def]
    have : 0 < (c - x) / ((n : ℝ) + 2) := by positivity
    linarith
  have hzs_lt : ∀ n, zs n < c := fun n => by
    simp only [hzs_def]
    have hlt : (c - x) / ((n : ℝ) + 2) < c - x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hcx, (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    linarith
  have hzs_mem : ∀ n, zs n ∈ Icc a b := fun n =>
    ⟨le_trans hx.1 (hzs_gt n).le, le_trans (hzs_lt n).le hcb⟩
  have hzs_mem0 : ∀ n, zs n ∈ Ioo x c0 := fun n =>
    ⟨hzs_gt n, lt_of_lt_of_le (hzs_lt n) hcc0⟩
  have hzs_lim : Tendsto zs atTop (nhds x) := by
    have h0 : Tendsto (fun n : ℕ => (c - x) / ((n : ℝ) + 2))
        atTop (nhds 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hzs_def] using tendsto_const_nhds.add h0
  have hxIcc : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
  have hstep : ∀ n, ∃ ξ q,
      ξ ∈ Ioo x (zs n) ∧
        F (zs n) q = M (zs n) ∧
        r ≤ deriv (fun w => F w q) ξ := by
    intro n
    have hslice : ContinuousOn (F (zs n)) (Set.univ : Set K) := by
      have hmap : ContinuousOn (fun q : K => (zs n, q)) Set.univ :=
        (continuous_const.prodMk continuous_id).continuousOn
      exact hF.comp hmap (fun q _ => ⟨hzs_mem n, Set.mem_univ q⟩)
    obtain ⟨q, _, hMq, hqmax⟩ :=
      isCompact_univ.exists_sSup_image_eq_and_ge Set.univ_nonempty hslice
    have hcontxz : ContinuousOn (fun w => F w q) (Icc x (zs n)) :=
      (hslice_cont q).mono
        (Icc_subset_Icc hx.1 (le_trans (hzs_lt n).le hcb))
    have hdiffxz : ∀ w ∈ Ioo x (zs n),
        HasDerivAt (fun s => F s q) (deriv (fun s => F s q) w) w := by
      intro w hw
      exact hslice_diff q w
        ⟨lt_of_le_of_lt hx.1 hw.1,
          lt_of_lt_of_le hw.2 (le_trans (hzs_lt n).le hcb)⟩
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope
      (fun w => F w q) (deriv (fun w => F w q)) (hzs_gt n)
      hcontxz hdiffxz
    refine ⟨ξ, q, hξ, hMq.symm, ?_⟩
    have hFx_le : F x q ≤ M x := by
      have hxSlice : ContinuousOn (F x) (Set.univ : Set K) := by
        have hmap : ContinuousOn (fun z : K => (x, z)) Set.univ :=
          (continuous_const.prodMk continuous_id).continuousOn
        exact hF.comp hmap (fun z _ => ⟨hxIcc, Set.mem_univ z⟩)
      have hbdd := (isCompact_univ.image_of_continuousOn hxSlice).bddAbove
      exact le_csSup hbdd (Set.mem_image_of_mem _ (Set.mem_univ q))
    have hnum : M (zs n) - M x ≤ F (zs n) q - F x q := by
      rw [← hMq]
      linarith [hFx_le]
    have hzx : 0 < zs n - x := by linarith [hzs_gt n]
    have hrle : r ≤ (zs n - x)⁻¹ * (M (zs n) - M x) :=
      hc0_sub (hzs_mem0 n)
    have hquot : r ≤ (F (zs n) q - F x q) / (zs n - x) := by
      rw [inv_mul_eq_div] at hrle
      exact hrle.trans (div_le_div_of_nonneg_right hnum hzx.le)
    rw [hξeq]
    exact hquot
  choose ξs qs hξ harg hkey using hstep
  obtain ⟨qstar, _, φ, hφ, hq_lim⟩ :=
    isCompact_univ.tendsto_subseq (x := qs) (fun _ => Set.mem_univ _)
  have hξ_lim : Tendsto (fun k => ξs (φ k)) atTop (nhds x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (hzs_lim.comp hφ.tendsto_atTop)
      (fun k => (hξ (φ k)).1.le) (fun k => (hξ (φ k)).2.le)
  have hzsφ_lim : Tendsto (fun k => zs (φ k)) atTop (nhds x) :=
    hzs_lim.comp hφ.tendsto_atTop
  have hpair_arg_lim : Tendsto (fun k => (zs (φ k), qs (φ k))) atTop
      (nhds (x, qstar)) := hzsφ_lim.prodMk_nhds hq_lim
  have hFarg_lim : Tendsto (fun k => F (zs (φ k)) (qs (φ k))) atTop
      (nhds (F x qstar)) := by
    have hc := hF (x, qstar) ⟨hxIcc, Set.mem_univ qstar⟩
    exact hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpair_arg_lim, Eventually.of_forall fun k =>
        ⟨hzs_mem (φ k), Set.mem_univ _⟩⟩)
  have hM_lim : Tendsto (fun k => M (zs (φ k))) atTop (nhds (M x)) := by
    have hc := hM_cont x hxIcc
    exact hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hzsφ_lim, Eventually.of_forall fun k => hzs_mem (φ k)⟩)
  have hqstar : F x qstar = M x := by
    have heq : (fun k => F (zs (φ k)) (qs (φ k))) =
        fun k => M (zs (φ k)) := funext fun k => harg (φ k)
    rw [heq] at hFarg_lim
    exact tendsto_nhds_unique hFarg_lim hM_lim
  have hpair_der_lim : Tendsto (fun k => (ξs (φ k), qs (φ k))) atTop
      (nhds (x, qstar)) := hξ_lim.prodMk_nhds hq_lim
  have hd_lim : Tendsto
      (fun k => deriv (fun w => F w (qs (φ k))) (ξs (φ k))) atTop
      (nhds (deriv (fun w => F w qstar) x)) := by
    have hc := hdF_cont (x, qstar) ⟨hxIcc, Set.mem_univ qstar⟩
    exact hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpair_der_lim, Eventually.of_forall fun k =>
        ⟨⟨le_trans hx.1 (hξ (φ k)).1.le,
          le_trans (hξ (φ k)).2.le
            (le_trans (hzs_lt (φ k)).le hcb)⟩, Set.mem_univ _⟩⟩)
  have hrle : r ≤ deriv (fun w => F w qstar) x :=
    ge_of_tendsto hd_lim (Eventually.of_forall fun k => hkey (φ k))
  have hgle := hbound x hxIcc qstar hqstar
  exact (not_lt_of_ge (hrle.trans hgle)) hr

#print axioms sliceMin_dini_of_argmin_lowerBound
#print axioms sliceMax_dini_of_argmax_upperBound
#print axioms compactMax_dini_of_argmax_upperBound

end

end ShenWork.Paper3
