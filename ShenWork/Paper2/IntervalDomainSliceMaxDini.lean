/-
  Lemma 3.1 (MAX side): the right-upper Dini hypothesis for the spatial-MAXIMUM
  trajectory, obtained for free from the proven min-side machinery via the
  reflection `G := −F` (argmin of `−F` = argmax of `F`, `sInf(−F) = −sSup F`).

  `sliceMax_dini_of_argmax_bound` is the exact dual of
  `MinPersistenceAtoms.sliceMin_dini_of_argmin_bound`: from the max-point slope
  bound `∂ₛF(argmax) ≤ Kp·M` it produces the forward difference-quotient bound
    `∀ x, ∀ r > Kp·M(x), ∃ᶠ z→x⁺, (z−x)⁻¹·(M z − M x) < r`,   `M t := sSup (F t '' [0,1])`,
  which (with `Kp = 0`) is exactly the Dini input of
  `Paper2.Lemma31Heat.supNorm_nonincreasing_of_dini`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainSliceMinDini

open Set Filter Topology

noncomputable section

namespace ShenWork.MaxPrincipleAtoms

/-- `sInf` of the negated set is `−sSup` (conditionally-complete real lattice). -/
private theorem sInf_neg_image {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) :
    sInf ((fun x => -x) '' S) = -sSup S := by
  have hbddb : BddBelow ((fun x => -x) '' S) := by
    obtain ⟨B, hB⟩ := hbdd
    exact ⟨-B, by rintro y ⟨z, hz, rfl⟩; linarith [hB hz]⟩
  have hne' : ((fun x => -x) '' S).Nonempty := hne.image _
  apply le_antisymm
  · have hub : ∀ z ∈ S, z ≤ -sInf ((fun x => -x) '' S) := by
      intro z hz
      have : sInf ((fun x => -x) '' S) ≤ -z := csInf_le hbddb ⟨z, hz, rfl⟩
      linarith
    have : sSup S ≤ -sInf ((fun x => -x) '' S) := csSup_le hne hub
    linarith
  · apply le_csInf hne'
    rintro t ⟨z, hz, rfl⟩
    have : z ≤ sSup S := le_csSup hbdd hz
    linarith

/-- The spatial slice `F t '' [0,1]` is nonempty and bounded above (continuous
image of the compact `[0,1]`), so its `sSup`/the negated `sInf` are well-behaved. -/
private theorem slice_ne_bdd {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    (F t '' Set.Icc (0:ℝ) 1).Nonempty ∧ BddAbove (F t '' Set.Icc (0:ℝ) 1) := by
  have hmap : ContinuousOn (fun y => (t, y)) (Set.Icc (0:ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcont : ContinuousOn (fun y => F t y) (Set.Icc (0:ℝ) 1) :=
    hF.comp hmap (fun y hy => ⟨ht, hy⟩)
  have hcompact := isCompact_Icc.image_of_continuousOn hcont
  exact ⟨(Set.nonempty_Icc.mpr zero_le_one).image _, hcompact.bddAbove⟩

/-- The negated spatial slice image rewrites as a negation of the image. -/
private theorem neg_slice_image (F : ℝ → ℝ → ℝ) (t : ℝ) :
    (fun y => -F t y) '' Set.Icc (0:ℝ) 1
      = (fun x => -x) '' (F t '' Set.Icc (0:ℝ) 1) := by
  rw [Set.image_image]

/-- Bridge: `sInf((−F) t '' [0,1]) = −sSup(F t '' [0,1])`. -/
private theorem sInf_neg_slice {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    sInf ((fun y => -F t y) '' Set.Icc (0:ℝ) 1)
      = -sSup (F t '' Set.Icc (0:ℝ) 1) := by
  obtain ⟨hne, hbdd⟩ := slice_ne_bdd hF ht
  rw [neg_slice_image, sInf_neg_image hne hbdd]

/-- **Right-upper Dini hypothesis for the spatial maximum.**  Dual of
`MinPersistenceAtoms.sliceMin_dini_of_argmin_bound` via `G := −F`. -/
theorem sliceMax_dini_of_argmax_bound
    {F : ℝ → ℝ → ℝ} {a b Kp : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hslice_cont : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ContinuousOn (fun r => F r y) (Set.Icc a b))
    (hslice_diff : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s)
    (hM_cont : ContinuousOn (fun t => sSup (F t '' Set.Icc (0:ℝ) 1))
      (Set.Icc a b))
    (hdF_cont : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => F r y) s))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
    (hbound : ∀ s ∈ Set.Icc a b, ∀ xs ∈ Set.Icc (0:ℝ) 1,
      F s xs = sSup (F s '' Set.Icc (0:ℝ) 1) →
      deriv (fun r => F r xs) s ≤ Kp * sSup (F s '' Set.Icc (0:ℝ) 1)) :
    ∀ x ∈ Set.Ico a b, ∀ r : ℝ,
      Kp * sSup (F x '' Set.Icc (0:ℝ) 1) < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (sSup (F z '' Set.Icc (0:ℝ) 1)
          - sSup (F x '' Set.Icc (0:ℝ) 1)) < r := by
  -- Reflect: `G r y := -F r y`.  `sInf (G t '' [0,1]) = -sSup (F t '' [0,1])`.
  set G : ℝ → ℝ → ℝ := fun r y => -F r y with hG_def
  have hGder : ∀ y s, deriv (fun r => G r y) s = -deriv (fun r => F r y) s := by
    intro y s
    show deriv (fun r => -F r y) s = -deriv (fun r => F r y) s
    exact deriv.neg
  have hGsInf : ∀ {t}, t ∈ Set.Icc a b →
      sInf (G t '' Set.Icc (0:ℝ) 1) = -sSup (F t '' Set.Icc (0:ℝ) 1) := by
    intro t ht; exact sInf_neg_slice hF ht
  -- Hypotheses for the min lemma on `G`.
  have hF' : ContinuousOn (Function.uncurry G)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := by
    have : Function.uncurry G = fun p => -(Function.uncurry F) p := by
      funext p; simp [hG_def, Function.uncurry]
    rw [this]; exact hF.neg
  have hslice_cont' : ∀ y ∈ Set.Icc (0:ℝ) 1,
      ContinuousOn (fun r => G r y) (Set.Icc a b) := by
    intro y hy; simp only [hG_def]; exact (hslice_cont y hy).neg
  have hslice_diff' : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => G r y) (deriv (fun r => G r y) s) s := by
    intro y hy s hs
    have h := (hslice_diff y hy s hs).neg
    rw [hGder y s]; exact h
  have hm_cont' : ContinuousOn (fun t => sInf (G t '' Set.Icc (0:ℝ) 1))
      (Set.Icc a b) := by
    have heq : Set.EqOn (fun t => sInf (G t '' Set.Icc (0:ℝ) 1))
        (fun t => -sSup (F t '' Set.Icc (0:ℝ) 1)) (Set.Icc a b) :=
      fun t ht => hGsInf ht
    exact (hM_cont.neg).congr heq
  have hdF_cont' : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => G r y) s))
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := by
    have heq : Set.EqOn
        (Function.uncurry (fun s y => deriv (fun r => G r y) s))
        (fun p => -(Function.uncurry (fun s y => deriv (fun r => F r y) s)) p)
        (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := by
      rintro ⟨s, y⟩ _; simp only [Function.uncurry, hGder]
    exact (hdF_cont.neg).congr heq
  have hbound' : ∀ s ∈ Set.Icc a b, ∀ xs ∈ Set.Icc (0:ℝ) 1,
      G s xs = sInf (G s '' Set.Icc (0:ℝ) 1) →
      -(-Kp) * sInf (G s '' Set.Icc (0:ℝ) 1) ≤ deriv (fun r => G r xs) s := by
    intro s hs xs hxs hargmin
    -- `G s xs = sInf (G s) = -sSup (F s)` ⟹ `F s xs = sSup (F s)`.
    rw [hGsInf hs] at hargmin
    have hFarg : F s xs = sSup (F s '' Set.Icc (0:ℝ) 1) := by
      simp only [hG_def] at hargmin; linarith
    have hb := hbound s hs xs hxs hFarg
    rw [hGder xs s, hGsInf hs]
    -- goal: -(-Kp) * (-sSup F) ≤ -deriv F ; i.e. -Kp*sSup F ≤ -deriv F
    have : deriv (fun r => F r xs) s ≤ Kp * sSup (F s '' Set.Icc (0:ℝ) 1) := hb
    nlinarith [this]
  -- Apply the min-side Dini lemma to `G` with rate `-Kp`.
  have hmin := MinPersistenceAtoms.sliceMin_dini_of_argmin_bound
    (Kp := -Kp) hF' hslice_cont' hslice_diff' hm_cont' hdF_cont' hbound'
  intro x hx r hr
  have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le⟩
  have hrG : -Kp * sInf (G x '' Set.Icc (0:ℝ) 1) < r := by
    rw [hGsInf hxIcc, neg_mul_neg]; exact hr
  have hfreq := hmin x hx r hrG
  -- `z` near `x⁺` eventually lies in `Icc a b` (since `a ≤ x < b`).
  have hev : ∀ᶠ z in nhdsWithin x (Set.Ioi x), z ∈ Set.Icc a b := by
    have hmem : Set.Ioo x b ∈ nhdsWithin x (Set.Ioi x) := by
      rw [← Set.Ioi_inter_Iio]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.2)
    filter_upwards [hmem] with z hz
    exact ⟨le_trans hx.1 hz.1.le, hz.2.le⟩
  refine (hfreq.and_eventually hev).mono ?_
  rintro z ⟨hzlt, hzIcc⟩
  rw [hGsInf hxIcc, hGsInf hzIcc] at hzlt
  have hring : -sSup (F x '' Set.Icc (0:ℝ) 1) - -sSup (F z '' Set.Icc (0:ℝ) 1)
      = sSup (F z '' Set.Icc (0:ℝ) 1) - sSup (F x '' Set.Icc (0:ℝ) 1) := by ring
  rw [hring] at hzlt
  exact hzlt

end ShenWork.MaxPrincipleAtoms
