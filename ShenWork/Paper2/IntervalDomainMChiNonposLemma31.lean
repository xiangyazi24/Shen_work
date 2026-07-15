/-
  Lemma 3.1 for the faithful general-m interval model.
-/
import ShenWork.Paper2.IntervalDomainMChiNonposMax

open ShenWork.IntervalDomain ShenWork.Paper2 Filter Topology
open ShenWork.MaxPrincipleAtoms Set

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMChiNonpos

/-- A nonpositive slope at every spatial maximum makes the sup norm
nonincreasing. -/
theorem supNorm_nonincr_core_M
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hub : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ xs ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u s) xs =
          sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
        deriv (fun r => intervalDomainLift (u r) xs) s ≤ 0) :
    SupNormNonincreasingOn intervalDomainM u (Set.Ioo (0 : ℝ) T) := by
  obtain ⟨_, hTimeReg, _, _, _, hdF6, hSol7⟩ := hsol.regularity
  set F : ℝ → ℝ → ℝ := fun t y => intervalDomainLift (u t) y
    with hF_def
  have hsupeq : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainSupNorm (u s) =
        sSup (F s '' Set.Icc (0 : ℝ) 1) :=
    fun s hs => supNorm_eq_sSup_lift_image
      (fun q => (hsol.u_pos' hs.1 hs.2).le)
  have hFwin : ∀ {a b : ℝ}, Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    fun hsub => hSol7.1.mono (Set.prod_mono hsub (le_refl _))
  have hcont : ContinuousOn (fun t => intervalDomainSupNorm (u t))
      (Set.Ioo (0 : ℝ) T) := by
    have hSSup : ContinuousOn
        (fun t => sSup (F t '' Set.Icc (0 : ℝ) 1))
        (Set.Ioo (0 : ℝ) T) := by
      intro x hx
      have ha_pos : 0 < x / 2 := by linarith [hx.1]
      have hb_T : (x + T) / 2 < T := by linarith [hx.2]
      have hax : x / 2 < x := by linarith [hx.1]
      have hxb : x < (x + T) / 2 := by linarith [hx.2]
      have hsub : Set.Icc (x / 2) ((x + T) / 2) ⊆
          Set.Ioo (0 : ℝ) T := fun s hs =>
        ⟨lt_of_lt_of_le ha_pos hs.1, lt_of_le_of_lt hs.2 hb_T⟩
      exact ((sliceMax_continuousOn (hFwin hsub)) x
        ⟨hax.le, hxb.le⟩).mono_of_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hax hxb))
    exact hSSup.congr hsupeq
  have hDini : ∀ x ∈ Set.Ioo (0 : ℝ) T, ∀ r : ℝ, 0 < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ *
          (intervalDomainSupNorm (u z) - intervalDomainSupNorm (u x)) < r := by
    intro x hx r hr
    have ha_pos : 0 < x / 2 := by linarith [hx.1]
    have hb_T : (x + T) / 2 < T := by linarith [hx.2]
    have hax : x / 2 ≤ x := by linarith [hx.1]
    have hxb : x < (x + T) / 2 := by linarith [hx.2]
    have hsub : Set.Icc (x / 2) ((x + T) / 2) ⊆
        Set.Ioo (0 : ℝ) T := fun s hs =>
      ⟨lt_of_lt_of_le ha_pos hs.1, lt_of_le_of_lt hs.2 hb_T⟩
    have hFab := hFwin hsub
    have hslice_cont : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ContinuousOn (fun r => F r y)
          (Set.Icc (x / 2) ((x + T) / 2)) := by
      intro y hy
      have hmaps : Set.MapsTo (fun r => (r, y))
          (Set.Icc (x / 2) ((x + T) / 2))
          (Set.Icc (x / 2) ((x + T) / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
        fun w hw => ⟨hw, hy⟩
      exact hFab.comp (Continuous.continuousOn (by fun_prop)) hmaps
    have hslice_diff : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Ioo (x / 2) ((x + T) / 2),
          HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s := by
      intro y hy s hs
      have hsInt : s ∈ Set.Ioo (0 : ℝ) T :=
        hsub (Set.Ioo_subset_Icc_self hs)
      have hfun : (fun r => F r y) = fun r => u r ⟨y, hy⟩ := by
        funext r
        show intervalDomainLift (u r) y = u r ⟨y, hy⟩
        rw [intervalDomainLift, dif_pos hy]
      rw [hfun]
      exact ((hTimeReg ⟨y, hy⟩ s hsInt).1.1).hasDerivAt
    have hdFc : ContinuousOn
        (Function.uncurry (fun s y => deriv (fun r => F r y) s))
        (Set.Icc (x / 2) ((x + T) / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
      hdF6.1.mono (Set.prod_mono hsub (le_refl _))
    have hbnd : ∀ s ∈ Set.Icc (x / 2) ((x + T) / 2),
        ∀ xs ∈ Set.Icc (0 : ℝ) 1,
          F s xs = sSup (F s '' Set.Icc (0 : ℝ) 1) →
            deriv (fun r => F r xs) s ≤
              (0 : ℝ) * sSup (F s '' Set.Icc (0 : ℝ) 1) := by
      intro s hs xs hxs hargmax
      rw [zero_mul]
      exact hub s (hsub hs) xs hxs hargmax
    have hdini := sliceMax_dini_of_argmax_bound (Kp := 0) hFab
      hslice_cont hslice_diff (sliceMax_continuousOn hFab) hdFc hbnd x
        ⟨hax, hxb⟩ r (by rw [zero_mul]; exact hr)
    have hev : ∀ᶠ z in nhdsWithin x (Set.Ioi x),
        z ∈ Set.Ioo (0 : ℝ) T := by
      have hmem : Set.Ioo x T ∈ nhdsWithin x (Set.Ioi x) := by
        rw [← Set.Ioi_inter_Iio]
        exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.2)
      filter_upwards [hmem] with z hz
      exact ⟨lt_trans hx.1 hz.1, hz.2⟩
    refine (hdini.and_eventually hev).mono ?_
    rintro z ⟨hzlt, hzmem⟩
    rw [← hsupeq z hzmem, ← hsupeq x hx] at hzlt
    exact hzlt
  exact ShenWork.Paper2.Lemma31Heat.supNorm_nonincreasing_of_dini
    hcont hDini

/-- The zero-linear-growth branch of Lemma 3.1. -/
theorem lemma31_zero_M
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : p.a = 0)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v) :
    SupNormNonincreasingOn intervalDomainM u (Set.Ioo (0 : ℝ) T) := by
  refine supNorm_nonincr_core_M hsol ?_
  intro s hs xs hxs hargmax
  have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
    intro y
    have hcontU : ContinuousOn (intervalDomainLift (u s))
        (Set.Icc (0 : ℝ) 1) :=
      (hsol.regularity.2.2.2.2.1 s hs).1.1.continuousOn
    have hbdd : BddAbove
        (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
    have huy : u s y = intervalDomainLift (u s) y.1 := by
      rw [intervalDomainLift, dif_pos y.2, Subtype.coe_eta]
    have huq : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
      rw [intervalDomainLift, dif_pos hxs]
    rw [huy, huq, hargmax]
    exact le_csSup hbdd (Set.mem_image_of_mem _ y.2)
  have hsl := max_point_slope_bound_M hχ hsol hs.1 hs.2 hmax
  have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩ =
      deriv (fun r => intervalDomainLift (u r) xs) s := by
    show deriv (fun r => u r ⟨xs, hxs⟩) s =
      deriv (fun r => intervalDomainLift (u r) xs) s
    congr 1
    funext r
    rw [intervalDomainLift, dif_pos hxs]
  rw [htd, ha] at hsl
  have hb_nonneg := p.hb
  have hu_nonneg : 0 ≤ intervalDomainLift (u s) xs := by
    rw [intervalDomainLift, dif_pos hxs]
    exact (hsol.u_pos' hs.1 hs.2).le
  have hpow_nonneg : 0 ≤ intervalDomainLift (u s) xs ^ p.α :=
    Real.rpow_nonneg hu_nonneg _
  nlinarith [mul_nonneg hb_nonneg hpow_nonneg]

end ShenWork.Paper2.IntervalDomainMChiNonpos
