/-
  Lemma 3.1 for the faithful general-m interval model.
-/
import ShenWork.Paper2.IntervalDomainMChiNonposMax

open ShenWork.IntervalDomain ShenWork.Paper2 Filter Topology
open ShenWork.MaxPrincipleAtoms Set
open ShenWork.MinPersistenceAtoms

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
    {T : ℝ} (_hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
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
      rw [intervalDomainLift,
        dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from y.2),
        Subtype.coe_eta]
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

/-- Above the logistic carrying capacity, the general-`m` sup norm is
nonincreasing on the whole preceding time interval. -/
theorem lemma31_above_capacity_M
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {T : ℝ} (_hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t₀ : ℝ} (_ht₀ : 0 < t₀) (ht₀T : t₀ < T)
    (hsup : (p.a / p.b) ^ (1 / p.α) < intervalDomainM.supNorm (u t₀)) :
    SupNormNonincreasingOn intervalDomainM u (Set.Ioc (0 : ℝ) t₀) := by
  obtain ⟨_, hTimeReg, _, _, hClosed, hdF6, hSol7⟩ := hsol.regularity
  set M : ℝ → ℝ := fun t => intervalDomainM.supNorm (u t) with hM_def
  set c : ℝ := (p.a / p.b) ^ (1 / p.α) with hc_def
  have hMt₀ : c < M t₀ := hsup
  have hca : (0 : ℝ) ≤ p.a / p.b := div_nonneg ha.le hb.le
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg hca _
  have hcpow : c ^ p.α = p.a / p.b := by
    rw [hc_def, ← Real.rpow_mul hca,
      one_div_mul_cancel (ne_of_gt p.hα), Real.rpow_one]
  have hcap : ∀ m : ℝ, 0 ≤ m → c ≤ m →
      p.a - p.b * m ^ p.α ≤ 0 := by
    intro m hm hcm
    have h1 : c ^ p.α ≤ m ^ p.α :=
      Real.rpow_le_rpow hc_nonneg hcm p.hα.le
    rw [hcpow] at h1
    have h2 := (div_le_iff₀ hb).mp h1
    nlinarith [h2]
  have hsupeq : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      M s = sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
    fun s hs => supNorm_eq_sSup_lift_image
      (fun q => (hsol.u_pos' hs.1 hs.2).le)
  have hFwin : ∀ {a b : ℝ}, Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T →
      ContinuousOn
        (Function.uncurry (fun t y => intervalDomainLift (u t) y))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    fun hsub => hSol7.1.mono (Set.prod_mono hsub (le_refl _))
  have hMcont : ContinuousOn M (Set.Ioo (0 : ℝ) T) := by
    have hSSup : ContinuousOn
        (fun t => sSup
          (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1))
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
  have hmono_win : ∀ a b : ℝ,
      Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T →
      (∀ s ∈ Set.Icc a b, c ≤ M s) →
      ∀ t₁ ∈ Set.Icc a b, ∀ t₂ ∈ Set.Icc a b, t₁ ≤ t₂ →
        M t₂ ≤ M t₁ := by
    intro a b hab hge
    have hFab := hFwin hab
    have hslice_cont : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ContinuousOn (fun r => intervalDomainLift (u r) y)
          (Set.Icc a b) := by
      intro y hy
      have hmaps : Set.MapsTo (fun r => (r, y)) (Set.Icc a b)
          (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
        fun w hw => ⟨hw, hy⟩
      exact hFab.comp (Continuous.continuousOn (by fun_prop)) hmaps
    have hslice_diff : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Ioo a b,
          HasDerivAt (fun r => intervalDomainLift (u r) y)
            (deriv (fun r => intervalDomainLift (u r) y) s) s := by
      intro y hy s hs
      have hsInt : s ∈ Set.Ioo (0 : ℝ) T :=
        hab (Set.Ioo_subset_Icc_self hs)
      have hfun : (fun r => intervalDomainLift (u r) y) =
          fun r => u r ⟨y, hy⟩ := by
        funext r
        rw [intervalDomainLift, dif_pos hy]
      rw [hfun]
      exact ((hTimeReg ⟨y, hy⟩ s hsInt).1.1).hasDerivAt
    have hdFc : ContinuousOn
        (Function.uncurry
          (fun s y => deriv (fun r => intervalDomainLift (u r) y) s))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
      hdF6.1.mono (Set.prod_mono hab (le_refl _))
    have hsupeq_ab : ∀ s ∈ Set.Icc a b,
        M s = sSup
          (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      fun s hs => hsupeq s (hab hs)
    have hbnd : ∀ s ∈ Set.Icc a b,
        ∀ xs ∈ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (u s) xs =
              sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
            deriv (fun r => intervalDomainLift (u r) xs) s ≤
              (0 : ℝ) * sSup
                (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
      intro s hs xs hxs hargmax
      rw [zero_mul]
      have hsmem := hab hs
      have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
        intro y
        have hcontU : ContinuousOn (intervalDomainLift (u s))
            (Set.Icc (0 : ℝ) 1) :=
          (hClosed s hsmem).1.1.continuousOn
        have hbdd : BddAbove
            (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
          (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
        have huy : u s y = intervalDomainLift (u s) y.1 := by
          rw [intervalDomainLift,
            dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from y.2),
            Subtype.coe_eta]
        have huq : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
          rw [intervalDomainLift, dif_pos hxs]
        rw [huy, huq, hargmax]
        exact le_csSup hbdd (Set.mem_image_of_mem _ y.2)
      have hsl := max_point_slope_bound_M hχ hsol
        hsmem.1 hsmem.2 hmax
      have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩ =
          deriv (fun r => intervalDomainLift (u r) xs) s := by
        show deriv (fun r => u r ⟨xs, hxs⟩) s =
          deriv (fun r => intervalDomainLift (u r) xs) s
        congr 1
        funext r
        rw [intervalDomainLift, dif_pos hxs]
      rw [htd] at hsl
      have hxs_eq : intervalDomainLift (u s) xs = M s := by
        rw [hsupeq_ab s hs, hargmax]
      have hxs_nonneg : 0 ≤ intervalDomainLift (u s) xs := by
        rw [intervalDomainLift, dif_pos hxs]
        exact (hsol.u_pos' hsmem.1 hsmem.2).le
      have hcap_s : p.a -
          p.b * intervalDomainLift (u s) xs ^ p.α ≤ 0 :=
        hcap _ hxs_nonneg (by rw [hxs_eq]; exact hge s hs)
      exact le_trans hsl
        (mul_nonpos_of_nonneg_of_nonpos hxs_nonneg hcap_s)
    have hDini : ∀ x ∈ Set.Ico a b, ∀ r : ℝ, 0 < r →
        ∃ᶠ z in nhdsWithin x (Set.Ioi x),
          (z - x)⁻¹ * (M z - M x) < r := by
      intro x hx r hr
      have hdini := sliceMax_dini_of_argmax_bound (Kp := 0) hFab
        hslice_cont hslice_diff (sliceMax_continuousOn hFab) hdFc hbnd
          x hx r (by rw [zero_mul]; exact hr)
      have hev : ∀ᶠ z in nhdsWithin x (Set.Ioi x), z ∈ Set.Icc a b := by
        have hmem : Set.Ioo x b ∈ nhdsWithin x (Set.Ioi x) := by
          rw [← Set.Ioi_inter_Iio]
          exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.2)
        filter_upwards [hmem] with z hz
        exact ⟨le_trans hx.1 hz.1.le, hz.2.le⟩
      refine (hdini.and_eventually hev).mono ?_
      rintro z ⟨hzlt, hzmem⟩
      rw [← hsupeq_ab z hzmem,
        ← hsupeq_ab x (Set.Ico_subset_Icc_self hx)] at hzlt
      exact hzlt
    have hcontM : ContinuousOn M (Set.Icc a b) :=
      (sliceMax_continuousOn hFab).congr hsupeq_ab
    exact fun t₁ h₁ t₂ h₂ hle =>
      ShenWork.Paper2.Lemma31Closure.mono_of_dini_window
        hcontM hDini h₁ h₂ hle
  have hpersist : ∀ s ∈ Set.Ioc (0 : ℝ) t₀, c ≤ M s := by
    intro s hsmem
    by_contra hlt
    push Not at hlt
    have hs_pos : 0 < s := hsmem.1
    have hst₀ : s ≤ t₀ := hsmem.2
    have hsub_st₀ : Set.Icc s t₀ ⊆ Set.Ioo (0 : ℝ) T :=
      fun z hz =>
        ⟨lt_of_lt_of_le hs_pos hz.1, lt_of_le_of_lt hz.2 ht₀T⟩
    have hMcont_st₀ : ContinuousOn M (Set.Icc s t₀) :=
      hMcont.mono hsub_st₀
    set A : Set ℝ := {z | z ∈ Set.Icc s t₀ ∧ M z ≤ c} with hA_def
    have hsA : s ∈ A := ⟨⟨le_rfl, hst₀⟩, hlt.le⟩
    have hAbdd : BddAbove A := ⟨t₀, fun z hz => hz.1.2⟩
    have hAne : A.Nonempty := ⟨s, hsA⟩
    have hAeq : A = Set.Icc s t₀ ∩ M ⁻¹' Set.Iic c := by
      ext z
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2⟩
    have hAclosed : IsClosed A := by
      rw [hAeq]
      exact hMcont_st₀.preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Iic
    set tstar : ℝ := sSup A with htstar_def
    have htstar_A : tstar ∈ A := hAclosed.csSup_mem hAne hAbdd
    have htstar_mem : tstar ∈ Set.Icc s t₀ := htstar_A.1
    have hMtstar_le : M tstar ≤ c := htstar_A.2
    have hs_le_tstar : s ≤ tstar := htstar_mem.1
    have htstar_le : tstar ≤ t₀ := htstar_mem.2
    have htstar_lt : tstar < t₀ := by
      rcases lt_or_eq_of_le htstar_le with h | h
      · exact h
      · exfalso
        rw [h] at hMtstar_le
        linarith [hMt₀]
    have hMt₀_le : ∀ z ∈ Set.Ioo tstar t₀, M t₀ ≤ M z := by
      intro z hz
      have hz_pos : 0 < z :=
        lt_of_lt_of_le hs_pos
          (le_trans hs_le_tstar hz.1.le)
      have hzt₀ : Set.Icc z t₀ ⊆ Set.Ioo (0 : ℝ) T :=
        fun r hr =>
          ⟨lt_of_lt_of_le hz_pos hr.1, lt_of_le_of_lt hr.2 ht₀T⟩
      have hge_z : ∀ r ∈ Set.Icc z t₀, c ≤ M r := by
        intro r hr
        by_contra hrlt
        push Not at hrlt
        have hrA : r ∈ A :=
          ⟨⟨le_trans hs_le_tstar (le_trans hz.1.le hr.1), hr.2⟩,
            hrlt.le⟩
        have : r ≤ tstar := le_csSup hAbdd hrA
        exact (not_le.mpr (lt_of_lt_of_le hz.1 hr.1)) this
      exact hmono_win z t₀ hzt₀ hge_z z
        ⟨le_rfl, hz.2.le⟩ t₀ ⟨hz.2.le, le_rfl⟩ hz.2.le
    have hMt₀_le_tstar : M t₀ ≤ M tstar := by
      haveI : (nhdsWithin tstar (Set.Ioo tstar t₀)).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (by
          rw [closure_Ioo (ne_of_lt htstar_lt)]
          exact ⟨le_rfl, htstar_lt.le⟩)
      have hcont_r : Tendsto M
          (nhdsWithin tstar (Set.Ioo tstar t₀)) (nhds (M tstar)) :=
        (hMcont_st₀ tstar htstar_mem).mono_left
          (nhdsWithin_mono tstar (fun r hr =>
            ⟨le_of_lt (lt_of_le_of_lt hs_le_tstar hr.1), hr.2.le⟩))
      refine ge_of_tendsto hcont_r ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hMt₀_le z hz
    linarith [hMt₀_le_tstar, hMtstar_le, hMt₀]
  intro t₁ ht₁ t₂ ht₂ hle
  have hsub_t : Set.Icc t₁ t₂ ⊆ Set.Ioo (0 : ℝ) T :=
    fun r hr =>
      ⟨lt_of_lt_of_le ht₁.1 hr.1,
        lt_of_le_of_lt (le_trans hr.2 ht₂.2) ht₀T⟩
  have hge_t : ∀ r ∈ Set.Icc t₁ t₂, c ≤ M r :=
    fun r hr => hpersist r
      ⟨lt_of_lt_of_le ht₁.1 hr.1, le_trans hr.2 ht₂.2⟩
  exact hmono_win t₁ t₂ hsub_t hge_t t₁ ⟨le_rfl, hle⟩
    t₂ ⟨hle, le_rfl⟩ hle

end ShenWork.Paper2.IntervalDomainMChiNonpos
