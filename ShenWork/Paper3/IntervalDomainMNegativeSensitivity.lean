import ShenWork.Paper3.IntervalDomainNegativeSensitivityMaxDecay
import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassFloor
import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassConvergence
import ShenWork.Paper3.IntervalDomainGlobalTailHolderM
import ShenWork.Paper3.IntervalDomainThetaMomentUniform
import ShenWork.Paper2.IntervalDomainMChiNonposMax
import ShenWork.Paper2.IntervalDomainMChiNonposLemma31
import ShenWork.Paper2.IntervalDomainMMass

/-!
# χ₀ ≤ 0 global attraction for the faithful general-`m` equation

For the neutral / repulsive sensitivity regime `χ₀ ≤ 0` the positive logistic
equilibrium attracts every bounded global orbit of the faithful `u^m` flux.
The genuinely `m`-specific max-principle inputs already exist
(`max_point_slope_bound_M`, `lemma31_above_capacity_M`); this file assembles
the supremum-decay Gronwall, the Hölder mass floor, the reaction coercivity,
mass convergence to the carrying capacity, and the Arzelà–Ascoli uniform
convergence, with NO `p.m = 1` hypothesis.
-/

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.MaxPrincipleAtoms ShenWork.MinPersistenceAtoms
open ShenWork.Paper2.IntervalDomainMChiNonpos

namespace ShenWork.Paper3

noncomputable section

/-! ## Faithful helper facts (continuity/positivity-only, from the M solution) -/

/-- Pointwise absolute control by the supremum norm for a faithful slice. -/
theorem abs_lift_le_supNorm_M
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |intervalDomainLift (u τ) y| ≤ intervalDomainSupNorm (u τ) := by
  have hcont : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol hτ
  have hc : Continuous (u τ) := by
    have := hcont.comp_continuous (continuous_subtype_val)
      (fun x : intervalDomainPoint => x.2)
    exact this.congr (fun x => by simp [Function.comp, intervalDomainLift, x.2])
  have hbdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u τ x|)) := by
    have himg := isCompact_univ.image hc.abs
    rw [Set.image_univ] at himg
    exact himg.bddAbove
  change |intervalDomainLift (u τ) y| ≤ sSup _
  rw [intervalDomainLift, dif_pos hy]
  exact le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩

/-- Mass bounded by supremum norm for a faithful `u^m` positive classical
slice. -/
theorem intervalDomainM_classicalSolution_mass_le_supNorm
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomainM.integral (u t) ≤ intervalDomainM.supNorm (u t) := by
  have hu_cont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol ht
  have hu_int : IntervalIntegrable (intervalDomainLift (u t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hu_cont
  change intervalDomainIntegral (u t) ≤ intervalDomainSupNorm (u t)
  unfold intervalDomainIntegral
  calc ∫ y in (0:ℝ)..1, intervalDomainLift (u t) y
      ≤ ∫ _y in (0:ℝ)..1, intervalDomainSupNorm (u t) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hu_int
          intervalIntegrable_const
        intro y hy
        exact le_trans (le_abs_self _) (abs_lift_le_supNorm_M hsol ht hy)
    _ = intervalDomainSupNorm (u t) := by simp

/-! ## Supremum-norm Gronwall decay (χ₀ ≤ 0) -/

/-- Faithful `u^m` copy of the supremum-norm Gronwall window bound.  The proof
is kinematic (regularity only); the flux never enters. -/
theorem intervalDomainM_supNorm_gronwall_on_window
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {a b K : ℝ} (hab : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (hmaxSlope : ∀ s ∈ Set.Icc a b, ∀ xs ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u s) xs =
          sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
      deriv (fun r => intervalDomainLift (u r) xs) s ≤
        K * sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1))
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc a b) (ht₂ : t₂ ∈ Set.Icc a b)
    (ht : t₁ ≤ t₂) :
    intervalDomainM.supNorm (u t₂) ≤
      intervalDomainM.supNorm (u t₁) * Real.exp (K * (t₂ - t₁)) := by
  obtain ⟨_, hTimeReg, _, _, _, hdF6, hSol7⟩ := hsol.regularity
  let F : ℝ → ℝ → ℝ := fun t y => intervalDomainLift (u t) y
  let M : ℝ → ℝ := fun t => intervalDomainM.supNorm (u t)
  have hFab : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hSol7.1.mono (Set.prod_mono hab (le_refl _))
  have hsupeq : ∀ s ∈ Set.Icc a b,
      M s = sSup (F s '' Set.Icc (0 : ℝ) 1) := by
    intro s hs
    exact supNorm_eq_sSup_lift_image
      (fun q => (hsol.u_pos' (hab hs).1 (hab hs).2).le)
  have hslice_cont : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun r => F r y) (Set.Icc a b) := by
    intro y hy
    have hmaps : Set.MapsTo (fun r => (r, y)) (Set.Icc a b)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := fun w hw => ⟨hw, hy⟩
    exact hFab.comp (Continuous.continuousOn (by fun_prop)) hmaps
  have hslice_diff : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Ioo a b,
      HasDerivAt (fun r => F r y) (deriv (fun r => F r y) s) s := by
    intro y hy s hs
    have hsInt : s ∈ Set.Ioo (0 : ℝ) T := hab (Set.Ioo_subset_Icc_self hs)
    have hfun : (fun r => F r y) = fun r => u r ⟨y, hy⟩ := by
      funext r
      show intervalDomainLift (u r) y = u r ⟨y, hy⟩
      rw [intervalDomainLift, dif_pos hy]
    rw [hfun]
    exact ((hTimeReg ⟨y, hy⟩ s hsInt).1.1).hasDerivAt
  have hdFc : ContinuousOn
      (Function.uncurry (fun s y => deriv (fun r => F r y) s))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hdF6.1.mono (Set.prod_mono hab (le_refl _))
  have hbnd : ∀ s ∈ Set.Icc a b, ∀ xs ∈ Set.Icc (0 : ℝ) 1,
      F s xs = sSup (F s '' Set.Icc (0 : ℝ) 1) →
      deriv (fun r => F r xs) s ≤ K * sSup (F s '' Set.Icc (0 : ℝ) 1) := by
    simpa [F] using hmaxSlope
  have hDini : ∀ x ∈ Set.Ico a b, ∀ r : ℝ, K * M x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (M z - M x) < r := by
    intro x hx r hr
    have hxIcc : x ∈ Set.Icc a b := Set.Ico_subset_Icc_self hx
    have hdini := sliceMax_dini_of_argmax_bound (Kp := K)
      hFab hslice_cont hslice_diff (sliceMax_continuousOn hFab) hdFc hbnd
      x hx r (by rwa [← hsupeq x hxIcc])
    have hev : ∀ᶠ z in nhdsWithin x (Set.Ioi x), z ∈ Set.Icc a b := by
      have hmem : Set.Ioo x b ∈ nhdsWithin x (Set.Ioi x) := by
        rw [← Set.Ioi_inter_Iio]
        exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.2)
      filter_upwards [hmem] with z hz
      exact ⟨le_trans hx.1 hz.1.le, hz.2.le⟩
    refine (hdini.and_eventually hev).mono ?_
    rintro z ⟨hzlt, hzmem⟩
    rwa [← hsupeq z hzmem, ← hsupeq x hxIcc] at hzlt
  have hcontM : ContinuousOn M (Set.Icc a b) :=
    (sliceMax_continuousOn hFab).congr hsupeq
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc a b := fun s hs =>
    ⟨le_trans ht₁.1 hs.1, le_trans hs.2 ht₂.2⟩
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f := M) (f' := fun s => K * M s)
    (δ := M t₁) (K := K) (ε := 0) (a := t₁) (b := t₂)
    (hcontM.mono hsub)
    (by
      intro x hx r hr
      exact hDini x ⟨le_trans ht₁.1 hx.1, lt_of_lt_of_le hx.2 ht₂.2⟩ r hr)
    (le_refl _) (by intro x _; simp)
  have hbound := hgron t₂ (Set.right_mem_Icc.mpr ht)
  simpa [M, gronwallBound_ε0] using hbound

/-- Above the carrying capacity, the faithful `u^m` supremum norm decays
exponentially through the χ₀ ≤ 0 max-principle. -/
theorem intervalDomainM_chiNonpos_supNorm_decay_if_above_capacity_add
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {ε t : ℝ} (hε : 0 < ε) (ht : 1 ≤ t)
    (habove : (p.a / p.b) ^ (1 / p.α) + ε <
      intervalDomainM.supNorm (u t)) :
    intervalDomainM.supNorm (u t) ≤
      intervalDomainM.supNorm (u 1) *
        Real.exp ((p.a - p.b *
          (((p.a / p.b) ^ (1 / p.α) + ε) ^ p.α)) * (t - 1)) := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let K : ℝ := p.a - p.b * ((c + ε) ^ p.α)
  let H : ℝ := t + 1
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  have hsol := huv.classical H hH
  have hcAbove : c < intervalDomainM.supNorm (u t) := by
    dsimp [c]; linarith
  have hmono := lemma31_above_capacity_M
    p hχ ha hb hH hsol htpos htH hcAbove
  have hab : Set.Icc (1 : ℝ) t ⊆ Set.Ioo (0 : ℝ) H := by
    intro s hs
    exact ⟨lt_of_lt_of_le (by norm_num) hs.1, lt_of_le_of_lt hs.2 htH⟩
  have hmaxSlope : ∀ s ∈ Set.Icc (1 : ℝ) t,
      ∀ xs ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u s) xs =
          sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
      deriv (fun r => intervalDomainLift (u r) xs) s ≤
        K * sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
    intro s hs xs hxs hargmax
    have hsmem : s ∈ Set.Ioo (0 : ℝ) H := hab hs
    have hcontU : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 s hsmem).1.1).continuousOn
    have hbdd : BddAbove
        (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
    have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
      intro y
      have huy : u s y = intervalDomainLift (u s) y.1 := by
        rw [intervalDomainLift,
          dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from y.2), Subtype.coe_eta]
      have huxs : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
        rw [intervalDomainLift, dif_pos hxs]
      rw [huy, huxs, hargmax]
      exact le_csSup hbdd (Set.mem_image_of_mem _ y.2)
    have hslope := max_point_slope_bound_M hχ hsol hsmem.1 hsmem.2 hmax
    have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩ =
        deriv (fun r => intervalDomainLift (u r) xs) s := by
      show deriv (fun r => u r ⟨xs, hxs⟩) s =
        deriv (fun r => intervalDomainLift (u r) xs) s
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos hxs]
    rw [htd] at hslope
    have hsupeq : intervalDomainM.supNorm (u s) =
        sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      supNorm_eq_sSup_lift_image
        (fun q => (hsol.u_pos' hsmem.1 hsmem.2).le)
    have hterminal : intervalDomainM.supNorm (u t) ≤
        intervalDomainM.supNorm (u s) := by
      exact hmono s ⟨lt_of_lt_of_le (by norm_num) hs.1, hs.2⟩
        t ⟨htpos, le_refl _⟩ hs.2
    have hlevel : c + ε ≤ intervalDomainLift (u s) xs := by
      rw [hargmax, ← hsupeq]
      exact le_trans habove.le hterminal
    have hvalue_nonneg : 0 ≤ intervalDomainLift (u s) xs := by
      rw [intervalDomainLift, dif_pos hxs]
      exact (hsol.u_pos' hsmem.1 hsmem.2).le
    have hbase_nonneg : 0 ≤ c + ε := by
      have hratio : 0 ≤ p.a / p.b := div_nonneg ha.le hb.le
      have hc : 0 ≤ c := by dsimp [c]; exact Real.rpow_nonneg hratio _
      linarith
    have hpow : (c + ε) ^ p.α ≤
        (intervalDomainLift (u s) xs) ^ p.α :=
      Real.rpow_le_rpow hbase_nonneg hlevel p.hα.le
    have hcoef : p.a - p.b *
        (intervalDomainLift (u s) xs) ^ p.α ≤ K := by
      dsimp [K]
      nlinarith [mul_le_mul_of_nonneg_left hpow hb.le]
    have hreact : intervalDomainLift (u s) xs *
        (p.a - p.b * (intervalDomainLift (u s) xs) ^ p.α) ≤
        K * intervalDomainLift (u s) xs := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcoef hvalue_nonneg
    exact hslope.trans (by simpa [hargmax] using hreact)
  have hgron := intervalDomainM_supNorm_gronwall_on_window
    hsol hab hmaxSlope (t₁ := (1 : ℝ)) (t₂ := t)
    ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simpa [K, c] using hgron

/-- Every bounded positive repulsive orbit is eventually below the carrying
capacity up to any margin. -/
theorem intervalDomainM_chiNonpos_eventually_supNorm_le_capacity_add
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      intervalDomainM.supNorm (u t) ≤
        (p.a / p.b) ^ (1 / p.α) + ε := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let K : ℝ := p.a - p.b * ((c + ε) ^ p.α)
  have hratio : 0 ≤ p.a / p.b := div_nonneg ha.le hb.le
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg hratio _
  have hcpow : c ^ p.α = p.a / p.b := by
    rw [show c = (p.a / p.b) ^ (1 / p.α) by rfl,
      ← Real.rpow_mul hratio, one_div_mul_cancel (ne_of_gt p.hα), Real.rpow_one]
  have hpow : c ^ p.α < (c + ε) ^ p.α :=
    Real.rpow_lt_rpow hc_nonneg (by linarith) p.hα
  have hdiv : p.a / p.b < (c + ε) ^ p.α := by rwa [hcpow] at hpow
  have hmul : p.a < p.b * ((c + ε) ^ p.α) := by
    simpa [mul_comm] using (div_lt_iff₀ hb).mp hdiv
  have hKneg : K < 0 := by dsimp [K]; linarith
  have hlin : Tendsto (fun t : ℝ => K * (t - 1)) atTop atBot := by
    have hbase : Tendsto (fun t : ℝ => K * t + (-K)) atTop atBot :=
      tendsto_atBot_add_const_right _ (-K)
        (tendsto_id.const_mul_atTop_of_neg hKneg)
    convert hbase using 1
    funext t; ring
  have hexp : Tendsto (fun t : ℝ => Real.exp (K * (t - 1)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hlin
  have hdecay : Tendsto
      (fun t : ℝ => intervalDomainM.supNorm (u 1) *
        Real.exp (K * (t - 1))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp)
  have hthreshold : 0 < c + ε := by linarith
  have hevlt : ∀ᶠ t in atTop,
      intervalDomainM.supNorm (u 1) * Real.exp (K * (t - 1)) < c + ε :=
    (tendsto_order.1 hdecay).2 _ hthreshold
  filter_upwards [hevlt, eventually_ge_atTop (1 : ℝ)] with t hright ht
  by_contra hnot
  have habove : c + ε < intervalDomainM.supNorm (u t) := lt_of_not_ge hnot
  have hbound := intervalDomainM_chiNonpos_supNorm_decay_if_above_capacity_add
    p hχ ha hb huv hε ht (by simpa [c] using habove)
  have : intervalDomainM.supNorm (u t) ≤
      intervalDomainM.supNorm (u 1) * Real.exp (K * (t - 1)) := by
    simpa [K, c] using hbound
  linarith

/-! ## Hölder mass floor -/

/-- A nonnegative Hölder-`1/2` profile on `[0,1]` whose maximum is at least
`c/2` has explicit positive mass.  The Hölder exponent shrinks the guaranteed
width to a square but keeps a strictly positive floor. -/
theorem interval_holder_mass_lower_of_sSup_ge_half
    {f : ℝ → ℝ} {c G : ℝ} (hc : 0 < c) (hG : 0 ≤ G)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hnonneg : ∀ x, 0 ≤ f x)
    (hhol : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |f x - f y| ≤ G * |x - y| ^ ((1 : ℝ) / 2))
    (hsup : c / 2 ≤ sSup (f '' Set.Icc (0 : ℝ) 1)) :
    c * min (1 / 2 : ℝ) ((c / (8 * (G + 1))) ^ 2) / 4 ≤
      ∫ x in (0 : ℝ)..1, f x := by
  let ell : ℝ := min (1 / 2 : ℝ) ((c / (8 * (G + 1))) ^ 2)
  have hG1 : 0 < G + 1 := by linarith
  have hfrac : 0 < c / (8 * (G + 1)) := div_pos hc (by positivity)
  have hellPos : 0 < ell := by
    dsimp [ell]; exact lt_min (by norm_num) (by positivity)
  have hellHalf : ell ≤ 1 / 2 := by dsimp [ell]; exact min_le_left _ _
  have hellFrac : ell ≤ (c / (8 * (G + 1))) ^ 2 := by dsimp [ell]; exact min_le_right _ _
  have hsqrtell : ell ^ ((1 : ℝ) / 2) ≤ c / (8 * (G + 1)) := by
    have h1 : ell ^ ((1 : ℝ) / 2) ≤ ((c / (8 * (G + 1))) ^ 2) ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow hellPos.le hellFrac (by norm_num)
    have h2 : ((c / (8 * (G + 1))) ^ 2) ^ ((1:ℝ)/2) = c / (8 * (G + 1)) := by
      rw [show ((c / (8 * (G + 1))) ^ 2) = (c / (8 * (G + 1))) ^ (2:ℕ) from rfl,
        ← Real.rpow_natCast (c / (8 * (G + 1))) 2, ← Real.rpow_mul hfrac.le]
      norm_num
    rwa [h2] at h1
  have hGell : G * ell ^ ((1 : ℝ) / 2) ≤ c / 8 := by
    calc G * ell ^ ((1:ℝ)/2) ≤ G * (c / (8 * (G + 1))) :=
          mul_le_mul_of_nonneg_left hsqrtell hG
      _ ≤ (G + 1) * (c / (8 * (G + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hc.le (by positivity))
      _ = c / 8 := by field_simp
  obtain ⟨x₀, hx₀, hxmax, _⟩ :=
    isCompact_Icc.exists_sSup_image_eq_and_ge
      (Set.nonempty_Icc.mpr (by norm_num)) hcont
  have hxvalue : c / 2 ≤ f x₀ := by rwa [← hxmax]
  have hfint : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
  have hnonnegAe : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f :=
    Filter.Eventually.of_forall hnonneg
  have hdrop_of : ∀ y ∈ Set.Icc (0 : ℝ) 1, |x₀ - y| ≤ ell → c / 4 ≤ f y := by
    intro y hy hdist
    have hpow : |x₀ - y| ^ ((1:ℝ)/2) ≤ ell ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (abs_nonneg _) hdist (by norm_num)
    have hdrop : f x₀ - f y ≤ G * ell ^ ((1:ℝ)/2) :=
      (le_abs_self (f x₀ - f y)).trans
        ((hhol x₀ hx₀ y hy).trans (mul_le_mul_of_nonneg_left hpow hG))
    linarith
  by_cases hxleft : x₀ ≤ 1 / 2
  · have hright : x₀ + ell ≤ 1 := by linarith
    have hsub : Set.Icc x₀ (x₀ + ell) ⊆ Set.Icc (0 : ℝ) 1 := fun y hy =>
      ⟨le_trans hx₀.1 hy.1, le_trans hy.2 hright⟩
    have hpoint : ∀ y ∈ Set.Icc x₀ (x₀ + ell), c / 4 ≤ f y := fun y hy =>
      hdrop_of y (hsub hy) (by rw [abs_of_nonpos (sub_nonpos.mpr hy.1)]; linarith [hy.2])
    have hmonoSub : ∫ y in x₀..(x₀ + ell), c / 4 ≤ ∫ y in x₀..(x₀ + ell), f y :=
      intervalIntegral.integral_mono_on (by linarith [hellPos])
        intervalIntegrable_const
        ((hcont.mono hsub).intervalIntegrable_of_Icc (by linarith [hellPos])) hpoint
    have hsubFull : (∫ y in x₀..(x₀ + ell), f y) ≤ ∫ y in (0 : ℝ)..1, f y :=
      intervalIntegral.integral_mono_interval hx₀.1 (by linarith [hellPos])
        hright hnonnegAe hfint
    have hconst : (∫ _y in x₀..(x₀ + ell), c / 4) = c * ell / 4 := by
      simp [intervalIntegral.integral_const]; ring
    rw [hconst] at hmonoSub
    exact hmonoSub.trans hsubFull
  · have hxright : 1 / 2 < x₀ := lt_of_not_ge hxleft
    have hleft : 0 ≤ x₀ - ell := by linarith
    have hsub : Set.Icc (x₀ - ell) x₀ ⊆ Set.Icc (0 : ℝ) 1 := fun y hy =>
      ⟨le_trans hleft hy.1, le_trans hy.2 hx₀.2⟩
    have hpoint : ∀ y ∈ Set.Icc (x₀ - ell) x₀, c / 4 ≤ f y := fun y hy =>
      hdrop_of y (hsub hy) (by rw [abs_of_nonneg (sub_nonneg.mpr hy.2)]; linarith [hy.1])
    have hmonoSub : ∫ y in (x₀ - ell)..x₀, c / 4 ≤ ∫ y in (x₀ - ell)..x₀, f y :=
      intervalIntegral.integral_mono_on (by linarith [hellPos])
        intervalIntegrable_const
        ((hcont.mono hsub).intervalIntegrable_of_Icc (by linarith [hellPos])) hpoint
    have hsubFull : (∫ y in (x₀ - ell)..x₀, f y) ≤ ∫ y in (0 : ℝ)..1, f y :=
      intervalIntegral.integral_mono_interval hleft (by linarith [hellPos])
        hx₀.2 hnonnegAe hfint
    have hconst : (∫ _y in (x₀ - ell)..x₀, c / 4) = c * ell / 4 := by
      simp [intervalIntegral.integral_const]; ring
    rw [hconst] at hmonoSub
    exact hmonoSub.trans hsubFull

/-- Below half capacity the faithful `u^m` mass derivative is nonnegative. -/
theorem intervalDomainM_mass_hasDerivAt_nonneg_of_supNorm_lt_half_capacity
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hsup : intervalDomainM.supNorm (u t) < ((p.a / p.b) ^ (1 / p.α)) / 2) :
    ∃ d : ℝ, 0 ≤ d ∧
      HasDerivAt (fun s => intervalDomainM.integral (u s)) d t := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let rate : ℝ := p.a - p.b * ((c / 2) ^ p.α)
  have hratioPos : 0 < p.a / p.b := div_pos ha hb
  have hcPos : 0 < c := Real.rpow_pos_of_pos hratioPos _
  have hcpow : c ^ p.α = p.a / p.b := by
    rw [show c = (p.a / p.b) ^ (1 / p.α) by rfl, ← Real.rpow_mul hratioPos.le,
      one_div_mul_cancel (ne_of_gt p.hα), Real.rpow_one]
  have hhalfPow : (c / 2) ^ p.α < c ^ p.α :=
    Real.rpow_lt_rpow (by positivity) (by linarith) p.hα
  have hmul : p.b * ((c / 2) ^ p.α) < p.a := by
    have hdiv : (c / 2) ^ p.α < p.a / p.b := by rwa [← hcpow]
    simpa [mul_comm] using (lt_div_iff₀ hb).mp hdiv
  have hrate : 0 < rate := by dsimp [rate]; linarith
  let f : ℝ → ℝ := intervalDomainLift (u t)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol ht
  have hfpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < f y :=
    fun y hy => ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsol ht y hy
  have hfle : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y < c / 2 := by
    intro y hy
    exact lt_of_le_of_lt (le_trans (le_abs_self (f y)) (abs_lift_le_supNorm_M hsol ht hy))
      (by simpa [c] using hsup)
  have hf_int : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] using hfcont
  have hpowh_int : IntervalIntegrable (fun y => f y ^ (1 + p.α)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)]
    exact hfcont.rpow_const (fun y hy => Or.inl (ne_of_gt (hfpos y hy)))
  let d : ℝ := p.a * intervalDomainM.integral (u t) -
    p.b * intervalDomainM.integral (fun x => (u t x) ^ (1 + p.α))
  have hd : HasDerivAt (fun s => intervalDomainM.integral (u s)) d t := by
    simpa [d] using
      ShenWork.Paper2.IntervalDomainM.mass_logistic_hasDerivAt hsol ht.1 ht.2
  refine ⟨d, ?_, hd⟩
  have hmassPos : 0 < intervalDomainM.integral (u t) :=
    ShenWork.Paper2.IntervalDomainM.mass_pos hsol ht
  have hu_eq : intervalDomainM.integral (u t) = ∫ y in (0:ℝ)..1, f y := rfl
  have hh_eq : intervalDomainM.integral (fun x => (u t x) ^ (1 + p.α)) =
      ∫ y in (0:ℝ)..1, f y ^ (1 + p.α) := by
    change intervalDomainIntegral _ = _
    unfold intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at hy
    simp [f, intervalDomainLift, hy]
  have hdval : d = ∫ y in (0:ℝ)..1, (p.a * f y - p.b * f y ^ (1 + p.α)) := by
    rw [show d = p.a * intervalDomainM.integral (u t) -
        p.b * intervalDomainM.integral (fun x => (u t x) ^ (1 + p.α)) from rfl,
      hu_eq, hh_eq,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hf_int.const_mul p.a) (hpowh_int.const_mul p.b)]
  rw [hdval]
  have hpoint : ∀ y ∈ Set.Icc (0:ℝ) 1,
      rate * f y ≤ p.a * f y - p.b * f y ^ (1 + p.α) := by
    intro y hy
    have hpos := hfpos y hy
    have hmul2 : f y ^ (1 + p.α) = f y * f y ^ p.α := by
      rw [Real.rpow_add hpos, Real.rpow_one]
    have hpow : f y ^ p.α ≤ (c / 2) ^ p.α :=
      Real.rpow_le_rpow hpos.le (hfle y hy).le p.hα.le
    have hcoef : rate ≤ p.a - p.b * f y ^ p.α := by
      dsimp [rate]; nlinarith [mul_le_mul_of_nonneg_left hpow hb.le]
    rw [hmul2]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hpos.le]
  have hrateInt : IntervalIntegrable (fun y => rate * f y) volume 0 1 :=
    hf_int.const_mul rate
  have hrhsInt : IntervalIntegrable (fun y => p.a * f y - p.b * f y ^ (1 + p.α))
      volume 0 1 := (hf_int.const_mul p.a).sub (hpowh_int.const_mul p.b)
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hrateInt hrhsInt hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hleft : 0 ≤ rate * ∫ y in (0:ℝ)..1, f y := (mul_pos hrate (by rwa [← hu_eq])).le
  exact hleft.trans hmono

/-- Concrete positive tail mass for every bounded faithful `u^m` global orbit
in the positive logistic regime, via the proved Hölder tail modulus. -/
theorem intervalDomainM_globalBounded_eventual_mass_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∃ Tmass eta : ℝ, 0 < Tmass ∧ 0 < eta ∧
      ∀ t, Tmass ≤ t → eta ≤ intervalDomainM.integral (u t) := by
  obtain ⟨Th, Mh, G, hTh, _hMh, hG, _hsup, hhol⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let ell : ℝ := min (1 / 2 : ℝ) ((c / (8 * (G + 1))) ^ 2)
  let etaGeom : ℝ := c * ell / 4
  let Tmass : ℝ := max Th 1
  have hratioPos : 0 < p.a / p.b := div_pos ha hb
  have hcPos : 0 < c := Real.rpow_pos_of_pos hratioPos _
  have hG1 : 0 < G + 1 := by linarith
  have hellPos : 0 < ell := by
    dsimp [ell]; exact lt_min (by norm_num) (by positivity)
  have hetaGeom : 0 < etaGeom := by dsimp [etaGeom]; positivity
  have hTmass : 0 < Tmass := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let Mass : ℝ → ℝ := fun t => intervalDomainM.integral (u t)
  have hMassCont : ContinuousOn Mass (Set.Ioi (0 : ℝ)) := by
    intro s hs
    change 0 < s at hs
    have hsol := huv.classical (s + 1) (by linarith)
    exact (ShenWork.Paper2.IntervalDomainM.mass_hasDerivAt
      hsol hs (by linarith)).continuousAt.continuousWithinAt
  have hSmallSup : ∀ s, Tmass ≤ s → Mass s < etaGeom →
      intervalDomainM.supNorm (u s) < c / 2 := by
    intro s hTs hMass
    have hsPos : 0 < s := lt_of_lt_of_le hTmass hTs
    have hsol := huv.classical (s + 1) (by linarith)
    have hsMem : s ∈ Set.Ioo (0 : ℝ) (s + 1) := ⟨hsPos, by linarith⟩
    have hcont : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
      ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol hsMem
    have hnonneg : ∀ x, 0 ≤ intervalDomainLift (u s) x := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · rw [intervalDomainLift, dif_pos hx]
        exact (hsol.u_pos' hsMem.1 hsMem.2).le
      · simp [intervalDomainLift, hx]
    have hsupEq : intervalDomainM.supNorm (u s) =
        sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      supNorm_eq_sSup_lift_image (fun q => (hsol.u_pos' hsMem.1 hsMem.2).le)
    by_contra hnot
    have hsupGe : c / 2 ≤ sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
      rw [← hsupEq]; exact le_of_not_gt hnot
    have hholLift : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
        |intervalDomainLift (u s) x - intervalDomainLift (u s) y| ≤
          G * |x - y| ^ ((1:ℝ)/2) := by
      intro x hx y hy
      have := hhol s (le_trans (le_max_left _ _) hTs) ⟨x, hx⟩ ⟨y, hy⟩
      simpa [intervalDomainLift, hx, hy] using this
    have hgeom := interval_holder_mass_lower_of_sSup_ge_half
      hcPos hG hcont hnonneg hholLift hsupGe
    have : etaGeom ≤ Mass s := by simpa [etaGeom, ell, Mass] using hgeom
    linarith
  have hMassDeriv : ∀ s, Tmass ≤ s → Mass s < etaGeom →
      ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt Mass d s := by
    intro s hsT hSmall
    have hs : 0 < s := lt_of_lt_of_le hTmass hsT
    have hsol := huv.classical (s + 1) (by linarith)
    exact intervalDomainM_mass_hasDerivAt_nonneg_of_supNorm_lt_half_capacity
      p ha hb hsol ⟨hs, by linarith⟩ (by simpa [c] using hSmallSup s hsT hSmall)
  have hlower := lower_bound_of_hasDerivAt_nonneg_below_threshold
    (M := Mass) (a := Tmass) (threshold := etaGeom) hTmass hMassCont hMassDeriv
  have hsolMass := huv.classical (Tmass + 1) (by linarith)
  have hMassPos : 0 < Mass Tmass :=
    ShenWork.Paper2.IntervalDomainM.mass_pos hsolMass ⟨hTmass, by linarith⟩
  refine ⟨Tmass, min (Mass Tmass) etaGeom, hTmass, lt_min hMassPos hetaGeom,
    fun t ht => hlower t ht⟩

/-- Reaction integral in the logistic mass-balance form. -/
theorem intervalDomainM_reaction_integral_eq
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomainM.integral
        (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) =
      p.a * intervalDomainM.integral (u t) -
        p.b * intervalDomainM.integral (fun x => (u t x) ^ (1 + p.α)) := by
  have hUcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol ht
  have hUpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) y :=
    fun y hy => ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsol ht y hy
  have hU_int : IntervalIntegrable
      (fun y => p.a * intervalDomainLift (u t) y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)]; exact hUcont.const_mul p.a
  have hHcont : ContinuousOn
      (fun y => intervalDomainLift (fun x => (u t x) ^ (1 + p.α)) y) (Set.Icc (0:ℝ) 1) := by
    have hbase : ContinuousOn (fun y => intervalDomainLift (u t) y ^ (1 + p.α))
        (Set.Icc (0:ℝ) 1) :=
      hUcont.rpow_const (p := 1 + p.α) (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))
    refine hbase.congr ?_
    intro y hy
    simp [intervalDomainLift, hy]
  have hH_int : IntervalIntegrable
      (fun y => p.b * intervalDomainLift (fun x => (u t x) ^ (1 + p.α)) y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)]
    exact hHcont.const_mul p.b
  have hkey : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) y =
        p.a * intervalDomainLift (u t) y -
          p.b * intervalDomainLift (fun x => (u t x) ^ (1 + p.α)) y := by
    intro y hy
    have hpos := hUpos y hy
    have e1 : intervalDomainLift (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) y
        = u t ⟨y, hy⟩ * (p.a - p.b * (u t ⟨y, hy⟩) ^ p.α) := by
      simp [intervalDomainLift, hy]
    have e2 : intervalDomainLift (u t) y = u t ⟨y, hy⟩ := by simp [intervalDomainLift, hy]
    have e3 : intervalDomainLift (fun x => (u t x) ^ (1 + p.α)) y
        = (u t ⟨y, hy⟩) ^ (1 + p.α) := by simp [intervalDomainLift, hy]
    rw [e1, e2, e3]
    have hpos' : 0 < u t ⟨y, hy⟩ := by rw [← e2]; exact hpos
    have hmul2 : (u t ⟨y, hy⟩) ^ (1 + p.α) = u t ⟨y, hy⟩ * (u t ⟨y, hy⟩) ^ p.α := by
      rw [Real.rpow_add hpos', Real.rpow_one]
    rw [hmul2]; ring
  change intervalDomainIntegral _ =
    p.a * intervalDomainIntegral (u t) -
      p.b * intervalDomainIntegral (fun x => (u t x) ^ (1 + p.α))
  unfold intervalDomainIntegral
  calc (∫ y in (0:ℝ)..1,
        intervalDomainLift (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) y)
      = ∫ y in (0:ℝ)..1, (p.a * intervalDomainLift (u t) y -
          p.b * intervalDomainLift (fun x => (u t x) ^ (1 + p.α)) y) :=
        intervalIntegral.integral_congr
          (fun y hy => hkey y (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at hy))
    _ = p.a * (∫ y in (0:ℝ)..1, intervalDomainLift (u t) y) -
          p.b * (∫ y in (0:ℝ)..1,
            intervalDomainLift (fun x => (u t x) ^ (1 + p.α)) y) := by
        rw [intervalIntegral.integral_sub hU_int hH_int,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-! ## Hölder reaction coercivity + mass convergence -/

/-- Hölder-`1/2` reaction coercivity: a mass gap below the carrying capacity
forces a uniformly positive logistic reaction integral.  Identical to the
Lipschitz statement except the modulus is Hölder-`1/2`, which the faithful
`u^m` orbit supplies. -/
theorem intervalDomainM_logisticReaction_coercive_of_mass_gap_holder
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {eta d G : ℝ} (heta : 0 < eta) (hd : 0 < d)
    (hdc : d < (positiveEquilibrium p ⟨ha, hb⟩).1) (hG : 0 ≤ G) :
    ∃ eps > 0, ∃ q > 0,
      ∀ f : C(intervalDomainPoint, ℝ),
        (∀ x, 0 ≤ f x) →
        (∀ x, f x ≤ (positiveEquilibrium p ⟨ha, hb⟩).1 + eps) →
        eta ≤ intervalDomain.integral f →
        intervalDomain.integral f ≤ (positiveEquilibrium p ⟨ha, hb⟩).1 - d →
        (∀ x y, |f x - f y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2)) →
        q ≤ intervalDomain.integral
          (fun x => intervalDomainLogisticReaction p (f x)) := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  by_contra hcoercive
  push_neg at hcoercive
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have heps_pos : ∀ n, 0 < eps n := by intro n; positivity
  let f : ℕ → C(intervalDomainPoint, ℝ) := fun n =>
    Classical.choose (hcoercive (eps n) (heps_pos n) (eps n) (heps_pos n))
  have hf_spec (n : ℕ) :
      (∀ x, 0 ≤ f n x) ∧
      (∀ x, f n x ≤ c + eps n) ∧
      eta ≤ intervalDomain.integral (f n) ∧
      intervalDomain.integral (f n) ≤ c - d ∧
      (∀ x y, |f n x - f n y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2)) ∧
      intervalDomain.integral
          (fun x => intervalDomainLogisticReaction p (f n x)) < eps n := by
    simpa [f, c] using
      Classical.choose_spec (hcoercive (eps n) (heps_pos n) (eps n) (heps_pos n))
  have heps_le_one (n : ℕ) : eps n ≤ 1 := by
    dsimp [eps]
    rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hf_abs : ∀ n x, |f n x| ≤ c + 1 := by
    intro n x
    rw [abs_of_nonneg ((hf_spec n).1 x)]
    exact le_trans ((hf_spec n).2.1 x)
      (by simpa [add_comm] using add_le_add_left (heps_le_one n) c)
  obtain ⟨g, φ, hφ, hfg⟩ :=
    intervalDomain_exists_uniform_convergent_subseq_of_holder f
      (by linarith : (0 : ℝ) ≤ c + 1) hG (by norm_num : (0 : ℝ) < 1 / 2)
      hf_abs (fun n => (hf_spec n).2.2.2.2.1)
  have heps_zero : Tendsto eps atTop (𝓝 0) := by
    simpa [eps, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have heps_subseq_zero : Tendsto (fun n => eps (φ n)) atTop (𝓝 0) :=
    heps_zero.comp hφ.tendsto_atTop
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hfg.tendsto_at x)
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).1 x)
  have hg_le_c : ∀ x, g x ≤ c := by
    intro x
    have hsum : Tendsto (fun n => c + eps (φ n)) atTop (𝓝 c) := by
      simpa using tendsto_const_nhds.add heps_subseq_zero
    exact le_of_tendsto_of_tendsto (hfg.tendsto_at x) hsum
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).2.1 x)
  have hint_f : Tendsto (fun n => intervalDomain.integral (f (φ n))) atTop
      (𝓝 (intervalDomain.integral g)) :=
    intervalDomain_integral_tendsto_of_tendstoUniformly hfg
  have hg_mass_lower : eta ≤ intervalDomain.integral g :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hint_f
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).2.2.1)
  have hg_mass_upper : intervalDomain.integral g ≤ c - d :=
    le_of_tendsto hint_f
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).2.2.2.1)
  have hreaction_uniform : TendstoUniformly
      (fun n x => intervalDomainLogisticReaction p (f (φ n) x))
      (fun x => intervalDomainLogisticReaction p (g x)) atTop := by
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := Set.Icc (0 : ℝ) (c + 1))
    · intro n x
      exact ⟨(hf_spec (φ n)).1 x,
        le_trans ((hf_spec (φ n)).2.1 x)
          (by simpa [add_comm] using add_le_add_left (heps_le_one (φ n)) c)⟩
    · exact fun x => ⟨hg_nonneg x, le_trans (hg_le_c x) (by linarith)⟩
    · exact isCompact_Icc.uniformContinuousOn_of_continuous
        (continuous_intervalDomainLogisticReaction p).continuousOn
    · exact hfg
  have hreaction_int : Tendsto
      (fun n => intervalDomain.integral
        (fun x => intervalDomainLogisticReaction p (f (φ n) x))) atTop
      (𝓝 (intervalDomain.integral
        (fun x => intervalDomainLogisticReaction p (g x)))) := by
    let F : ℕ → C(intervalDomainPoint, ℝ) := fun n =>
      ⟨fun x => intervalDomainLogisticReaction p (f (φ n) x),
        (continuous_intervalDomainLogisticReaction p).comp (f (φ n)).continuous⟩
    let Rg : C(intervalDomainPoint, ℝ) :=
      ⟨fun x => intervalDomainLogisticReaction p (g x),
        (continuous_intervalDomainLogisticReaction p).comp g.continuous⟩
    exact intervalDomain_integral_tendsto_of_tendstoUniformly
      (f := F) (g := Rg) (by simpa [F, Rg] using hreaction_uniform)
  have hreaction_int_nonpos :
      intervalDomain.integral
          (fun x => intervalDomainLogisticReaction p (g x)) ≤ 0 :=
    le_of_tendsto_of_tendsto hreaction_int heps_subseq_zero
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).2.2.2.2.2.le)
  let Rg : C(intervalDomainPoint, ℝ) :=
    ⟨fun x => intervalDomainLogisticReaction p (g x),
      (continuous_intervalDomainLogisticReaction p).comp g.continuous⟩
  have hRg_nonneg : ∀ x, 0 ≤ Rg x := by
    intro x
    have hpow : g x ^ p.α ≤ c ^ p.α :=
      Real.rpow_le_rpow (hg_nonneg x) (hg_le_c x) p.hα.le
    have hfactor : 0 ≤ p.a - p.b * g x ^ p.α := by
      have : p.b * g x ^ p.α ≤ p.b * c ^ p.α :=
        mul_le_mul_of_nonneg_left hpow hb.le
      have hcapacity_zero : p.a - p.b * c ^ p.α = 0 := by
        simpa [c] using positiveEquilibrium_logistic_zero p ⟨ha, hb⟩
      linarith
    exact mul_nonneg (hg_nonneg x) hfactor
  have hRg_zero : ∀ x, Rg x = 0 := by
    intro x
    apply le_antisymm
    · by_contra hx
      have hxpos : 0 < Rg x := lt_of_not_ge hx
      have hint_pos :=
        intervalDomain_integral_pos_of_continuous_nonneg_of_exists_pos
          Rg hRg_nonneg ⟨x, hxpos⟩
      have : intervalDomain.integral Rg ≤ 0 := by
        simpa [Rg] using hreaction_int_nonpos
      exact (not_lt_of_ge this) hint_pos
    · exact hRg_nonneg x
  have hg_zero_or_capacity : ∀ x, g x = 0 ∨ g x = c := by
    intro x
    have hprod : g x * (p.a - p.b * g x ^ p.α) = 0 := by
      simpa [Rg, intervalDomainLogisticReaction] using hRg_zero x
    rcases mul_eq_zero.mp hprod with hx0 | hfactor
    · exact Or.inl hx0
    · right
      have hcapacity_zero : p.a - p.b * c ^ p.α = 0 := by
        simpa [c] using positiveEquilibrium_logistic_zero p ⟨ha, hb⟩
      have hpow_eq : g x ^ p.α = c ^ p.α := by nlinarith
      exact le_antisymm
        ((Real.rpow_le_rpow_iff (hg_nonneg x) hc.le p.hα).mp hpow_eq.le)
        ((Real.rpow_le_rpow_iff hc.le (hg_nonneg x) p.hα).mp hpow_eq.ge)
  have hex_capacity : ∃ x, g x = c := by
    by_contra hnone
    push_neg at hnone
    have hg_zero : ∀ x, g x = 0 := fun x =>
      (hg_zero_or_capacity x).resolve_right (hnone x)
    have hint_zero : intervalDomain.integral g = 0 := by
      rw [show (g : intervalDomainPoint → ℝ) = fun _ => 0 from funext hg_zero]
      exact intervalDomain_integral_const 0
    linarith
  have hex_zero : ∃ x, g x = 0 := by
    by_contra hnone
    push_neg at hnone
    have hg_capacity : ∀ x, g x = c := fun x =>
      (hg_zero_or_capacity x).resolve_left (hnone x)
    have hint_capacity : intervalDomain.integral g = c := by
      rw [show (g : intervalDomainPoint → ℝ) = fun _ => c from funext hg_capacity]
      exact intervalDomain_integral_const c
    linarith
  obtain ⟨xzero, hxzero⟩ := hex_zero
  obtain ⟨xcapacity, hxcapacity⟩ := hex_capacity
  have hg_lift_cont : ContinuousOn (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift g) = g := by
      funext x; simp [intervalDomainLift]
    rw [heq]; exact g.continuous
  have hlift_zero : intervalDomainLift g xzero.1 = 0 := by
    simp [intervalDomainLift, xzero.2, hxzero]
  have hlift_capacity : intervalDomainLift g xcapacity.1 = c := by
    simp [intervalDomainLift, xcapacity.2, hxcapacity]
  have hmid_mem : c / 2 ∈
      Set.Icc (intervalDomainLift g xzero.1) (intervalDomainLift g xcapacity.1) := by
    rw [hlift_zero, hlift_capacity]; constructor <;> linarith
  obtain ⟨ymid, hymid_mem, hymid⟩ :=
    isPreconnected_Icc.intermediate_value xzero.2 xcapacity.2 hg_lift_cont hmid_mem
  let xmid : intervalDomainPoint := ⟨ymid, hymid_mem⟩
  have hxmid : g xmid = c / 2 := by
    simpa [xmid, intervalDomainLift, hymid_mem] using hymid
  rcases hg_zero_or_capacity xmid with hxmid_zero | hxmid_capacity
  · rw [hxmid_zero] at hxmid; linarith
  · rw [hxmid_capacity] at hxmid; linarith

/-- The mass is eventually within `d` below the carrying capacity. -/
theorem intervalDomainM_chiNonpos_eventually_mass_ge_capacity_sub
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {d : ℝ} (hd : 0 < d) (hdc : d < (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∀ᶠ t in atTop,
      (positiveEquilibrium p ⟨ha, hb⟩).1 - d ≤ intervalDomainM.integral (u t) := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  obtain ⟨Th, Mh, G, hTh, _hMh, hG, _hsupH, hhol⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  obtain ⟨Tmass, eta, hTmass, heta, hmass⟩ :=
    intervalDomainM_globalBounded_eventual_mass_pos p ha hb huv
  obtain ⟨eps, heps, q, hq, hcoercive⟩ :=
    intervalDomainM_logisticReaction_coercive_of_mass_gap_holder
      p ha hb heta hd (by simpa [c] using hdc) hG
  obtain ⟨Tmax, hmax⟩ := eventually_atTop.1
    (intervalDomainM_chiNonpos_eventually_supNorm_le_capacity_add p hχ ha hb huv heps)
  let a₀ : ℝ := max 1 (max Th (max Tmass Tmax))
  have ha₀ : 0 < a₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hTh₀ : Th ≤ a₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTmass₀ : Tmass ≤ a₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hTmax₀ : Tmax ≤ a₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  let Mass : ℝ → ℝ := fun t => intervalDomainM.integral (u t)
  have hMassCont : ContinuousOn Mass (Set.Ioi (0 : ℝ)) := by
    intro s hs
    change 0 < s at hs
    have hsol := huv.classical (s + 1) (by linarith)
    exact (ShenWork.Paper2.IntervalDomainM.mass_hasDerivAt
      hsol hs (by linarith)).continuousAt.continuousWithinAt
  have hMassUpper : ∀ t, a₀ ≤ t → Mass t ≤ c + eps := by
    intro t ht
    have htPos : 0 < t := lt_of_lt_of_le ha₀ ht
    have hsol := huv.classical (t + 1) (by linarith)
    have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
    exact (intervalDomainM_classicalSolution_mass_le_supNorm hsol htMem).trans
      (by simpa [c, positiveEquilibrium, one_div] using hmax t (hTmax₀.trans ht))
  have hMassDeriv : ∀ t, a₀ ≤ t → Mass t < c - d →
      ∃ r : ℝ, q ≤ r ∧ HasDerivAt Mass r t := by
    intro t ht hMt
    have htPos : 0 < t := lt_of_lt_of_le ha₀ ht
    have hsol := huv.classical (t + 1) (by linarith)
    have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
    let ft : C(intervalDomainPoint, ℝ) :=
      ⟨u t, ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsol htMem⟩
    have hft_nonneg : ∀ x, 0 ≤ ft x := fun x => (hsol.u_pos' htMem.1 htMem.2).le
    have hft_upper : ∀ x, ft x ≤ c + eps := by
      intro x
      have hpoint : ft x ≤ intervalDomainM.supNorm (u t) :=
        le_trans (le_abs_self (ft x))
          (by
            have := abs_lift_le_supNorm_M hsol htMem x.2
            simpa [ft, intervalDomainLift, x.2] using this)
      exact hpoint.trans (by
        simpa [c, positiveEquilibrium, one_div] using hmax t (hTmax₀.trans ht))
    have hft_hol : ∀ x y, |ft x - ft y| ≤ G * |x.1 - y.1| ^ ((1:ℝ)/2) :=
      fun x y => hhol t (hTh₀.trans ht) x y
    have hreact : q ≤ intervalDomain.integral
        (fun x => intervalDomainLogisticReaction p (ft x)) :=
      hcoercive ft hft_nonneg hft_upper
        (by simpa [Mass, ft] using hmass t (hTmass₀.trans ht))
        (by simpa [Mass, ft] using hMt.le) hft_hol
    let r : ℝ := intervalDomainM.integral (u t) * 0 +
      (p.a * intervalDomainM.integral (u t) -
        p.b * intervalDomainM.integral (fun x => (u t x) ^ (1 + p.α)))
    have hrDeriv : HasDerivAt Mass
        (p.a * intervalDomainM.integral (u t) -
          p.b * intervalDomainM.integral (fun x => (u t x) ^ (1 + p.α))) t :=
      ShenWork.Paper2.IntervalDomainM.mass_logistic_hasDerivAt hsol htMem.1 htMem.2
    have hreactEq : intervalDomain.integral
        (fun x => intervalDomainLogisticReaction p (ft x)) =
        p.a * intervalDomainM.integral (u t) -
          p.b * intervalDomainM.integral (fun x => (u t x) ^ (1 + p.α)) :=
      intervalDomainM_reaction_integral_eq hsol htMem
    exact ⟨_, by rw [← hreactEq]; exact hreact, hrDeriv⟩
  obtain ⟨T, _haT, htail⟩ := eventually_ge_of_hasDerivAt_pos_below_threshold
    (M := Mass) (a := a₀) (threshold := c - d) (q := q) (B := c + eps)
    ha₀ hq hMassCont hMassUpper hMassDeriv
  exact eventually_atTop.2 ⟨T, fun t ht => by simpa [Mass, c] using htail t ht⟩

/-- The mass converges to the carrying capacity. -/
theorem intervalDomainM_chiNonpos_mass_tendsto_capacity
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    Tendsto (fun t => intervalDomainM.integral (u t)) atTop
      (𝓝 (positiveEquilibrium p ⟨ha, hb⟩).1) := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  change Tendsto (fun t => intervalDomainM.integral (u t)) atTop (𝓝 c)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let d : ℝ := min (ε / 2) (c / 2)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hdc : d < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hlower := intervalDomainM_chiNonpos_eventually_mass_ge_capacity_sub
    p hχ ha hb huv hd (by simpa [c] using hdc)
  have hmax := intervalDomainM_chiNonpos_eventually_supNorm_le_capacity_add
    p hχ ha hb huv (by linarith : 0 < ε / 2)
  apply eventually_atTop.1
  filter_upwards [hlower, hmax, eventually_ge_atTop (1 : ℝ)] with t hlow hsup ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsol := huv.classical (t + 1) (by linarith)
  have hmassSup := intervalDomainM_classicalSolution_mass_le_supNorm hsol
    (⟨htPos, by linarith⟩ : t ∈ Set.Ioo (0 : ℝ) (t + 1))
  have hupper : intervalDomainM.integral (u t) ≤ c + ε / 2 :=
    hmassSup.trans (by simpa [c, positiveEquilibrium, one_div] using hsup)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [min_le_left (ε / 2) (c / 2)]

/-! ## Uniform convergence and global attraction -/

/-- Hölder-`1/2` static closeness: mass near capacity plus a supremum bound
force uniform closeness to the equilibrium. -/
theorem intervalDomainM_uniform_close_of_mass_and_upper_of_holder
    {c G ε : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : C(intervalDomainPoint, ℝ),
      (∀ x, 0 ≤ f x) →
      (∀ x, f x ≤ c + δ) →
      c - δ ≤ intervalDomain.integral f →
      (∀ x y, |f x - f y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2)) →
      ∀ x, |f x - c| < ε := by
  let ell : ℝ := min (1 / 2 : ℝ) (((2 * ε) / (8 * (G + 1))) ^ 2)
  let L : ℝ := (2 * ε) * ell / 4
  have hG1 : 0 < G + 1 := by linarith
  have hell : 0 < ell := by
    dsimp [ell]; exact lt_min (by norm_num) (by positivity)
  have hL : 0 < L := by dsimp [L]; positivity
  let δ : ℝ := min (ε / 2) (L / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδL : δ ≤ L / 4 := min_le_right _ _
  refine ⟨δ, hδ, fun f _hf_nonneg hf_upper hmass hhol x => ?_⟩
  rw [abs_lt]
  refine ⟨?_, by linarith [hf_upper x]⟩
  by_contra hnot
  have hfx : f x ≤ c - ε := by linarith
  let deficit : C(intervalDomainPoint, ℝ) :=
    ⟨fun y => c + δ - f y, continuous_const.sub f.continuous⟩
  have hdef_nonneg_sub : ∀ y, 0 ≤ deficit y := fun y => by
    dsimp [deficit]; linarith [hf_upper y]
  have hdef_cont : ContinuousOn (intervalDomainLift deficit) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalDomainM.lift_continuousOn_Icc_of_continuous deficit.continuous
  have hdef_nonneg : ∀ y, 0 ≤ intervalDomainLift deficit y := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · rw [intervalDomainLift, dif_pos hy]; exact hdef_nonneg_sub _
    · simp [intervalDomainLift, hy]
  have hdef_hol : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift deficit y - intervalDomainLift deficit z| ≤
        G * |y - z| ^ ((1 : ℝ) / 2) := by
    intro y hy z hz
    have hd := hhol ⟨y, hy⟩ ⟨z, hz⟩
    have hval : |intervalDomainLift deficit y - intervalDomainLift deficit z|
        = |f ⟨y, hy⟩ - f ⟨z, hz⟩| := by
      simp only [intervalDomainLift, hy, hz, dif_pos, deficit, ContinuousMap.coe_mk]
      rw [abs_sub_comm]
      congr 1; ring
    rw [hval]
    simpa using hd
  have hdef_at_x : ε ≤ intervalDomainLift deficit x.1 := by
    have : intervalDomainLift deficit x.1 = c + δ - f x := by
      simp [deficit, intervalDomainLift, x.2]
    rw [this]; linarith
  have hbdd : BddAbove (intervalDomainLift deficit '' Set.Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hdef_cont).bddAbove
  have hsup : (2 * ε) / 2 ≤
      sSup (intervalDomainLift deficit '' Set.Icc (0 : ℝ) 1) :=
    (by linarith : (2 * ε) / 2 ≤ intervalDomainLift deficit x.1).trans
      (le_csSup hbdd ⟨x.1, x.2, rfl⟩)
  have hgeom := interval_holder_mass_lower_of_sSup_ge_half
    (c := 2 * ε) (G := G) (by positivity) hG hdef_cont hdef_nonneg hdef_hol hsup
  have hgeom' : L ≤ intervalDomain.integral deficit := by
    simpa [L, ell, intervalDomain, intervalDomainIntegral] using hgeom
  have hdefIntegral : intervalDomain.integral deficit =
      c + δ - intervalDomain.integral f := by
    simpa [deficit] using intervalDomain_integral_const_sub (c + δ) f
  have hdefUpper : intervalDomain.integral deficit ≤ 2 * δ := by
    rw [hdefIntegral]; linarith
  linarith

/-- Uniform convergence of the population to the positive equilibrium for the
faithful `u^m` neutral / repulsive regime. -/
theorem intervalDomainM_chiNonpos_uniform_u_converges
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    UniformConvergesInSup intervalDomainM u (positiveEquilibrium p ⟨ha, hb⟩).1 := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  obtain ⟨Thol, Mhol, G, hThol, _hMhol, hG, _hsupHol, hhol⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  have hmasslim := intervalDomainM_chiNonpos_mass_tendsto_capacity p hχ ha hb huv
  unfold UniformConvergesInSup
  change Tendsto (fun t => intervalDomainM.supNorm (fun x => u t x - c)) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hstatic⟩ :=
    intervalDomainM_uniform_close_of_mass_and_upper_of_holder
      hc hG (by linarith : 0 < ε / 2)
  let δ₀ : ℝ := min δ (c / 2)
  have hδ₀ : 0 < δ₀ := lt_min hδ (by linarith)
  have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
  have hmax := intervalDomainM_chiNonpos_eventually_supNorm_le_capacity_add
    p hχ ha hb huv hδ₀
  have hmassClose : ∀ᶠ t in atTop,
      dist (intervalDomainM.integral (u t)) c < δ₀ := by
    have hball := hmasslim.eventually (Metric.ball_mem_nhds c hδ₀)
    simpa [Metric.mem_ball, c] using hball
  apply eventually_atTop.1
  filter_upwards [hmax, hmassClose,
    eventually_ge_atTop (max Thol (1 : ℝ))] with t hmax_t hmass_t ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one ((le_max_right Thol (1 : ℝ)).trans ht)
  have hsol := huv.classical (t + 1) (by linarith)
  have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
  let ft : C(intervalDomainPoint, ℝ) :=
    ⟨u t, ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsol htMem⟩
  have hft_nonneg : ∀ x, 0 ≤ ft x := fun _x => (hsol.u_pos' htMem.1 htMem.2).le
  have hft_upper : ∀ x, ft x ≤ c + δ := by
    intro x
    have hpoint : ft x ≤ intervalDomainM.supNorm (u t) :=
      le_trans (le_abs_self (ft x))
        (by
          have := abs_lift_le_supNorm_M hsol htMem x.2
          simpa [ft, intervalDomainLift, x.2] using this)
    have hsupδ₀ : intervalDomainM.supNorm (u t) ≤ c + δ₀ := by
      simpa [c, positiveEquilibrium, one_div] using hmax_t
    linarith
  have hft_mass : c - δ ≤ intervalDomain.integral ft := by
    rw [Real.dist_eq, abs_lt] at hmass_t
    have : c - δ ≤ intervalDomainM.integral (u t) := by linarith
    simpa [ft] using this
  have hft_hol : ∀ x y, |ft x - ft y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2) :=
    fun x y => hhol t ((le_max_left Thol (1 : ℝ)).trans ht) x y
  have hpointClose : ∀ x, |ft x - c| < ε / 2 :=
    hstatic ft hft_nonneg hft_upper hft_mass hft_hol
  have hsup_le : intervalDomainM.supNorm (fun x => u t x - c) ≤ ε / 2 :=
    intervalDomain_supNorm_le_of_pointwise_abs_le (fun x => (hpointClose x).le)
  have hsup_nonneg : 0 ≤ intervalDomainM.supNorm (fun x => u t x - c) :=
    intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded (fun x => (hpointClose x).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nonneg]
  linarith

/-- **χ₀ ≤ 0 global attraction on the faithful `u^m` equation.**  The positive
logistic equilibrium attracts every bounded global orbit. -/
theorem intervalDomainM_chiNonpos_globallyAsymptoticallyStableNonminimal
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    GloballyAsymptoticallyStableNonminimal intervalDomainM p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  intro u v huv
  exact intervalDomainM_chiNonpos_uniform_u_converges p hχ ha hb huv

#print axioms intervalDomainM_chiNonpos_eventually_supNorm_le_capacity_add
#print axioms intervalDomainM_chiNonpos_mass_tendsto_capacity
#print axioms intervalDomainM_chiNonpos_uniform_u_converges
#print axioms intervalDomainM_chiNonpos_globallyAsymptoticallyStableNonminimal

end

end ShenWork.Paper3
