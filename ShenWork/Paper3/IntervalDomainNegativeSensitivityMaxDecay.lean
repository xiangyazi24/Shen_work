import ShenWork.Paper2.IntervalLemma31Closure
import ShenWork.Paper3.Statements

/-!
# Maximum decay for nonpositive sensitivity

This file develops the quantitative maximum-principle input for the faithful
eventual form of Paper 3, Theorem 2.3.  The first result is a windowed
Grönwall estimate for the spatial maximum.  Unlike the monotonicity-only
version used in Paper 2, it retains an arbitrary (possibly negative) rate.

No stability, orbit-convergence, compactness-package, or existence conclusion
is used.
-/

namespace ShenWork.Paper3

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.MaxPrincipleAtoms ShenWork.MinPersistenceAtoms

noncomputable section

/-- A pointwise upper slope `u_t <= K * max u` at every spatial maximizer
integrates to the corresponding Grönwall bound for the maximum on a compact
positive-time window.  The rate `K` is arbitrary; in particular, the theorem
retains strict exponential decay when `K < 0`. -/
theorem intervalDomain_supNorm_gronwall_on_window
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {a b K : ℝ} (hab : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (hmaxSlope : ∀ s ∈ Set.Icc a b, ∀ xs ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u s) xs =
          sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
      deriv (fun r => intervalDomainLift (u r) xs) s ≤
        K * sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1))
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc a b) (ht₂ : t₂ ∈ Set.Icc a b)
    (ht : t₁ ≤ t₂) :
    intervalDomain.supNorm (u t₂) ≤
      intervalDomain.supNorm (u t₁) * Real.exp (K * (t₂ - t₁)) := by
  obtain ⟨_, hTimeReg, _, _, _, hdF6, hSol7⟩ := hsol.regularity
  let F : ℝ → ℝ → ℝ := fun t y => intervalDomainLift (u t) y
  let M : ℝ → ℝ := fun t => intervalDomain.supNorm (u t)
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

/-- If the terminal maximum remains a fixed amount above the logistic carrying
capacity, the whole preceding positive-time window lies above the same level
and hence carries a uniform strictly negative maximum-point rate. -/
theorem intervalDomain_chiNonpos_supNorm_decay_if_above_capacity_add
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {ε t : ℝ} (hε : 0 < ε) (ht : 1 ≤ t)
    (habove : (p.a / p.b) ^ (1 / p.α) + ε <
      intervalDomain.supNorm (u t)) :
    intervalDomain.supNorm (u t) ≤
      intervalDomain.supNorm (u 1) *
        Real.exp ((p.a - p.b *
          (((p.a / p.b) ^ (1 / p.α) + ε) ^ p.α)) * (t - 1)) := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let K : ℝ := p.a - p.b * ((c + ε) ^ p.α)
  let H : ℝ := t + 1
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  have hsol := huv.classical H hH
  have hcAbove : c < intervalDomain.supNorm (u t) := by
    dsimp [c]
    linarith
  have hmono := ShenWork.Paper2.Lemma31Closure.lemma31_above_capacity
    p hχ ha hb hH hsol htpos htH hcAbove
  have hab : Set.Icc (1 : ℝ) t ⊆ Set.Ioo (0 : ℝ) H := by
    intro s hs
    exact ⟨lt_of_lt_of_le (by norm_num) hs.1,
      lt_of_le_of_lt hs.2 htH⟩
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
    have hslope := ShenWork.Paper2.Lemma31Closure.max_point_slope_bound
      hχ hsol hsmem.1 hsmem.2 hmax
    have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩ =
        deriv (fun r => intervalDomainLift (u r) xs) s := by
      show deriv (fun r => u r ⟨xs, hxs⟩) s =
        deriv (fun r => intervalDomainLift (u r) xs) s
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos hxs]
    rw [htd] at hslope
    have hsupeq : intervalDomain.supNorm (u s) =
        sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      supNorm_eq_sSup_lift_image
        (fun q => (hsol.u_pos' hsmem.1 hsmem.2).le)
    have hterminal : intervalDomain.supNorm (u t) ≤
        intervalDomain.supNorm (u s) := by
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
  have hgron := intervalDomain_supNorm_gronwall_on_window
    hsol hab hmaxSlope (t₁ := (1 : ℝ)) (t₂ := t)
      ⟨le_refl _, ht⟩ ⟨ht, le_refl _⟩ ht
  simpa [c, K] using hgron

/-- For nonpositive chemotactic sensitivity, every positive bounded global
orbit eventually lies below any prescribed upper neighbourhood of the
logistic carrying capacity.  This is the first concrete global-attractor
component of Paper 3, Theorem 2.3. -/
theorem intervalDomain_chiNonpos_eventually_supNorm_le_capacity_add
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      intervalDomain.supNorm (u t) ≤
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
    funext t
    ring
  have hexp : Tendsto (fun t : ℝ => Real.exp (K * (t - 1)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hlin
  have hdecay : Tendsto
      (fun t : ℝ => intervalDomain.supNorm (u 1) *
        Real.exp (K * (t - 1))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp)
  have hthreshold : 0 < c + ε := by linarith
  have hevlt : ∀ᶠ t in atTop,
      intervalDomain.supNorm (u 1) * Real.exp (K * (t - 1)) < c + ε :=
    (tendsto_order.1 hdecay).2 _ hthreshold
  filter_upwards [hevlt, eventually_ge_atTop (1 : ℝ)] with t hright ht
  by_contra hnot
  have habove : c + ε < intervalDomain.supNorm (u t) := lt_of_not_ge hnot
  have hbound := intervalDomain_chiNonpos_supNorm_decay_if_above_capacity_add
    p hχ ha hb huv hε ht (by simpa [c] using habove)
  have : intervalDomain.supNorm (u t) ≤
      intervalDomain.supNorm (u 1) * Real.exp (K * (t - 1)) := by
    simpa [K, c] using hbound
  linarith

#print axioms intervalDomain_supNorm_gronwall_on_window
#print axioms intervalDomain_chiNonpos_supNorm_decay_if_above_capacity_add
#print axioms intervalDomain_chiNonpos_eventually_supNorm_le_capacity_add

end

end ShenWork.Paper3
