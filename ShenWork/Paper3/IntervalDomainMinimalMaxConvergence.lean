import ShenWork.Paper3.IntervalDomainStrictMaxDissipation
import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassConvergence
import ShenWork.Paper3.EventualGlobalStability

/-!
# Maximum convergence in the repulsive minimal model

The physical mass fixes the neutral constant mode.  When the spatial maximum
stays a fixed amount above that mass, the quantitative resolver gap gives a
uniform strictly negative maximum slope.  The compact-slice Dini theorem then
forces entry below every such upper threshold.
-/

namespace ShenWork.Paper3

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.MaxPrincipleAtoms ShenWork.MinPersistenceAtoms

noncomputable section

/-- The spatial maximum is nonincreasing on positive times in the minimal
model with nonpositive sensitivity. -/
theorem intervalDomain_minimal_supNorm_antitone_positiveTimes
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ ≤ 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm (u s) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have hmono := ShenWork.Paper2.Lemma31Closure.lemma31_zero
    p hχ ha hb hH hsol
  exact hmono s ⟨hs, by linarith⟩ t ⟨ht, by linarith⟩ hst

/-- If a terminal maximum is still above `uStar + d`, the entire preceding
window has a uniform negative relative rate. -/
theorem intervalDomain_minimal_chiNeg_supNorm_decay_if_above_mass_add
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ < 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {uStar d t : ℝ} (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (ht : 1 ≤ t)
    (habove : uStar + d < intervalDomain.supNorm (u t)) :
    intervalDomain.supNorm (u t) ≤
      intervalDomain.supNorm (u 1) *
        Real.exp
          ((-intervalDomainMinimalMaxDissipationConstant p uStar d
              (intervalDomain.supNorm (u 1)) /
                intervalDomain.supNorm (u 1)) * (t - 1)) := by
  let B : ℝ := intervalDomain.supNorm (u 1)
  let C : ℝ := intervalDomainMinimalMaxDissipationConstant p uStar d B
  let K : ℝ := -C / B
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hterminalB : intervalDomain.supNorm (u t) ≤ B := by
    dsimp [B]
    exact intervalDomain_minimal_supNorm_antitone_positiveTimes
      p ha hb hχ.le huv (by norm_num) ht
  have hBlevel : uStar + d ≤ B :=
    habove.le.trans hterminalB
  have hBpos : 0 < B := lt_of_lt_of_le (by linarith) hBlevel
  have hCpos : 0 < C := by
    dsimp [C]
    exact intervalDomainMinimalMaxDissipationConstant_pos
      p hχ huStar hd hBlevel
  have hKneg : K < 0 := by
    dsimp [K]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hCpos) hBpos
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  have hsol := huv.classical H hH
  have hwindow : Set.Icc (1 : ℝ) t ⊆ Set.Ioo (0 : ℝ) H := by
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
    have hsmem : s ∈ Set.Ioo (0 : ℝ) H := hwindow hs
    have hcontU : ContinuousOn (intervalDomainLift (u s))
        (Set.Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 s hsmem).1.1).continuousOn
    have hbdd : BddAbove
        (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
    have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
      intro y
      have huy : u s y = intervalDomainLift (u s) y.1 := by
        rw [intervalDomainLift,
          dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from y.2),
          Subtype.coe_eta]
      have huxs : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
        rw [intervalDomainLift, dif_pos hxs]
      rw [huy, huxs, hargmax]
      exact le_csSup hbdd (Set.mem_image_of_mem _ y.2)
    have hsupeq : intervalDomain.supNorm (u s) =
        sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      supNorm_eq_sSup_lift_image
        (fun q => (hsol.u_pos' hsmem.1 hsmem.2).le)
    have hterminal : intervalDomain.supNorm (u t) ≤
        intervalDomain.supNorm (u s) :=
      intervalDomain_minimal_supNorm_antitone_positiveTimes
        p ha hb hχ.le huv hsmem.1 hs.2
    have hlevel : uStar + d ≤ intervalDomainLift (u s) xs := by
      rw [hargmax, ← hsupeq]
      exact habove.le.trans hterminal
    have hsB : intervalDomain.supNorm (u s) ≤ B := by
      dsimp [B]
      exact intervalDomain_minimal_supNorm_antitone_positiveTimes
        p ha hb hχ.le huv (by norm_num) hs.1
    have hpointB : intervalDomainLift (u s) xs ≤ B := by
      rw [hargmax, ← hsupeq]
      exact hsB
    have hslope := intervalDomain_minimal_argmax_uniform_strict_slope
      ha hb hχ hsol hsmem.1 hsmem.2 huStar hd
      (by simpa [intervalDomain] using hmass s hsmem.1)
      hmax hlevel hpointB
    have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩ =
        deriv (fun r => intervalDomainLift (u r) xs) s := by
      show deriv (fun r => u r ⟨xs, hxs⟩) s =
        deriv (fun r => intervalDomainLift (u r) xs) s
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos hxs]
    rw [htd] at hslope
    have hKB : K * B = -C := by
      dsimp [K]
      exact div_mul_cancel₀ (-C) hBpos.ne'
    have hmul := mul_le_mul_of_nonpos_left hsB hKneg.le
    rw [hKB, hsupeq] at hmul
    exact hslope.trans hmul
  have hgron := intervalDomain_supNorm_gronwall_on_window
    hsol hwindow hmaxSlope (t₁ := (1 : ℝ)) (t₂ := t)
      ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simpa [B, C, K] using hgron

/-- Every bounded positive orbit in the strictly repulsive minimal model
eventually enters every upper neighbourhood of its physical mean. -/
theorem intervalDomain_minimal_chiNeg_eventually_supNorm_le_mass_add
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ < 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {uStar d : ℝ} (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    ∀ᶠ t in atTop,
      intervalDomain.supNorm (u t) ≤ uStar + d := by
  let B : ℝ := intervalDomain.supNorm (u 1)
  have hH2 : 0 < (2 : ℝ) := by norm_num
  have hsol2 := huv.classical 2 hH2
  have hmass1 : intervalDomain.integral (u 1) = uStar := by
    simpa [intervalDomain] using hmass 1 (by norm_num)
  have hmass_le := intervalDomain_classicalSolution_mass_le_supNorm hsol2
    (⟨by norm_num, by norm_num⟩ : (1 : ℝ) ∈ Set.Ioo 0 2)
  have hBmass : uStar ≤ B := by simpa [B, hmass1] using hmass_le
  have hBpos : 0 < B := lt_of_lt_of_le huStar hBmass
  have hBlevel : uStar + d ≤ max B (uStar + d) := le_max_right _ _
  let C₀ : ℝ := intervalDomainMinimalMaxDissipationConstant
    p uStar d (max B (uStar + d))
  let K₀ : ℝ := -C₀ / max B (uStar + d)
  have hB₀pos : 0 < max B (uStar + d) :=
    lt_of_lt_of_le hBpos (le_max_left _ _)
  have hC₀pos : 0 < C₀ := by
    dsimp [C₀]
    exact intervalDomainMinimalMaxDissipationConstant_pos
      p hχ huStar hd hBlevel
  have hK₀neg : K₀ < 0 := by
    dsimp [K₀]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hC₀pos) hB₀pos
  have hlin : Tendsto (fun t : ℝ => K₀ * (t - 1)) atTop atBot := by
    have hbase : Tendsto (fun t : ℝ => K₀ * t + (-K₀)) atTop atBot :=
      tendsto_atBot_add_const_right _ (-K₀)
        (tendsto_id.const_mul_atTop_of_neg hK₀neg)
    convert hbase using 1
    funext t
    ring
  have hexp : Tendsto (fun t : ℝ => Real.exp (K₀ * (t - 1)))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hlin
  have hdecay : Tendsto
      (fun t : ℝ => B * Real.exp (K₀ * (t - 1))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  have hthreshold : 0 < uStar + d := by linarith
  have hevlt : ∀ᶠ t in atTop,
      B * Real.exp (K₀ * (t - 1)) < uStar + d :=
    (tendsto_order.1 hdecay).2 _ hthreshold
  filter_upwards [hevlt, eventually_ge_atTop (1 : ℝ)] with t hright ht
  by_contra hnot
  have habove : uStar + d < intervalDomain.supNorm (u t) :=
    lt_of_not_ge hnot
  have hBt : intervalDomain.supNorm (u t) ≤ B := by
    dsimp [B]
    exact intervalDomain_minimal_supNorm_antitone_positiveTimes
      p ha hb hχ.le huv (by norm_num) ht
  have hBeq : max B (uStar + d) = B := max_eq_left (habove.le.trans hBt)
  have hbound := intervalDomain_minimal_chiNeg_supNorm_decay_if_above_mass_add
    p ha hb hχ huv huStar hd hmass ht habove
  have : intervalDomain.supNorm (u t) ≤
      B * Real.exp (K₀ * (t - 1)) := by
    simpa [B, C₀, K₀, hBeq] using hbound
  linarith

#print axioms intervalDomain_minimal_supNorm_antitone_positiveTimes
#print axioms intervalDomain_minimal_chiNeg_supNorm_decay_if_above_mass_add
#print axioms intervalDomain_minimal_chiNeg_eventually_supNorm_le_mass_add

end

end ShenWork.Paper3
