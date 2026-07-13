import ShenWork.Paper2.IntervalDomainMMass
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform
import ShenWork.Paper3.IntervalDomainNegativeSensitivityMaxDecay
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit
import ShenWork.Paper3.IntervalDomainGlobalTailLipschitz

/-!
# A concrete tail mass floor for bounded interval orbits

Uniform positive-time spatial Lipschitz control prevents a profile with a
fixed positive maximum from having arbitrarily small mass.  Combined with the
exact logistic mass identity, this gives a positive orbitwise tail mass floor:
below the geometric mass threshold the entire profile lies below half the
carrying capacity, so the mass derivative is strictly positive.

No persistence, compactness, stability, or convergence package is assumed.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- A scalar trajectory cannot cross downward below a threshold on which its
derivative is nonnegative.  This is the lower-barrier dual of the threshold
persistence lemma used for maximum estimates. -/
theorem lower_bound_of_hasDerivAt_nonneg_below_threshold
    {M : ℝ → ℝ} {a threshold : ℝ} (ha : 0 < a)
    (hcont : ContinuousOn M (Set.Ioi (0 : ℝ)))
    (hderiv : ∀ t, a ≤ t → M t < threshold →
      ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt M d t) :
    ∀ t, a ≤ t → min (M a) threshold ≤ M t := by
  intro t hat
  by_contra hnot
  have hMt : M t < min (M a) threshold := lt_of_not_ge hnot
  have hMtThreshold : M t < threshold := hMt.trans_le (min_le_right _ _)
  have hatStrict : a < t := by
    rcases lt_or_eq_of_le hat with h | h
    · exact h
    · subst t
      linarith [hMt, min_le_left (M a) threshold]
  let tau : ℝ := t - a
  have htau : 0 < tau := by dsimp [tau]; linarith
  let N : ℝ → ℝ := fun r => -M (a + r)
  have hNcont : ContinuousOn N (Set.Ioo (0 : ℝ) (tau + 1)) := by
    have hshift : ContinuousOn (fun r : ℝ => a + r)
        (Set.Ioo (0 : ℝ) (tau + 1)) := Continuous.continuousOn (by fun_prop)
    exact hcont.neg.comp hshift (fun r hr => by
      show 0 < a + r
      linarith [ha, hr.1])
  have hNderiv : ∀ r ∈ Set.Ioo (0 : ℝ) (tau + 1),
      -threshold < N r →
      ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt N d r := by
    intro r hr hNr
    have hMr : M (a + r) < threshold := by dsimp [N] at hNr; linarith
    obtain ⟨d, hd, hMd⟩ := hderiv (a + r) (by linarith [hr.1]) hMr
    have hshift : HasDerivAt (fun q : ℝ => a + q) 1 r :=
      (hasDerivAt_id r).const_add a
    have hcomp := (hMd.comp r hshift).neg
    refine ⟨-d, by linarith, ?_⟩
    simpa [N, Function.comp_def] using hcomp
  have hN_tau : -threshold < N tau := by
    have htEq : a + tau = t := by dsimp [tau]; ring
    dsimp [N]
    rw [htEq]
    linarith
  have hAbove := ShenWork.Paper2.threshold_persists_below_of_hasDerivAt_nonpos
    (M := N) (threshold := -threshold) (T := tau + 1)
    htau (by linarith) hNcont hNderiv hN_tau
  have hNcontIcc : ContinuousOn N (Set.Icc (0 : ℝ) tau) := by
    have hshift : ContinuousOn (fun r : ℝ => a + r) (Set.Icc (0 : ℝ) tau) :=
      Continuous.continuousOn (by fun_prop)
    exact hcont.neg.comp hshift (fun r hr => by
      show 0 < a + r
      linarith [ha, hr.1])
  have hdiff : DifferentiableOn ℝ N (interior (Set.Icc (0 : ℝ) tau)) := by
    intro r hr
    rw [interior_Icc] at hr
    have hrIoc : r ∈ Set.Ioc (0 : ℝ) tau := ⟨hr.1, hr.2.le⟩
    obtain ⟨d, _, hd⟩ := hNderiv r
      ⟨hr.1, lt_trans hr.2 (by linarith)⟩ (hAbove r hrIoc)
    exact hd.differentiableAt.differentiableWithinAt
  have hderNonpos : ∀ r ∈ interior (Set.Icc (0 : ℝ) tau), deriv N r ≤ 0 := by
    intro r hr
    rw [interior_Icc] at hr
    have hrIoc : r ∈ Set.Ioc (0 : ℝ) tau := ⟨hr.1, hr.2.le⟩
    obtain ⟨d, hd, hNd⟩ := hNderiv r
      ⟨hr.1, lt_trans hr.2 (by linarith)⟩ (hAbove r hrIoc)
    rw [hNd.deriv]
    exact hd
  have hanti : AntitoneOn N (Set.Icc (0 : ℝ) tau) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) hNcontIcc hdiff hderNonpos
  have hcompare := hanti (Set.left_mem_Icc.mpr htau.le)
    (Set.right_mem_Icc.mpr htau.le) htau.le
  have hMa : M a ≤ M t := by
    have htEq : a + tau = t := by dsimp [tau]; ring
    dsimp [N] at hcompare
    rw [htEq] at hcompare
    simp only [add_zero] at hcompare
    linarith
  linarith [hMt, min_le_left (M a) threshold]

/-- A nonnegative `G`-Lipschitz profile on `[0,1]` whose maximum is at least
`c/2` has an explicit positive mass.  A one-sided interval at a maximizer
avoids any boundary loss. -/
theorem interval_lipschitz_mass_lower_of_sSup_ge_half
    {f : ℝ → ℝ} {c G : ℝ} (hc : 0 < c) (hG : 0 ≤ G)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hnonneg : ∀ x, 0 ≤ f x)
    (hlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |f x - f y| ≤ G * |x - y|)
    (hsup : c / 2 ≤ sSup (f '' Set.Icc (0 : ℝ) 1)) :
    c * min (1 / 2 : ℝ) (c / (8 * (G + 1))) / 4 ≤
      ∫ x in (0 : ℝ)..1, f x := by
  let ell : ℝ := min (1 / 2 : ℝ) (c / (8 * (G + 1)))
  have hG1 : 0 < G + 1 := by linarith
  have hellPos : 0 < ell := by
    dsimp [ell]
    exact lt_min (by norm_num) (div_pos hc (by positivity))
  have hellHalf : ell ≤ 1 / 2 := by dsimp [ell]; exact min_le_left _ _
  have hellFrac : ell ≤ c / (8 * (G + 1)) := by
    dsimp [ell]
    exact min_le_right _ _
  have hGell : G * ell ≤ c / 8 := by
    calc
      G * ell ≤ G * (c / (8 * (G + 1))) :=
        mul_le_mul_of_nonneg_left hellFrac hG
      _ ≤ (G + 1) * (c / (8 * (G + 1))) := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (div_nonneg hc.le (by positivity))
      _ = c / 8 := by
        field_simp [ne_of_gt hG1]
  obtain ⟨x₀, hx₀, hxmax, _⟩ :=
    isCompact_Icc.exists_sSup_image_eq_and_ge
      (Set.nonempty_Icc.mpr (by norm_num)) hcont
  have hxvalue : c / 2 ≤ f x₀ := by rwa [← hxmax]
  have hfint : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
  have hnonnegAe : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f :=
    Filter.Eventually.of_forall hnonneg
  by_cases hxleft : x₀ ≤ 1 / 2
  · have hright : x₀ + ell ≤ 1 := by linarith
    have hsub : Set.Icc x₀ (x₀ + ell) ⊆ Set.Icc (0 : ℝ) 1 := fun y hy =>
      ⟨le_trans hx₀.1 hy.1, le_trans hy.2 hright⟩
    have hpoint : ∀ y ∈ Set.Icc x₀ (x₀ + ell), c / 4 ≤ f y := by
      intro y hy
      have hdist : |x₀ - y| ≤ ell := by
        rw [abs_of_nonpos (sub_nonpos.mpr hy.1)]
        linarith [hy.2]
      have hdrop : f x₀ - f y ≤ G * ell :=
        (le_abs_self (f x₀ - f y)).trans
          ((hlip x₀ hx₀ y (hsub hy)).trans
            (mul_le_mul_of_nonneg_left hdist hG))
      linarith
    have hmonoSub :
        ∫ y in x₀..(x₀ + ell), c / 4 ≤
          ∫ y in x₀..(x₀ + ell), f y :=
      intervalIntegral.integral_mono_on (by linarith [hellPos])
        intervalIntegrable_const
        ((hcont.mono hsub).intervalIntegrable_of_Icc (by linarith [hellPos])) hpoint
    have hsubFull : (∫ y in x₀..(x₀ + ell), f y) ≤
        ∫ y in (0 : ℝ)..1, f y :=
      intervalIntegral.integral_mono_interval hx₀.1 (by linarith [hellPos])
        hright hnonnegAe hfint
    have hconst : (∫ _y in x₀..(x₀ + ell), c / 4) = c * ell / 4 := by
      simp [intervalIntegral.integral_const]
      ring
    rw [hconst] at hmonoSub
    exact hmonoSub.trans hsubFull
  · have hxright : 1 / 2 < x₀ := lt_of_not_ge hxleft
    have hleft : 0 ≤ x₀ - ell := by linarith
    have hsub : Set.Icc (x₀ - ell) x₀ ⊆ Set.Icc (0 : ℝ) 1 := fun y hy =>
      ⟨le_trans hleft hy.1, le_trans hy.2 hx₀.2⟩
    have hpoint : ∀ y ∈ Set.Icc (x₀ - ell) x₀, c / 4 ≤ f y := by
      intro y hy
      have hdist : |x₀ - y| ≤ ell := by
        rw [abs_of_nonneg (sub_nonneg.mpr hy.2)]
        linarith [hy.1]
      have hdrop : f x₀ - f y ≤ G * ell :=
        (le_abs_self (f x₀ - f y)).trans
          ((hlip x₀ hx₀ y (hsub hy)).trans
            (mul_le_mul_of_nonneg_left hdist hG))
      linarith
    have hmonoSub :
        ∫ y in (x₀ - ell)..x₀, c / 4 ≤
          ∫ y in (x₀ - ell)..x₀, f y :=
      intervalIntegral.integral_mono_on (by linarith [hellPos])
        intervalIntegrable_const
        ((hcont.mono hsub).intervalIntegrable_of_Icc (by linarith [hellPos])) hpoint
    have hsubFull : (∫ y in (x₀ - ell)..x₀, f y) ≤
        ∫ y in (0 : ℝ)..1, f y :=
      intervalIntegral.integral_mono_interval hleft (by linarith [hellPos])
        hx₀.2 hnonnegAe hfint
    have hconst : (∫ _y in (x₀ - ell)..x₀, c / 4) = c * ell / 4 := by
      simp [intervalIntegral.integral_const]
      ring
    rw [hconst] at hmonoSub
    exact hmonoSub.trans hsubFull

/-- When the whole positive slice lies below half the logistic carrying
capacity, the exact mass derivative is nonnegative (in fact strictly
positive).  The faithful `intervalDomainM` mass identity is used through the
explicit `m = 1` conversion. -/
theorem intervalDomain_mass_hasDerivAt_nonneg_of_supNorm_lt_half_capacity
    (p : CM2Params) (hm : p.m = 1) (ha : 0 < p.a) (hb : 0 < p.b)
    {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hsup : intervalDomain.supNorm (u t) <
      ((p.a / p.b) ^ (1 / p.α)) / 2) :
    ∃ d : ℝ, 0 ≤ d ∧
      HasDerivAt (fun s => intervalDomain.integral (u s)) d t := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let rate : ℝ := p.a - p.b * ((c / 2) ^ p.α)
  have hratioPos : 0 < p.a / p.b := div_pos ha hb
  have hcPos : 0 < c := Real.rpow_pos_of_pos hratioPos _
  have hcpow : c ^ p.α = p.a / p.b := by
    rw [show c = (p.a / p.b) ^ (1 / p.α) by rfl,
      ← Real.rpow_mul hratioPos.le,
      one_div_mul_cancel (ne_of_gt p.hα), Real.rpow_one]
  have hhalfNonneg : 0 ≤ c / 2 := by positivity
  have hhalfPow : (c / 2) ^ p.α < c ^ p.α :=
    Real.rpow_lt_rpow hhalfNonneg (by linarith) p.hα
  have hmul : p.b * ((c / 2) ^ p.α) < p.a := by
    have hdiv : (c / 2) ^ p.α < p.a / p.b := by rwa [← hcpow]
    have := (lt_div_iff₀ hb).mp hdiv
    simpa [mul_comm] using this
  have hrate : 0 < rate := by dsimp [rate]; linarith
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let d : ℝ := p.a * intervalDomain.integral (u t) -
    p.b * intervalDomain.integral (fun x => (u t x) ^ (1 + p.α))
  have hd : HasDerivAt (fun s => intervalDomain.integral (u s)) d t := by
    simpa [d] using
      ShenWork.Paper2.IntervalDomainM.mass_logistic_hasDerivAt
        hsolM ht.1 ht.2
  let f : ℝ → ℝ := intervalDomainLift (u t)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    exact ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsolM ht
  have hfpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < f y := by
    intro y hy
    dsimp [f]
    exact ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsolM ht y hy
  have hfle : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y < c / 2 := by
    intro y hy
    have habs := abs_lift_le_supNorm hsol ht hy
    have hpos := hfpos y hy
    exact lt_of_le_of_lt (le_trans (le_abs_self (f y)) habs)
      (by simpa [c] using hsup)
  have hpowcont : ContinuousOn (fun y => f y ^ p.α)
      (Set.Icc (0 : ℝ) 1) :=
    hfcont.rpow_const (fun y hy => Or.inl (ne_of_gt (hfpos y hy)))
  have hreactcont : ContinuousOn
      (fun y => f y * (p.a - p.b * f y ^ p.α))
      (Set.Icc (0 : ℝ) 1) := by fun_prop
  have hleftInt : IntervalIntegrable (fun y => rate * f y) volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hfcont.const_mul rate
  have hrightInt : IntervalIntegrable
      (fun y => f y * (p.a - p.b * f y ^ p.α)) volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hreactcont
  have hpoint : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      rate * f y ≤ f y * (p.a - p.b * f y ^ p.α) := by
    intro y hy
    have hpow : f y ^ p.α ≤ (c / 2) ^ p.α :=
      Real.rpow_le_rpow (hfpos y hy).le (hfle y hy).le p.hα.le
    have hcoef : rate ≤ p.a - p.b * f y ^ p.α := by
      dsimp [rate]
      nlinarith [mul_le_mul_of_nonneg_left hpow hb.le]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hcoef (hfpos y hy).le
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hleftInt hrightInt hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hreactCongr :
      intervalDomain.integral
          (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) =
        ∫ y in (0 : ℝ)..1, f y * (p.a - p.b * f y ^ p.α) := by
    unfold intervalDomain intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
    simp [f, intervalDomainLift, hyIcc]
  have hreaction := intervalDomain_reaction_integral_eq hsol ht
  have hdEq : d = ∫ y in (0 : ℝ)..1,
      f y * (p.a - p.b * f y ^ p.α) := by
    rw [← hreactCongr, hreaction]
  have hmassPos : 0 < intervalDomain.integral (u t) := by
    exact ShenWork.Paper2.IntervalDomainM.mass_pos hsolM ht
  refine ⟨d, ?_, hd⟩
  rw [hdEq]
  have hleft : 0 ≤ rate * ∫ x in (0 : ℝ)..1, f x := by
    simpa [f] using (mul_pos hrate hmassPos).le
  exact hleft.trans hmono

/-- A uniform tail Lipschitz estimate produces an orbitwise positive mass
floor.  This theorem exposes the exact geometric input so that the concrete
tail-smoothing producer can be composed without any abstract compactness
package. -/
theorem intervalDomain_eventual_mass_pos_of_eventual_lipschitz
    (p : CM2Params) (hm : p.m = 1) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {T G : ℝ} (hG : 0 ≤ G)
    (hlip : ∀ t, T ≤ t →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (u t) x - intervalDomainLift (u t) y| ≤
          G * |x - y|) :
    ∃ Tmass eta : ℝ, 0 < Tmass ∧ 0 < eta ∧
      ∀ t, Tmass ≤ t → eta ≤ intervalDomain.integral (u t) := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let ell : ℝ := min (1 / 2 : ℝ) (c / (8 * (G + 1)))
  let etaGeom : ℝ := c * ell / 4
  let Tmass : ℝ := max T 1
  have hratioPos : 0 < p.a / p.b := div_pos ha hb
  have hcPos : 0 < c := Real.rpow_pos_of_pos hratioPos _
  have hG1 : 0 < G + 1 := by linarith
  have hellPos : 0 < ell := by
    dsimp [ell]
    exact lt_min (by norm_num) (div_pos hcPos (by positivity))
  have hetaGeom : 0 < etaGeom := by dsimp [etaGeom]; positivity
  have hTmass : 0 < Tmass := by
    dsimp [Tmass]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let Mass : ℝ → ℝ := fun t => intervalDomain.integral (u t)
  have hMassCont : ContinuousOn Mass (Set.Ioi (0 : ℝ)) := by
    intro s hs
    change 0 < s at hs
    have hH : 0 < s + 1 := by linarith [hs]
    have hsol := huv.classical (s + 1) hH
    have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
    exact (ShenWork.Paper2.IntervalDomainM.mass_hasDerivAt
      hsolM hs (by linarith)).continuousAt.continuousWithinAt
  have hSmallSup : ∀ s, Tmass ≤ s → Mass s < etaGeom →
      intervalDomain.supNorm (u s) < c / 2 := by
    intro s hTs hMass
    have hsPos : 0 < s := lt_of_lt_of_le hTmass hTs
    have hH : 0 < s + 1 := by linarith
    have hsol := huv.classical (s + 1) hH
    have hsMem : s ∈ Set.Ioo (0 : ℝ) (s + 1) := ⟨hsPos, by linarith⟩
    have hcont : ContinuousOn (intervalDomainLift (u s))
        (Set.Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 s hsMem).1.1).continuousOn
    have hnonneg : ∀ x, 0 ≤ intervalDomainLift (u s) x := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · rw [intervalDomainLift, dif_pos hx]
        exact (hsol.u_pos' hsMem.1 hsMem.2).le
      · simp [intervalDomainLift, hx]
    have hsupEq : intervalDomain.supNorm (u s) =
        sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
      ShenWork.MaxPrincipleAtoms.supNorm_eq_sSup_lift_image
        (fun q => (hsol.u_pos' hsMem.1 hsMem.2).le)
    by_contra hnot
    have hsupGe : c / 2 ≤
        sSup (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) := by
      rw [← hsupEq]
      exact le_of_not_gt hnot
    have hgeom := interval_lipschitz_mass_lower_of_sSup_ge_half
      hcPos hG hcont hnonneg
      (hlip s (le_trans (le_max_left _ _) hTs)) hsupGe
    have : etaGeom ≤ Mass s := by
      simpa [etaGeom, ell, Mass] using hgeom
    linarith
  have hMassDeriv : ∀ s, Tmass ≤ s → Mass s < etaGeom →
      ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt Mass d s := by
    intro s hsT hSmall
    have hs : 0 < s := lt_of_lt_of_le hTmass hsT
    have hH : 0 < s + 1 := by linarith
    have hsol := huv.classical (s + 1) hH
    exact intervalDomain_mass_hasDerivAt_nonneg_of_supNorm_lt_half_capacity
      p hm ha hb hsol ⟨hs, by linarith⟩
        (by simpa [c] using hSmallSup s hsT hSmall)
  have hlower := lower_bound_of_hasDerivAt_nonneg_below_threshold
    (M := Mass) (a := Tmass) (threshold := etaGeom)
    hTmass hMassCont hMassDeriv
  have hHmass : 0 < Tmass + 1 := by linarith
  have hsolMass := huv.classical (Tmass + 1) hHmass
  have hsolMassM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsolMass
  have hMassPos : 0 < Mass Tmass := by
    dsimp [Mass]
    exact ShenWork.Paper2.IntervalDomainM.mass_pos hsolMassM
      ⟨hTmass, by linarith⟩
  let eta : ℝ := min (Mass Tmass) etaGeom
  have heta : 0 < eta := by dsimp [eta]; exact lt_min hMassPos hetaGeom
  exact ⟨Tmass, eta, hTmass, heta, fun t ht => hlower t ht⟩

/-- Concrete positive tail mass for every bounded global interval orbit in the
positive logistic regime.  The uniform Lipschitz hypothesis of the preceding
theorem is discharged by the proved unit-window restart smoothing estimate. -/
theorem intervalDomain_globalBounded_eventual_mass_pos
    (p : CM2Params) (hm : p.m = 1) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∃ Tmass eta : ℝ, 0 < Tmass ∧ 0 < eta ∧
      ∀ t, Tmass ≤ t → eta ≤ intervalDomain.integral (u t) := by
  rcases intervalDomain_globalBounded_eventual_lipschitz p hm huv with
    ⟨T, G, hG, hlip⟩
  exact intervalDomain_eventual_mass_pos_of_eventual_lipschitz
    p hm ha hb huv hG hlip

#print axioms lower_bound_of_hasDerivAt_nonneg_below_threshold
#print axioms interval_lipschitz_mass_lower_of_sSup_ge_half
#print axioms intervalDomain_mass_hasDerivAt_nonneg_of_supNorm_lt_half_capacity
#print axioms intervalDomain_eventual_mass_pos_of_eventual_lipschitz
#print axioms intervalDomain_globalBounded_eventual_mass_pos

end

end ShenWork.Paper3
