import ShenWork.Paper3.IntervalDomainMContactSmallCeilingProducer
import ShenWork.Paper2.IntervalDomainMMass

/-!
# Corrected faithful Paper 3 Theorem 2.1(1)

The proof-supported reaction guard has two branches.  The positive-logistic
branch uses the faithful minimum-growth argument.  In the minimal branch the
positive conserved mass contradicts a uniformly small contact slice.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM

theorem intervalDomainM_mass_eq_time_one_of_minimal
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {t : ℝ} (ht : 0 < t) :
    intervalDomain.integral (u t) = intervalDomain.integral (u 1) := by
  let H : ℝ := max t 1 + 1
  have hH : 0 < H := by
    dsimp [H]
    linarith [le_max_right t (1 : ℝ)]
  have htH : t < H := by
    dsimp [H]
    linarith [le_max_left t (1 : ℝ)]
  have h1H : (1 : ℝ) < H := by
    dsimp [H]
    linarith [le_max_right t (1 : ℝ)]
  have hsol := huv.classical H hH
  let mass : ℝ → ℝ := fun s => intervalDomain.integral (u s)
  have hdiff : DifferentiableOn ℝ mass (Set.Ioo (0 : ℝ) H) := by
    intro s hs
    exact (mass_hasDerivAt hsol hs.1 hs.2).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) H, deriv mass s = 0 := by
    intro s hs
    simpa [mass, ha, hb] using mass_derivative_eq_logistic hsol hs.1 hs.2
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    hdiff hderiv ⟨ht, htH⟩ ⟨one_pos, h1H⟩

/-- Minimal faithful branch of corrected Part 1.  No initial-trace interface is
needed: the mass at positive time one is the invariant. -/
theorem intervalDomainM_minimal_part1
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hm : 1 ≤ p.m) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
        ∃ deltaU > 0,
          deltaU ≤ liminfInfValue intervalDomainM u ∧
          p.ν / p.μ * (liminfInfValue intervalDomainM u) ^ p.γ ≤
            liminfInfValue intervalDomainM v := by
  intro u v huv
  let uStar : ℝ := intervalDomain.integral (u 1)
  have huStar : 0 < uStar := by
    have hsol := huv.classical 2 (by norm_num)
    simpa [uStar] using mass_pos hsol
      (show (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 by norm_num)
  have hcontact := intervalDomainM_contactSmallCeiling p hm huv
  obtain ⟨T, hT, delta, hdelta, hsmall⟩ :=
    hcontact (uStar / 2) (half_pos huStar)
  have hmin : ∀ t, T ≤ t → delta < intervalDomainSpatialMin u t := by
    intro t ht
    by_contra hnot
    push Not at hnot
    have hslice := hsmall t ht hnot
    have htpos : 0 < t := lt_of_lt_of_le hT ht
    let H : ℝ := t + 1
    have hH : 0 < H := by dsimp [H]; linarith
    have hsol := huv.classical H hH
    have hcont := solution_lift_continuousOn_Icc hsol
      (show t ∈ Set.Ioo (0 : ℝ) H by
        dsimp [H]
        constructor <;> linarith)
    have hint : IntervalIntegrable (intervalDomainLift (u t)) volume 0 1 :=
      hcont.intervalIntegrable_of_Icc (by norm_num)
    have hmassLe : intervalDomain.integral (u t) ≤ uStar / 2 := by
      unfold intervalDomain intervalDomainIntegral
      have hmono : (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y) ≤
          ∫ _y in (0 : ℝ)..1, uStar / 2 :=
        intervalIntegral.integral_mono_on (by norm_num) hint
          intervalIntegrable_const (fun y hy =>
            (le_abs_self _).trans (hslice y))
      simpa using hmono
    have hmassEq : intervalDomain.integral (u t) = uStar := by
      simpa [uStar] using
        intervalDomainM_mass_eq_time_one_of_minimal p ha hb huv htpos
    linarith
  have hpoint : ∀ᶠ t in atTop,
      ∀ x : intervalDomainPoint, delta ≤ u t x := by
    let Hmin := intervalDomainM_generalM_compactMinFamily huv
    filter_upwards [eventually_ge_atTop T] with t ht x
    have htpos : 0 < t := lt_of_lt_of_le hT ht
    have hzle := Hmin.z_le t x.1 x.2
    have hmin_le : intervalDomainSpatialMin u t ≤ u t x := by
      simpa [intervalDomainActualLinearDanskinF, htpos, intervalDomainLift]
        using hzle
    exact (hmin t ht).le.trans hmin_le
  have huLowerLegacy : EventuallyLowerBound intervalDomain u delta :=
    intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
      hdelta hpoint
  have huLower : EventuallyLowerBound intervalDomainM u delta := by
    simpa [EventuallyLowerBound, intervalDomain, intervalDomainM] using
      huLowerLegacy
  have huLiminf : delta ≤ liminfInfValue intervalDomainM u :=
    liminf_ge_of_eventuallyLowerBound
      (intervalDomainM_infValue_isCoboundedUnder huv) huLower
  have huLiminfPos : 0 < liminfInfValue intervalDomainM u :=
    hdelta.trans_le huLiminf
  have hvLiminf := intervalDomainM_liminf_v_ge_of_u_liminf_lower
    huv huLiminfPos (le_refl _)
  exact ⟨delta, hdelta, huLiminf, hvLiminf⟩

/-- Unconditional, non-vacuous, paper-faithful correction of Paper 3,
Theorem 2.1(1), on the faithful physical unit interval. -/
theorem Theorem_2_1_part1_corrected_intervalDomainM
    (p : CM2Params) :
    Theorem_2_1_part1_corrected intervalDomainM p := by
  intro hguard hm u v huv
  rcases hguard with hminimal | hlogistic
  · exact intervalDomainM_minimal_part1 p hminimal.1 hminimal.2 hm u v huv
  · exact intervalDomainM_positiveLogistic_part1_of_contactSmallCeiling
      p hlogistic.1 hlogistic.2 hm
      (fun u v huv => intervalDomainM_contactSmallCeiling p hm huv)
      u v huv

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_minimal_part1
#print axioms ShenWork.Paper3.Theorem_2_1_part1_corrected_intervalDomainM
