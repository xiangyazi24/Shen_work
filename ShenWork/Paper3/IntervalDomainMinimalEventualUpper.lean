import ShenWork.Paper3.IntervalDomainMinimalEventualHighLp
import ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer

/-! # Uniform eventual supremum bound in the minimal model -/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainRestartedLpLinf
open ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer

namespace ShenWork.Paper3

noncomputable section

/-- Under the critical small-sensitivity condition, a physical-mass minimal
orbit eventually satisfies one supremum bound chosen before the orbit. -/
theorem exists_minimal_eventual_uniform_upper_bound
    (p : CM2Params) {uStar : ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiBeta p) (huStar : 0 < uStar) :
    ∃ uBar > 0,
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomain p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomain u uStar →
        ∀ᶠ t : ℝ in atTop, intervalDomain.supNorm (u t) ≤ uBar := by
  obtain ⟨P, C, hP, hC, hpowerEventual⟩ :=
    exists_minimal_eventual_high_lp_power_bound
      p hm ha0 hb0 hbeta hchi hthreshold huStar
  have hPone : 1 < P := lt_of_le_of_lt (le_max_left _ _) hP
  have hγP : p.γ ≤ P :=
    (le_max_right (1 : ℝ) p.γ).trans (le_of_lt hP)
  let w : ℝ := 1 / 2
  have hw : 0 < w := by norm_num [w]
  have hw1 : w ≤ 1 := by norm_num [w]
  let R : ℝ :=
    (fullHeatShortConstant * w ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
        (C + 1) ^ (1 / P) +
      |p.χ₀| *
        (conjugateLpLinftyConstant P *
          ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
          (w ^ (1 - conjugateLpLinftyTheta P) /
            (1 - conjugateLpLinftyTheta P))) +
      p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
        (w ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P)))
  let uBar : ℝ := max 1 R
  have huBar : 0 < uBar :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 R)
  refine ⟨uBar, huBar, ?_⟩
  intro u v huv hmass
  have hpowerEv := hpowerEventual u v huv hmass
  rcases eventually_atTop.1 hpowerEv with ⟨threshold, hthreshold⟩
  let tau : ℝ := max threshold 1
  have htau : 0 < tau :=
    lt_of_lt_of_le zero_lt_one (le_max_right threshold 1)
  have hthresholdTau : threshold ≤ tau := le_max_left _ _
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau) x
  have hshiftGlobal : IsPaper2GlobalClassicalSolution intervalDomain p us vs := by
    simpa [us, vs] using
      intervalDomain_globalClassicalSolution_timeShift huv.1 htau
  have hshiftGlobalM : IsPaper2GlobalClassicalSolution intervalDomainM p us vs :=
    isPaper2GlobalClassicalSolution_intervalDomainM_of_m_eq_one
      p hm hshiftGlobal
  have hpowerShift : ∀ s, 0 < s →
      intervalDomainM.integral (fun z => (us s z) ^ P) ≤ C := by
    intro s hs
    have horig : threshold ≤ s + tau := by linarith
    simpa [us, intervalDomainM, intervalDomain] using
      hthreshold (s + tau) horig
  have hshiftSup : ∀ s, 2 * w ≤ s → intervalDomainSupNorm (us s) ≤ R := by
    intro s hs
    let T : ℝ := s + 1
    let a : ℝ := s - w
    have hT : 0 < T := by dsimp [T]; linarith [hw]
    have ha : 0 < a := by dsimp [a]; linarith [hw]
    have hahT : a + w < T := by dsimp [a, T]; linarith
    have hsol : IsPaper2ClassicalSolution intervalDomainM p T us vs :=
      hshiftGlobalM.classical hT
    have hpowerT : ∀ r, 0 < r → r < T →
        intervalDomainM.integral (fun z => (us r z) ^ P) ≤ C :=
      fun r hr _ => hpowerShift r hr
    unfold intervalDomainSupNorm
    apply csSup_le
    · let x₀ : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
      exact ⟨|us s x₀|, ⟨x₀, rfl⟩⟩
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    change |us s x| ≤ R
    have hs0 : 0 < s := lt_of_lt_of_le (by linarith [hw]) hs
    have hsT : s < T := by dsimp [T]; linarith
    rw [abs_of_pos (u_pos hsol hs0 hsT x)]
    have hslice := solutionSlice_le_of_restart_affine_lp
      hsol ha hw.le hahT hm hPone hγP hpowerT hw le_rfl hw1 x.property
    have heq : intervalDomainLift (us (a + w)) x.1 = us s x := by
      dsimp [a]
      simp [intervalDomainLift]
    rw [← heq]
    simpa [R] using hslice
  apply eventually_atTop.2
  refine ⟨2 * w + tau, ?_⟩
  intro t ht
  let s : ℝ := t - tau
  have hs : 2 * w ≤ s := by dsimp [s]; linarith
  have hbound := hshiftSup s hs
  have htime : s + tau = t := by dsimp [s]; ring
  change intervalDomainSupNorm (u t) ≤ uBar
  calc
    intervalDomainSupNorm (u t) = intervalDomainSupNorm (us s) := by
      simp [us, htime]
    _ ≤ R := hbound
    _ ≤ uBar := le_max_right 1 R

#print axioms exists_minimal_eventual_uniform_upper_bound

end

end ShenWork.Paper3
