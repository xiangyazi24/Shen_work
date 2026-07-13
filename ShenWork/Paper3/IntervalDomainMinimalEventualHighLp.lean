import ShenWork.Paper3.IntervalDomainMinimalUniformBootstrap
import ShenWork.Paper3.IntervalDomainEventualConvergenceUpgrade

/-! # Uniform eventual high-power bound in the minimal model -/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

namespace ShenWork.Paper3

noncomputable section

/-- The minimal critical threshold produces a power strictly above `γ` and a
positive orbit-independent eventual bound at that power. -/
theorem exists_minimal_eventual_high_lp_power_bound
    (p : CM2Params) {uStar : ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiBeta p) (huStar : 0 < uStar) :
    ∃ P C : ℝ, max 1 p.γ < P ∧ 0 < C ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomain p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomain u uStar →
        ∀ᶠ t : ℝ in atTop,
          intervalDomain.integral (fun x => (u t x) ^ P) ≤ C := by
  obtain ⟨p0, C0, hp0, hC0, hseedEventual⟩ :=
    exists_minimal_eventual_lp_power_bound
      p hm ha0 hb0 hbeta hchi hthreshold huStar
  let P : ℝ := p0 + p.γ
  have hp0one : 1 < p0 := lt_of_le_of_lt (le_max_left _ _) hp0
  have hp0P : p0 ≤ P := by dsimp [P]; linarith [p.hγ]
  have hP : max 1 p.γ < P := by
    apply max_lt
    · dsimp [P]
      linarith [p.hγ]
    · dsimp [P]
      linarith [hp0one]
  obtain ⟨D, hdamp⟩ := exists_uniform_critical_bootstrap_damping
    p hm hbeta hp0 hp0P
  let C : ℝ := max D 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right D 0]
  refine ⟨P, C, hP, hC, ?_⟩
  intro u v huv hmass
  have hseedEv := hseedEventual u v huv hmass
  rcases eventually_atTop.1 hseedEv with ⟨threshold, hthresholdSeed⟩
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
  have hseedShift : ∀ s, 0 < s →
      intervalDomainM.integral (fun x => (us s x) ^ p0) ≤ C0 := by
    intro s hs
    have horig : threshold ≤ s + tau := by linarith
    simpa [us, intervalDomainM, intervalDomain] using
      hthresholdSeed (s + tau) horig
  have hdampShift : ∀ s, 0 < s →
      (1 / P) * deriv (fun r => intervalDomainLpEnergy P us r) s +
        intervalDomainLpEnergy P us s ≤ max D 0 := by
    intro s hs
    exact (hdamp us vs hshiftGlobalM hseedShift s hs).trans
      (le_max_left D 0)
  have hPpos : 0 < P := lt_trans zero_lt_one
    (lt_of_le_of_lt (le_max_left _ _) hP)
  have hderiv : ∀ s, 0 < s →
      HasDerivAt (fun r => intervalDomainLpEnergy P us r)
        (deriv (fun r => intervalDomainLpEnergy P us r) s) s := by
    intro s hs
    let H : ℝ := s + 1
    have hH : 0 < H := by dsimp [H]; linarith
    have hsH : s < H := by dsimp [H]; linarith
    exact lpEnergy_hasDerivAt_of_solution
      (q := P) (hshiftGlobalM.classical hH) hs hsH
  have henergyEv := eventually_le_add_one_of_linear_damping
    hPpos hderiv hdampShift
  have hpowerShift : ∀ᶠ s : ℝ in atTop,
      intervalDomain.integral (fun x => (us s x) ^ P) ≤ C := by
    filter_upwards [henergyEv, eventually_gt_atTop (0 : ℝ)] with s hs hspos
    let H : ℝ := s + 1
    have hH : 0 < H := by dsimp [H]; linarith
    have hsH : s < H := by dsimp [H]; linarith
    have heq : intervalDomainLpEnergy P us s =
        ∫ x in (0 : ℝ)..1, intervalDomainLift (us s) x ^ P :=
      lpEnergy_eq_lift_power_of_solution
        (q := P) (hshiftGlobalM.classical hH) hspos hsH
    have hdomain : intervalDomain.integral (fun x => (us s x) ^ P) =
        intervalDomainLpEnergy P us s := by
      rw [heq]
      exact intervalDomain_integral_rpow_eq_lift_integral
    simpa [C, hdomain] using hs
  rcases eventually_atTop.1 hpowerShift with ⟨shiftThreshold, hshiftThreshold⟩
  apply eventually_atTop.2
  refine ⟨shiftThreshold + tau, ?_⟩
  intro t ht
  let s : ℝ := t - tau
  have hs : shiftThreshold ≤ s := by dsimp [s]; linarith
  have hbound := hshiftThreshold s hs
  have htime : s + tau = t := by dsimp [s]; ring
  simpa [us, htime] using hbound

#print axioms exists_minimal_eventual_high_lp_power_bound

end

end ShenWork.Paper3
