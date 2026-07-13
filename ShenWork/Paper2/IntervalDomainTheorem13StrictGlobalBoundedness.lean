import ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness
import ShenWork.Paper2.IntervalDomainMCriticalGlobalLpBootstrap

/-!
# Horizon-independent bounds for the strict branches of Theorem 1.3

The finite-horizon energy estimates now expose parameter-only damping
constants.  Applying the same estimate on the slice `(0,t+1)` therefore gives
one autonomous inequality on the whole positive time axis.  Its late-time
bound is joined to the finite initial window and then fed to the faithful
general-`m` restarted endpoint.
-/

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13StrictGlobalBoundedness

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMRestartedLpLinfGeneral
open ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer
open ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness

/-- A fixed autonomous damping inequality plus a finite initial-window bound
gives one power bound for every positive time. -/
theorem lp_power_bounded_global_of_linear_damping_and_initial_window
    {p : CM2Params} {P D : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (hP : 1 < P)
    (hdamp : ∀ t, 0 < t →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ D)
    (hearly : LpPowerBoundedBefore intervalDomainM P 2 u) :
    ∃ C, ∀ t, 0 < t →
      intervalDomainM.integral (fun x => (u t x) ^ P) ≤ C := by
  obtain ⟨Clate, hlate⟩ :=
    lp_power_bounded_global_after_one_of_linear_damping hglobal hP hdamp
  obtain ⟨Cearly, hearlyBound⟩ := hearly
  refine ⟨max Cearly Clate, ?_⟩
  intro t ht0
  by_cases ht2 : t < 2
  · exact (hearlyBound t ht0 ht2).trans (le_max_left _ _)
  · have ht1 : 1 ≤ t := by linarith
    exact (hlate t ht1).trans (le_max_right _ _)

/-- Strict alternative (i) has a horizon-independent global supremum bound. -/
theorem boundedGlobal_strict_case_i_positive_chi
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hb : 0 < p.b) (hchi : 0 < p.χ₀)
    (hgap : p.m + p.γ - 1 < p.α) :
    IsPaper2Bounded intervalDomainM u := by
  let P : ℝ := strictEndpointExponent p
  let Q : ℝ := P / p.m
  have hP2 : 2 < P := strictEndpointExponent_gt_two p
  have hP : 1 < P := one_lt_two.trans hP2
  have hmP : p.m < P := strictEndpointExponent_gt_m p
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (lt_div_iff₀ p.hm).2 (by simpa using hmP)
  have hmQ : p.m * Q = P := by
    dsimp [Q]
    field_simp [p.hm.ne']
  have hdamp : ∀ t, 0 < t →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ strongCaseIDampingConstant p P := by
    intro t ht0
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    exact (strong_case_i_lp_energy_damping
      (hglobal.classical hT) hb hchi.le hP2 hgap).2 t ht0 htT
  have hearly : LpPowerBoundedBefore intervalDomainM P 2 u :=
    strong_case_i_lp_power_bounded_before hu₀
      (hglobal.classical (by norm_num)) htrace hb hchi.le hP2 hgap
  obtain ⟨C, hpower⟩ :=
    lp_power_bounded_global_of_linear_damping_and_initial_window
      hglobal hP hdamp hearly
  exact boundedGlobal_of_lp_restarted_affine_general hglobal hP hQ hmQ
    (strictEndpointExponent_ge_gamma p) hpower

/-- Strict alternative (ii) has a horizon-independent global supremum bound. -/
theorem boundedGlobal_strict_case_ii
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hb : 0 < p.b) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hgap : 2 * p.m + p.γ - 2 < p.α) :
    IsPaper2Bounded intervalDomainM u := by
  let P : ℝ := strictEndpointExponent p
  let Q : ℝ := P / p.m
  have hP2 : 2 < P := strictEndpointExponent_gt_two p
  have hP : 1 < P := one_lt_two.trans hP2
  have hmP : p.m < P := strictEndpointExponent_gt_m p
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (lt_div_iff₀ p.hm).2 (by simpa using hmP)
  have hmQ : p.m * Q = P := by
    dsimp [Q]
    field_simp [p.hm.ne']
  have hdamp : ∀ t, 0 < t →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ strongCaseIIDampingConstant p P := by
    intro t ht0
    let T : ℝ := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t < T := by dsimp [T]; linarith
    exact (strong_case_ii_lp_energy_damping
      (hglobal.classical hT) hb hP2 hbeta hgap).2 t ht0 htT
  have hearly : LpPowerBoundedBefore intervalDomainM P 2 u :=
    strong_case_ii_lp_power_bounded_before hu₀
      (hglobal.classical (by norm_num)) htrace hb hP2 hbeta hgap
  obtain ⟨C, hpower⟩ :=
    lp_power_bounded_global_of_linear_damping_and_initial_window
      hglobal hP hdamp hearly
  exact boundedGlobal_of_lp_restarted_affine_general hglobal hP hQ hmQ
    (strictEndpointExponent_ge_gamma p) hpower

#print axioms lp_power_bounded_global_of_linear_damping_and_initial_window
#print axioms boundedGlobal_strict_case_i_positive_chi
#print axioms boundedGlobal_strict_case_ii

end ShenWork.Paper2.IntervalDomainTheorem13StrictGlobalBoundedness

end
