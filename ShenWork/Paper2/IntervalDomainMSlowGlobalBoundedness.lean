import ShenWork.Paper2.IntervalDomainTheorem13StrictGlobalBoundedness

/-!
# Global boundedness in the slow-diffusion branch

The finite-descent exponent is chosen once above `1`, `m`, and `gamma`.
The horizon-independent slow energy inequality then gives one power bound for
all positive times.  The general-`m` affine restart turns that finite-power
bound into the eventual supremum bound required by corrected Theorem 1.2.
-/

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.Paper2.IntervalDomainTheorem13StrictGlobalBoundedness
open ShenWork.Paper2.IntervalDomainMRestartedLpLinfGeneral

/-- A global slow-diffusion solution has one uniform finite-power bound at an
exponent strictly above every exponent needed by the affine restart. -/
theorem exists_high_slow_lp_power_bounded_global
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1) :
    ∃ P : ℝ, max 1 (max p.m p.γ) < P ∧
      ∃ C : ℝ, ∀ t, 0 < t →
        intervalDomainM.integral (fun x => (u t x) ^ P) ≤ C := by
  obtain ⟨steps, P, hPdef, hP⟩ :=
    exists_slow_descent_exponent_above hm1 (max 1 (max p.m p.γ))
  have hPone : 1 < P := lt_of_le_of_lt (le_max_left _ _) hP
  obtain ⟨D, _hD, hdamp⟩ := slow_lp_energy_damping_global
    hguard hu₀ hglobal htrace hbeta hm1 hPdef hPone
  have hearly : LpPowerBoundedBefore intervalDomainM P 2 u :=
    slow_lp_power_bounded_before hguard hu₀
      (hglobal.classical (by norm_num)) htrace hbeta hm1 hPdef hPone
  obtain ⟨C, hpower⟩ :=
    lp_power_bounded_global_of_linear_damping_and_initial_window
      hglobal hPone hdamp hearly
  exact ⟨P, hP, C, hpower⟩

/-- The paper-faithful slow-diffusion global trajectory is eventually
uniformly bounded.  The endpoint uses `Q=P/m`; positivity of `m` and the
chosen inequality `P>m` make this a genuine smoothing exponent. -/
theorem slow_bounded_global
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1) :
    IsPaper2Bounded intervalDomainM u := by
  obtain ⟨P, hP, C, hpower⟩ :=
    exists_high_slow_lp_power_bounded_global
      hguard hu₀ hglobal htrace hbeta hm1
  let Q : ℝ := P / p.m
  have hPone : 1 < P := lt_of_le_of_lt (le_max_left _ _) hP
  have hmP : p.m < P :=
    lt_of_le_of_lt
      ((le_max_left p.m p.γ).trans
        (le_max_right (1 : ℝ) (max p.m p.γ))) hP
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (lt_div_iff₀ p.hm).2 (by simpa using hmP)
  have hmQ : p.m * Q = P := by
    dsimp [Q]
    field_simp [p.hm.ne']
  have hγP : p.γ ≤ P :=
    (le_max_right p.m p.γ).trans
      ((le_max_right (1 : ℝ) (max p.m p.γ)).trans hP.le)
  exact boundedGlobal_of_lp_restarted_affine_general
    hglobal hPone hQ hmQ hγP hpower

#print axioms exists_high_slow_lp_power_bounded_global
#print axioms slow_bounded_global

end ShenWork.Paper2.IntervalDomainM
