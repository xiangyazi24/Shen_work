import ShenWork.Paper2.IntervalDomainTheorem12
import ShenWork.Paper2.IntervalDomainMCriticalGlobalLinfBound

/-!
# Positive-sensitivity critical branch of Paper 2 Theorem 1.2

This assembly removes the last `hcriticalGlobalBound` frontier from the
positive-`chi0` critical branch.  Local existence, continuation, and the
finite critical seed remain the standard upstream inputs; the global bound is
the horizon-independent faithful Moser/restart producer.
-/

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

theorem Theorem_1_2_intervalDomain_positive_critical_branch
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) (hchiPos : 0 < p.χ₀)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hcriticalBootstrap :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) :
    0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
    p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
            InitialTrace intervalDomain u₀ u ∧
            IsPaper2Bounded intervalDomain u :=
  ShenWork.Paper2.IntervalDomainTheorem12.Theorem_1_2_intervalDomain_critical_branch_of_corollary21_and_proposition25
    p hCor21 hProp25 hlocal hglobalExtension hcriticalBootstrap
    (criticalGlobalBoundFrontier_positive_intervalDomain p hguard hchiPos)

#print axioms Theorem_1_2_intervalDomain_positive_critical_branch

end ShenWork.Paper2.IntervalDomainM

end
