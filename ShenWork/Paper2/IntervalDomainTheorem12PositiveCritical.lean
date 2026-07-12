import ShenWork.Paper2.IntervalDomainMCriticalGlobalLinfBound

/-!
# Positive-sensitivity critical branch of Paper 2 Theorem 1.2

This assembly uses the signal-weighted finite-power route directly.  The
weighted elliptic estimate supplies the sharp `rho = gamma` bootstrap, the
critical coefficient gap supplies its finite seed, and the semigroup endpoint
stops at one exponent above `max 1 gamma`.  Thus neither the generic
`Corollary_2_1` nor the generic `Proposition_2_5` statement-layer frontier is
needed here.
-/

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

theorem Theorem_1_2_intervalDomain_positive_critical_branch
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) (hchiPos : 0 < p.χ₀)
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
    :
    0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
    p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
            InitialTrace intervalDomain u₀ u ∧
            IsPaper2Bounded intervalDomain u := by
  intro _ha _hb hbeta hm hthreshold u₀ hu₀
  obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ := hlocal u₀ hu₀
  have hboundedBefore : IsPaper2BoundedBefore intervalDomain Tmax u :=
    critical_bounded_before_positive_intervalDomain
      hguard hu₀ hsol htrace hbeta hm hchiPos hthreshold
  have hm_ge : 1 ≤ p.m := by rw [hm]
  have hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v :=
    hglobalExtension u₀ hu₀ Tmax hTmax u v hsol htrace hboundedBefore hm_ge
  have hbounded : IsPaper2Bounded intervalDomain u :=
    critical_bounded_global_positive_intervalDomain
      hguard hu₀ hglobal htrace hbeta hm hchiPos hthreshold
  exact ⟨u, v, hglobal, htrace, hbounded⟩

#print axioms Theorem_1_2_intervalDomain_positive_critical_branch

end ShenWork.Paper2.IntervalDomainM

end
