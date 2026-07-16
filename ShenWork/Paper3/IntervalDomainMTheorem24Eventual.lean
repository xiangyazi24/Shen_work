import ShenWork.Paper3.IntervalDomainMEntropyStrong2Global
import ShenWork.Paper3.IntervalDomainTheorem24Eventual

/-!
# Faithful eventual Theorem 2.4 for the general-`m` equation: assembly layer

The two entropy branches (`chiStrong1`, `chiStrong2`) of the faithful
general-`m` eventual Theorem 2.4 are fully proved
(`IntervalDomainMEntropyStrong1Global` / `IntervalDomainMEntropyStrong2Global`)
with no `p.m = 1` hypothesis.  This file dispatches the four-branch formula
condition: branches one and two are discharged unconditionally; the two
rectangle branches (`chiStrong3`, `chiStrong4`) are exposed as explicit named
frontiers, to be discharged by the general-`m` rectangle log-gap port (see
`DOCTRINE_thm24_fable.md`).  When those two producers are proved, the final
headline is this theorem applied to them.
-/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- Package-free faithful eventual form of Paper 3 Theorem 2.4 for the
general-`m` equation, from the two (not yet discharged) rectangle-branch
producers.  Branches one and two are unconditional; no `p.m = 1` hypothesis
appears anywhere. -/
theorem intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula_of_rectangle_frontiers
    (p : CM2Params)
    (hstrong3 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        1 ≤ p.m → 1 ≤ p.γ →
        p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ) →
        p.χ₀ < chiStrong3Formula p
          (unitIntervalNormalizedResolverGradientConstant p)
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 →
        EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
          intervalDomainMSectorialStabilityNorms
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hstrong4 :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        1 ≤ p.m → 1 ≤ p.β → 1 ≤ p.γ →
        p.α + 1 ≥ p.m + 2 * p.γ →
        p.χ₀ < chiStrong4Formula p
          (unitIntervalNormalizedResolverGradientConstant p)
          (positiveEquilibrium p ⟨ha, hb⟩).1 →
        EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
          intervalDomainMSectorialStabilityNorms
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    Theorem_2_4_EventualGlobalStabilityFormula intervalDomainM p
      intervalDomainMSectorialStabilityNorms
      (unitIntervalNormalizedResolverGradientConstant p) := by
  intro ha0 hb0 hβ0 hα0 hγ0 ha hb
  dsimp
  intro hcond
  rcases hcond with hcond | hcond | hcond | hcond
  · exact
      intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong1
        p ha hb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  · exact
      intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong2
        p ha hb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2.1
          hcond.2.2.2.2
  · exact hstrong3 ha hb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  · exact hstrong4 ha hb hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2.1
      hcond.2.2.2.2

#print axioms
  intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula_of_rectangle_frontiers

end

end ShenWork.Paper3
