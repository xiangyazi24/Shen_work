import ShenWork.Paper3.IntervalDomainMEntropyStrong2Global
import ShenWork.Paper3.IntervalDomainMRectangleGlobal
import ShenWork.Paper3.IntervalDomainTheorem24Eventual

/-!
# Faithful eventual Theorem 2.4 for the general-`m` equation: assembly layer

All four branches of the faithful general-`m` eventual Theorem 2.4 are proved
with no `p.m = 1` hypothesis:

* branches one and two (`chiStrong1`, `chiStrong2`): the §7 entropy Lyapunov
  route (`IntervalDomainMEntropyStrong1Global` / `…Strong2Global`);
* branches three and four (`chiStrong3`, `chiStrong4`): the rectangle
  log-gap route (`IntervalDomainMRectangleGlobal`), for strictly attractive
  sensitivity `χ₀ > 0`.

The only residual is the neutral / repulsive case `χ₀ ≤ 0` of the two rectangle
branches, whose faithful general-`m` proof needs the mass-floor + max-decay
chain rebuilt for the `u^m` flux (a separate scoped frontier).  It enters the
final headline as the single hypothesis `hchiNonpos`.
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


/-- **Faithful eventual Theorem 2.4 for the general-`m` interval equation.**
All four strong-logistic branches on the faithful `u^m`-flux domain, with NO
`p.m = 1` hypothesis.  The single remaining input `hchiNonpos` supplies
qualitative global attraction in the neutral / repulsive sub-case `χ₀ ≤ 0` of
the two rectangle branches (a scoped general-`m` frontier); the entropy
branches and the strictly attractive `χ₀ > 0` rectangle branches are
unconditional. -/
theorem intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula
    (p : CM2Params)
    (hchiNonpos : ∀ (ha : 0 < p.a) (hb : 0 < p.b), p.χ₀ ≤ 0 →
      GloballyAsymptoticallyStableNonminimal intervalDomainM p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    Theorem_2_4_EventualGlobalStabilityFormula intervalDomainM p
      intervalDomainMSectorialStabilityNorms
      (unitIntervalNormalizedResolverGradientConstant p) := by
  refine intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula_of_rectangle_frontiers
    p ?_ ?_
  · intro ha hb hm hγ hrel hχ
    exact intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong3
      p hm ha hb hγ hrel hχ (hchiNonpos ha hb)
  · intro ha hb hm hβ hγ hrel hχ
    exact intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong4
      p hm ha hb hβ hγ hrel hχ (hchiNonpos ha hb)

#print axioms intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula

end

end ShenWork.Paper3
