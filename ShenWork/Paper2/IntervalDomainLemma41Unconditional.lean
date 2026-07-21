/-
  ShenWork/Paper2/IntervalDomainLemma41Unconditional.lean

  Unconditional Paper 2 Lemma 4.1 on the concrete interval domain.

  This file discharges the `IntervalDomainClassicalSolutionPositiveInterpolation`
  frontier carried by `Lemma_4_1_intervalDomain_of_solution_interpolation_frontier`
  using the already-proved positive C² Agmon interpolation inequality
  `unitIntervalPositiveAgmonInterpolation`, together with the closed-domain
  positivity and C²-regularity supplied by every Paper 2 classical solution.

  No new analytic estimate is introduced: this is a pure wiring of proved
  pieces (Class A).
-/
import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalAgmonInterpolation

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLemma41Unconditional

/-- The solution-slice positive interpolation frontier holds unconditionally on
the interval: every classical solution slice is positive on the closed domain
and `C²`, so the proved positive-`C²` Agmon interpolation inequality applies. -/
theorem intervalDomain_ClassicalSolutionPositiveInterpolation (p : CM2Params) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      p := by
  intro T u v hsol eps heps q hq
  rcases unitIntervalPositiveAgmonInterpolation q hq eps heps with
    ⟨Ceps, hCeps_pos, hCeps⟩
  refine ⟨Ceps, hCeps_pos, ?_⟩
  intro t ht0 htT
  exact hCeps (u t)
    (fun x => hsol.u_pos' ht0 htT (x := x))
    ((hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1)

/-- **Paper 2 Lemma 4.1 for the interval domain, unconditional.** -/
theorem Lemma_4_1_intervalDomain (p : CM2Params) :
    Lemma_4_1 intervalDomain p :=
  IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_solution_interpolation_frontier
    p (intervalDomain_ClassicalSolutionPositiveInterpolation p)

#print axioms Lemma_4_1_intervalDomain

end ShenWork.Paper2.IntervalDomainLemma41Unconditional

end
