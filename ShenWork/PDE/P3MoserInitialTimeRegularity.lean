import ShenWork.PDE.P3MoserEnergyContinuity

/-!
# Initial-time regularity audit for the interval-domain Lp PDE terms

Task 23 asks whether
`IntervalDomainLpPDETermInitialWindowIntegrability` follows from global
classical solution data alone, or whether it is a genuine residual frontier.

## Finding

The current formal API does not produce the componentwise initial-window
integrability from `IsPaper2GlobalClassicalSolution` alone.

The reason is visible in the definitions:

* `IsPaper2ClassicalSolution` in `ShenWork/Paper2/Statements.lean` stores
  positivity, nonnegativity, the PDE equations, and Neumann conditions only under
  hypotheses `0 < t` and `t < T`.
* For the interval domain, `D.classicalRegularity` unfolds to
  `intervalDomainClassicalRegularity` in `ShenWork/PDE/IntervalDomain.lean`.
  Its strongest joint continuity fields are on
  `Set.Ioo 0 T ×ˢ Set.Icc 0 1`: closed in space, but still open in time at
  `0`.
* The already-proved positive-start window theorem in
  `P3MoserEnergyContinuity.lean` therefore applies on `[a,b]` with `0 < a`,
  but intentionally does not cover windows `[0,b]`.

Thus Route A would need an additional closed-time-at-zero regularity theorem for
the three scalar PDE profiles, or an analytic proof that their possible
positive-time singularities are integrable at `0`.  That input is not present in
the current global-classical record.

Route B is more promising for the current architecture: the file
`P3MoserPDECombinedInitialProducer.lean` already routes an initial-window
Moser-derivative residual through the weighted time term and then to the
combined PDE scalar.  This avoids needing componentwise integrability of
diffusion, chemotaxis, and logistic terms separately at `0`.  However, it still
needs an explicit initial-window derivative/weighted-time residual; global
classical data alone does not currently supply it.

The small theorem below records the exact Route-A missing input: if closed-time
continuity of the three scalar PDE profiles on every `[0,b]` is supplied, then
the task residual follows immediately by `ContinuousOn.intervalIntegrable`.
-/

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

set_option linter.style.longLine false
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Closed-time-at-zero continuity package for the three scalar PDE profiles.

This is precisely the extra Route-A regularity missing from the current
`IsPaper2GlobalClassicalSolution` API. -/
def IntervalDomainLpPDETermInitialWindowContinuity
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      ContinuousOn
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        (Set.Icc (0 : ℝ) b) ∧
      ContinuousOn
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        (Set.Icc (0 : ℝ) b) ∧
      ContinuousOn
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        (Set.Icc (0 : ℝ) b)

/-- Route-A bridge: closed-time-at-zero scalar continuity immediately gives the
componentwise initial-window integrability residual. -/
theorem intervalDomain_lpPDETermInitialWindowIntegrability_of_initialWindowContinuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hcont :
      IntervalDomainLpPDETermInitialWindowContinuity params u v T p0) :
    IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0 := by
  intro q hq b hb
  rcases hcont q hq b hb with ⟨hDiff, hChem, hLog⟩
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hb.1]
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hb.1]
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hb.1]

/-- Componentwise initial-window integrability, if supplied, is already enough
for the thinner global-PDE initial-data package used downstream. -/
theorem intervalDomain_globalPDEInitialData_of_atZero_pdeTermInitial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hterms :
      IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0) :
    IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
      params u v T p0 where
  atZero := hzero
  pdeCombinedInitial :=
    intervalDomain_lpPDECombinedInitialWindowIntegrability_of_terms
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hterms

set_option linter.style.longLine true

#print axioms
  intervalDomain_lpPDETermInitialWindowIntegrability_of_initialWindowContinuity
#print axioms
  intervalDomain_globalPDEInitialData_of_atZero_pdeTermInitial

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
