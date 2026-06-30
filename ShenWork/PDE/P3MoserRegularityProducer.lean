import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.Statements

/-!
# Regularity producer: `IntegratedMoserFirstCrossingRegularity` from classical solutions

This file produces `IntegratedMoserFirstCrossingRegularity intervalDomain u T p0`
from `IsPaper2ClassicalSolution intervalDomain params T u v`.

The four fields of `IntegratedMoserFirstCrossingRegularity` are:

1. `energyContinuous`: `t ↦ ∫₀¹ u(t,x)^p dx` is continuous on `[0,T]`.
   **Status: sorry.**  This is a genuine analytic argument: joint space-time
   continuity of the classical solution (regularity conjunct (9)) plus a
   parametric-integral continuity lemma (e.g.
   `continuous_parametric_intervalIntegral_of_continuous'`) should close it,
   but the exact Mathlib wiring is nontrivial.

2. `initialPowerBound`: `∫₀¹ u(0,x)^p dx ≤ C₀` for some `C₀ ≥ 0`.
   **Status: sorry.**  Needs a bound on the initial trace `u(0,·)` on the
   compact `[0,1]`.  The classical solution interface does not directly
   expose `u(0,·)` regularity (positivity is only for `0 < t`), so a
   separate initial-data assumption is needed.

3. `powerTimeIntegrable`: `t ↦ ∫₀¹ u(t,x)^p dx` is integrable on `[0,T]`.
   Follows from `energyContinuous` via `ContinuousOn.integrableOn_compact`.
   **Status: sorry** (blocked on `energyContinuous`).

4. `gradientTimeIntegrable`: the gradient energy is integrable in time.
   **Status: sorry.**  Similar to (3) but needs gradient-energy continuity,
   which is a harder regularity statement.

The file provides the clean interface with explicit sorry locations.
-/

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-! ### Auxiliary lemmas for the interval domain -/

/-- Pointwise nonnegativity of `u(t,x)` at interior times, extracted from the
classical solution. -/
theorem intervalDomain_u_nonneg_of_classical
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T)
    (x : intervalDomain.Point) :
    0 ≤ u t x :=
  (hsol.u_pos' ht0 htT (x := x)).le

/-- The integral `∫₀¹ u(t,x)^p dx` is well-defined and nonneg for a positive
classical solution at interior times.  This is a consequence of `u > 0` on
`[0,1]` and compactness. -/
theorem intervalDomain_power_integral_nonneg_of_classical
    {params : CM2Params} {T p : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    0 ≤ intervalDomain.integral (fun x => (u t x) ^ p) :=
  intervalDomain_integral_nonneg _
    (fun x => Real.rpow_nonneg
      (intervalDomain_u_nonneg_of_classical hsol ht0 htT x) p)

/-! ### Energy continuity (the hard field) -/

/-- The energy map `t ↦ ∫₀¹ u(t,x)^p dx` is continuous on `[0,T]` for a
classical interval-domain solution.

This is the hardest field of `IntegratedMoserFirstCrossingRegularity`.
The proof strategy is:
- From `intervalDomainClassicalRegularity` conjunct (9), the solution field
  `(t,x) ↦ intervalDomainLift (u t) x` is jointly continuous on
  `Ioo 0 T ×ˢ Icc 0 1`.
- The power map `r ↦ r^p` is continuous for `r > 0`.
- Compose to get joint continuity of `(t,x) ↦ (u(t,x))^p` on the slab.
- Apply a parametric-integral continuity theorem to conclude that
  `t ↦ ∫₀¹ (u(t,x))^p dx` is continuous on `(0,T)`.
- Extending to the closed `[0,T]` requires the initial trace and terminal
  trace to be handled separately.

For now this is left as sorry. -/
theorem intervalDomain_energyContinuous_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) := by
  sorry

/-! ### Initial power bound -/

/-- The initial power integral `∫₀¹ u(0,x)^p dx` is bounded for a classical
solution.

The proof strategy: the classical solution has a continuous (or at least
bounded) initial trace `u(0,·)` on the compact `[0,1]`.  If `u(0,·)` is
bounded by `M`, then `u(0,x)^p ≤ M^p` pointwise, and the integral over
`[0,1]` is at most `M^p`.

Note: the `IsPaper2ClassicalSolution` interface only gives `u(t,x) > 0` for
`0 < t < T`, not at `t = 0`.  The initial trace bound requires either:
  (a) an additional `InitialTrace` / `PositiveInitialDatum` hypothesis, or
  (b) extracting the bound from the classical regularity at `t = 0`.

For now this is left as sorry. -/
theorem intervalDomain_initialPowerBound_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ p, p0 ≤ p →
      ∃ C0, 0 ≤ C0 ∧
        intervalDomain.integral (fun x => (u 0 x) ^ p) ≤ C0 := by
  sorry

/-! ### Power time integrability -/

/-- The energy map `t ↦ ∫₀¹ u(t,x)^p dx` is integrable on `[0,T]`.

If `energyContinuous` holds, this follows from
`ContinuousOn.integrableOn_compact` on the compact `Set.uIcc 0 T`.
Blocked on `energyContinuous`. -/
theorem intervalDomain_powerTimeIntegrable_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume := by
  sorry

/-! ### Gradient time integrability -/

/-- The gradient energy `t ↦ ∫₀¹ |∇(u(t,·)^{p/2})|² dx` is integrable on
`[0,T]`.

This is the gradient analogue of `powerTimeIntegrable`.  The proof strategy:
- From the classical regularity, `u(t,·)` is `C²` on `(0,1)` for each
  interior `t`, so `u(t,·)^{p/2}` is `C¹` on `(0,1)` (chain rule with
  `u > 0`), and the gradient norm squared is continuous on `(0,1)`.
- Joint space-time continuity of the gradient-energy integrand gives
  continuity of `t ↦ ∫₀¹ |∇(u^{p/2})|² dx` on `(0,T)`.
- Integrability on the compact `[0,T]` follows.

This is analytically harder than `powerTimeIntegrable` and is left as
sorry. -/
theorem intervalDomain_gradientTimeIntegrable_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume := by
  sorry

/-! ### Main producer -/

/-- Produce `IntegratedMoserFirstCrossingRegularity` for `intervalDomain`
from an `IsPaper2ClassicalSolution`.

All four fields are routed through the auxiliary lemmas above.  The
genuinely hard analysis (energy continuity, initial bound, gradient
integrability) is isolated in the sorry-marked auxiliaries. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 where
  energyContinuous :=
    intervalDomain_energyContinuous_of_classical hsol
  initialPowerBound :=
    intervalDomain_initialPowerBound_of_classical hsol
  powerTimeIntegrable :=
    intervalDomain_powerTimeIntegrable_of_classical hsol
  gradientTimeIntegrable :=
    intervalDomain_gradientTimeIntegrable_of_classical hsol

/-- Global-classical-solution version: extract `IntegratedMoserFirstCrossingRegularity`
for any finite horizon `T > 0`. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_classical
    (hglobal.classical hT)

/-! ### Combined regularity + nonnegativity package -/

/-- Produce both `IntegratedMoserFirstCrossingRegularity` and
`IntegratedMoserEnergyNonnegativity` from a single classical solution.
This is the standard entry point for the Moser iteration route. -/
theorem intervalDomain_regularity_and_nonnegativity_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 ∧
    IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
  ⟨intervalDomain_integratedMoserFirstCrossingRegularity_of_classical hsol,
   intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol⟩

/-! ### Lower-average/epsilon-gap data assembly -/

/-- Assemble the full `IntegratedMoserFirstCrossingLowerAverageEpsilonData`
from a classical solution, given the dissipation, interpolation, lower-average,
and epsilon-gap frontiers as separate inputs.

This is the top-level interface that the actual Moser wiring file should call.
The `hsol` gives regularity and nonnegativity; the remaining four hypotheses
are the genuine PDE content. -/
theorem intervalDomain_lowerAverageEpsilonData_of_classical
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hgap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          IntegratedMoserWindowUpperGapEpsilonFrontier
            intervalDomain u T rho p0 p) :
    IntegratedMoserFirstCrossingLowerAverageEpsilonData
      intervalDomain u T rho p0 where
  regularity :=
    intervalDomain_integratedMoserFirstCrossingRegularity_of_classical hsol
  energyNonneg :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
  dissipation := hdiss
  relative := hrel
  rho_pos := hrho
  p0_nonneg := hp0_nonneg
  lowerAverage := hlower
  epsilonGap := hgap

/-- Shortcut: produce `IntegratedMoserFirstCrossingStep` from a classical
solution and the four PDE-content hypotheses, going through the
lower-average/epsilon-gap route. -/
theorem intervalDomain_firstCrossingStep_of_classical_and_frontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore intervalDomain p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 p Cnext))
    (hgap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          IntegratedMoserWindowUpperGapEpsilonFrontier
            intervalDomain u T rho p0 p) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
    (intervalDomain_lowerAverageEpsilonData_of_classical
      hsol hdiss hrel hrho hp0_nonneg hlower hgap)

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
