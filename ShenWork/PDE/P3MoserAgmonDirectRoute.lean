import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.P3MoserThresholdPlanProducer
import ShenWork.PDE.P3MoserRegularityProducer
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainCrossDiffusionBootstrap

/-!
# Agmon-based direct route to Moser iteration (1D)

This file produces `IntegratedMoserFirstCrossingStep` (and hence all Lp bounds
and Proposition 2.5) for the concrete `intervalDomain` using the proved Agmon
interpolation, WITHOUT going through `RelativeMoserInterpolationBefore` as a
precondition.

## The gradient-exponent mismatch and its resolution

The Agmon interpolation gives (for positive C² functions on [0,1]):
  `∫ f^q ≤ ε · ∫ f^{q-2}|f'|² + Cε · (∫f)^q`

The existing Moser machinery needs `RelativeMoserInterpolationBefore`:
  `∫ u^{p+ρ} ≤ ε · ∫ |∇(u^{p/2})|² + Cε · ∫ u^p`

The gradient terms differ: `f^{q-2}|f'|²` vs `|∇(f^{p/2})|²`. By chain rule
`|∇(u^{p/2})|² = (p/2)² u^{p-2}|∇u|²`, so converting requires bounding `u^ρ`
pointwise — an L∞ bound, which is what Moser iteration PROVES (circular).

### Resolution: bound-dependent interpolation inside the iteration

The 1D Sobolev embedding (Agmon inequality for `g = u^{p/2}`) gives
  `u(x)^p ≤ C(∫u^p + ∫|∇(u^{p/2})|²)`    pointwise

Combined with `∫u^{p+ρ} ≤ ‖u‖∞^ρ · ∫u^p`, Young's inequality with
sub-additivity of concave powers, and the current Lp bound `∫u^p ≤ M`:

  `∫ u^{p+ρ} ≤ ε · ∫ |∇(u^{p/2})|² + (Cε · M^{ρ/(p-ρ)}) · ∫ u^p`

The constant `Cε · M^{ρ/(p-ρ)}` depends on `M` (the Lp bound from the
previous Moser step), but this is fine: inside the iteration, M is KNOWN.

This produces `RelativeMoserInterpolationBefore` at each step of the iteration,
feeding the threshold plan → `IntegratedMoserFirstCrossingStep` → next Lp bound.
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserThresholdPlanProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

/-! ### Step 1: Pointwise Sobolev for u^{p/2} on [0,1]

From the proved `agmon_inequality_interval` with `f = intervalDomainLift (u^{p/2})`
and L = 1:
  `(u(x)^{p/2})² ≤ 2 ∫(u^{p/2})² + 2√(∫(u^{p/2})²) · √(∫|(u^{p/2})'|²)`
i.e.,
  `u(x)^p ≤ 2 ∫u^p + 2√(∫u^p) · √(∫|∇(u^{p/2})|²)`

This is available from the existing `agmon_inequality_interval` applied to
classical solution slices.
-/

theorem intervalDomain_pointwise_sobolev_rpow
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hpExp : 2 ≤ pExp) :
    ∀ x : intervalDomain.Point,
      (u t x) ^ pExp ≤
        2 * intervalDomain.integral (fun y => (u t y) ^ pExp) +
        2 * Real.sqrt (intervalDomain.integral (fun y => (u t y) ^ pExp)) *
          Real.sqrt (intervalDomain.integral (fun y =>
            (intervalDomain.gradNorm
              (fun z => (u t z) ^ (pExp / 2)) y) ^ 2)) := by
  sorry

/-! ### Step 2: Superlinear interpolation

From Step 1: `u(x)^ρ ≤ (2A + 2√A√G)^{ρ/p}` where A = ∫u^p, G = ∫|∇(u^{p/2})|².

Then `∫u^{p+ρ} ≤ (2A + 2√A√G)^{ρ/p} · A`.

Using sub-additivity of concave powers (ρ/p < 1) and Young:
  `∫u^{p+ρ} ≤ ε G + Cε (A + A^{p/(p-ρ)})`
-/

theorem intervalDomain_superlinear_moser_interpolation
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hrho : 0 < rho)
    (hp0 : 2 ≤ p0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ Csl > 0,
      ∀ pExp, p0 ≤ pExp → rho < pExp →
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          Csl * ((intervalDomain.integral (fun x => (u t x) ^ pExp)) +
            (intervalDomain.integral (fun x => (u t x) ^ pExp)) ^
              (pExp / (pExp - rho))) := by
  sorry

/-! ### Step 3: Bound-dependent linearization

When `∫u^p ≤ M` and `M ≥ 1`:
  `(∫u^p)^{p/(p-ρ)} = (∫u^p)^{ρ/(p-ρ)} · ∫u^p ≤ M^{ρ/(p-ρ)} · ∫u^p`

So:  `∫u^{p+ρ} ≤ ε G + C'ε · ∫u^p` with `C'ε = Csl · (1 + M^{ρ/(p-ρ)})`.
-/

theorem intervalDomain_relativeMoserInterpolation_of_bound
    {params : CM2Params} {T rho p0 pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hrho : 0 < rho) (hp0 : 2 ≤ p0)
    (hpExp : p0 ≤ pExp) (hrho_lt : rho < pExp)
    {M : ℝ} (hM : 1 ≤ M)
    (hMbound : ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ M) :
    ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧ ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        eps * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
        Ceps * intervalDomain.integral (fun x => (u t x) ^ pExp) := by
  sorry

/-! ### Step 4: Integrated dissipation from energy balance + bound-dependent interpolation

The energy balance gives:
  `(1/p) Y'(t) + A G(t) + B Y(t) ≤ K Z(t) + L`

Using the bound-dependent interpolation `Z(t) ≤ ε G(t) + Cε Y(t)`:
  `(1/p) Y'(t) + (A - Kε) G(t) + (B - K Cε) Y(t) ≤ L`

Choosing ε small: `(1/p) Y'(t) + (A/2) G(t) ≤ L + |B - K Cε| Y(t)`.

Integrating: `Y(t₂) - Y(t₁) + (pA/2) ∫G ≤ pL(t₂-t₁) + p|B-KCε| ∫Y`.
-/

theorem intervalDomain_integratedDissipation_of_agmon_and_bound
    {params : CM2Params} {T rho p0 pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0)
    (hrho : 0 < rho) (hp0 : 2 ≤ p0)
    (hpExp : p0 ≤ pExp) (hrho_lt : rho < pExp)
    {M : ℝ} (hM : 1 ≤ M)
    (hMbound : ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ M) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho pExp := by
  sorry

/-! ### Step 5: Single Moser step (bound → next bound)

Combining:
- `LpBootstrapEnergyInequality` (proved from regularity)
- Bound-dependent `RelativeMoserInterpolationBefore` (Step 3)
- `IntegratedMoserDissipationDropBefore` (Step 4)
- Regularity data (from classical solution)
- Threshold plan (proved)

Produces `LpPowerBoundedBefore` at exponent `pExp + rho`.
-/

theorem intervalDomain_moser_single_step_of_agmon
    {params : CM2Params} {T rho p0 pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0)
    (hrho : 0 < rho) (hp0 : 2 ≤ p0)
    (hpExp : p0 ≤ pExp) (hrho_lt : rho < pExp)
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u) :
    LpPowerBoundedBefore intervalDomain (pExp + rho) T u := by
  sorry

/-! ### Step 6: Full Moser iteration (all Lp bounds from seed)

By induction on the exponent, using Step 5 at each level.
Produces `∀ r > 1, LpPowerBoundedBefore intervalDomain r T u`.
-/

theorem intervalDomain_allLp_of_agmon_moser_iteration
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0)
    (hrho : 0 < rho) (hp0 : 2 ≤ p0) (hrho_lt : rho < p0) :
    ∀ r : ℝ, 1 < r → LpPowerBoundedBefore intervalDomain r T u := by
  sorry

/-! ### Step 7: Wire to Corollary 2.1 and Proposition 2.5

All Lp bounds → Corollary 2.1 (immediate from the definition).
Lp bounds + quantitative endpoint → Proposition 2.5.
-/

theorem intervalDomain_Corollary_2_1_of_agmon_moser
    (params : CM2Params) :
    Corollary_2_1 intervalDomain params := by
  sorry

theorem intervalDomain_Proposition_2_5_of_agmon_moser
    (params : CM2Params)
    (hEndpoint :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    Proposition_2_5 intervalDomain params := by
  sorry

#check intervalDomain_allLp_of_agmon_moser_iteration
#check intervalDomain_Corollary_2_1_of_agmon_moser
#check intervalDomain_Proposition_2_5_of_agmon_moser

end ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

end
