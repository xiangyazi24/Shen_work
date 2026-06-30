# Q2429 shen2: integrated Moser Stage 1 Lean API compile audit

Repo target: `xiangyazi24/Shen_work`, `main` at commit `8466aff054e1a3dd7fb3d02a0c4523132c6d6722`.

## Verdict

The Stage 1 routine closure layer should compile as a standalone new module with only this import:

```lean
import ShenWork.PDE.P3MoserDissipationShape
```

No theorem should yet claim

```lean
IntegratedMoserDissipationDropBefore ... → IntegratedMoserFirstCrossingStep ...
```

The right Stage 1 design is to introduce a step predicate and prove only routine consumers of that step.  The real analytic proof remains a later theorem that produces the step.

## Current API facts checked

The names from the Q2411 skeleton are still available at this commit:

* `BoundedDomainData`, `intervalDomain`, and `intervalDomainLift` are in the imported dependency chain through `P3MoserDissipationShape`.
* `LpPowerBoundedBefore`, `AbstractLpBootstrapHypothesis`, `RelativeMoserInterpolationBefore`, `IntervalDomainMoserQuantitativeEndpoint`, `intervalDomain_boundedBefore_of_moser_quantitative_endpoint`, and `all_exponents_of_chain_and_lp_mono` are available from `ShenWork.Paper2.IntervalDomainMoserClosure`, already imported by `P3MoserDissipationShape`.
* `IntegratedMoserDissipationDropBefore` is available from `ShenWork.IntervalDomainExistence.P3MoserDissipationShape`, but Stage 1 does not need to mention it except through the import/module purpose.
* `MeasureTheory.volume`, `IntegrableOn`, and `ContinuousOn` are available through existing imports; open `MeasureTheory` in the new file for the unqualified `volume` field.

## New file: `ShenWork/PDE/P3MoserIntegratedClosure.lean`

This is the minimal Stage 1 file.  It contains no axioms, no `sorry`, and no analytic bridge from integrated dissipation to the step.

```lean
import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Closed-time and time-integrability data needed by a future integrated
first-crossing Moser step.

This is intentionally all-exponent data indexed by every `p >= p0`, not just
the existing closed-time L² seed frontier from `P3MoserLemmas`. -/
structure IntegratedMoserFirstCrossingRegularity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  initialPowerBound :
    ∀ p, p0 ≤ p →
      ∃ C0, 0 ≤ C0 ∧
        D.integral (fun x => (u 0 x) ^ p) ≤ C0
  powerTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- The one-step output needed from the future integrated first-crossing
argument.  Stage 1 only consumes this step; it does not produce it from
`IntegratedMoserDissipationDropBefore`. -/
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u

/-- Routine: iterate a supplied integrated first-crossing step along the
arithmetic Moser ladder. -/
theorem moser_iteration_chain_of_integrated_first_crossing_step
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
      simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      exact hbase
  | succ n ih =>
      have hexp_eq :
          p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
        push_cast
        ring
      rw [hexp_eq]
      have hp_ge : p0 ≤ p0 + ↑n * rho :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
      exact hstep (p0 + ↑n * rho) hp_ge ih

/-- Routine: a supplied integrated first-crossing step plus downward Lp
monotonicity gives all finite exponents. -/
theorem all_exponents_of_integrated_first_crossing_step_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_integrated_first_crossing_step
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      hstep)
    hLpMono

/-- Routine: interval-domain finite-horizon boundedness from a supplied
integrated first-crossing step and the existing quantitative endpoint. -/
theorem intervalDomain_boundedBefore_of_integrated_first_crossing_step
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u :=
    all_exponents_of_integrated_first_crossing_step_lpmono
      hboot hstep hLpMono
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hEndpoint hAll)

#print axioms IntegratedMoserFirstCrossingRegularity
#print axioms IntegratedMoserFirstCrossingStep
#print axioms moser_iteration_chain_of_integrated_first_crossing_step
#print axioms all_exponents_of_integrated_first_crossing_step_lpmono
#print axioms intervalDomain_boundedBefore_of_integrated_first_crossing_step

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

## `ShenWork.lean` import line

For `lake build ShenWork.PDE.P3MoserIntegratedClosure`, no root import is needed.

For `lake build ShenWork` to cover the new module, yes: add one import line to `ShenWork.lean`.  The lowest-risk placement is next to the existing `P3MoserActualWiring` import:

```lean
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper3.IntervalDomainMoserLadderHeadline
```

This creates no cycle: `P3MoserIntegratedClosure` imports `P3MoserDissipationShape`; it does not import `P3MoserActualWiring`, `IntervalDomainStatementAssembly`, or any Paper3 file.

## Suggested local checks

Run:

```bash
lake env lean ShenWork/PDE/P3MoserIntegratedClosure.lean
lake build ShenWork.PDE.P3MoserIntegratedClosure
lake build ShenWork
```

Expected `#print axioms` targets:

```lean
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserFirstCrossingRegularity
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserFirstCrossingStep
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.moser_iteration_chain_of_integrated_first_crossing_step
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.all_exponents_of_integrated_first_crossing_step_lpmono
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.intervalDomain_boundedBefore_of_integrated_first_crossing_step
```

The theorem targets should have the same harmless axiom profile as surrounding Prop-valued classical assembly lemmas, typically only core Lean/mathlib axioms such as `propext`, `Classical.choice`, and `Quot.sound`, if any appear.  There should be no `sorryAx`, no custom axiom, and no dependence on an integrated-to-pointwise adapter.

## Hard theorem deliberately absent from Stage 1

Do not add this yet:

```lean
theorem integratedMoserFirstCrossingStep_of_integrated_dissipation_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hT : 0 < T)
    (hrho : 0 < rho)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0
```

That theorem is the real analytic first-crossing proof and should be a later patch.
