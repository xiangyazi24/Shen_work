# Q2391 shen2: Prop25 nonnegative-B Moser dissipation audit

Repo target: `xiangyazi24/Shen_work`, `main` at commit `ceba98b2`.

## Verdict

No small faithful statement-layer patch currently reduces the remaining Prop. 2.5 atom

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.MoserDissipationDropBeforeNonnegB
```

to the existing integrated predicate

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.IntegratedMoserDissipationDropBefore
```

The current source requires a new integrated-first-crossing Moser chain before that reduction can feed Corollary 2.1 or Proposition 2.5.  The existing `IntegratedMoserDissipationDropBefore` / `integratedMoserDissipationDropBefore_of_integrated_energy` pair is only a predicate plus a same-shape packaging theorem; it is not consumed by the existing Moser closure.

## Source-grounded facts

1. `IntervalDomainPaper2Prop25ActualAtomFrontierData` in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` still carries

```lean
moserDissipation :
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
    ShenWork.IntervalDomainExistence.P3MoserDissipationShape.MoserDissipationDropBeforeNonnegB
      intervalDomain u T rho p0
```

and `intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData` passes this field directly to

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

2. The mass-gradient reduction does not lower dissipation.  The conversion
`IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms` contains

```lean
moserDissipation := h.moserDissipation
```

and only converts the relative field through

```lean
ShenWork.IntervalDomainExistence.P3MoserLemmas.intervalDomain_relativeMoserInterpolationBefore_of_massGradient
```

3. The terminal-endpoint reduction also does not lower dissipation.  The conversion
`IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData.toMassGradient` contains

```lean
moserDissipation := h.moserDissipation
relativeMassGradient := h.relativeMassGradient
```

and only converts the terminal pointwise endpoint into constant `pSeq` / `rootBound` data.

4. `ShenWork/PDE/P3MoserActualWiring.lean` has the two current actual-atom consumers

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

Both require an `hdiss` argument producing `MoserDissipationDropBeforeNonnegB`.  The endpoint consumer finally calls

```lean
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
```

with `(hdiss hsol hcross hboot)`.

5. `ShenWork/PDE/P3MoserDissipationShape.lean` defines the integrated predicate

```lean
def IntegratedMoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        2 * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))
```

and `integratedMoserDissipationDropBefore_of_integrated_energy` merely packages a same-shape hypothesis into that predicate.

6. The same file explicitly records the shape diagnosis: the pointwise drop is not the faithful analytic consequence of the PDE energy estimate, and an integrated first-crossing energy inequality is the faithful shape.  It also proves

```lean
theorem unitLinearDrop_not_MoserDissipationDropBeforeNonnegB :
    ¬ MoserDissipationDropBeforeNonnegB
      unitLinearDropDomain unitLinearDropU 1 1 1
```

so an abstract bridge from integrated data to the pointwise nonnegative-`B` predicate would be a no-go without substantial new hypotheses.

7. The existing nonnegative-`B` closure is pointwise.  Its core step is

```lean
theorem moser_step_of_energy_nonnegB_relative_interpolation
```

and its proof performs the local subtraction

```lean
rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hfull⟩
have hdrop_t := hdiss p hp A B K L_const hB.le hfull t ht0 htT
linarith
```

The integrated predicate gives an interval inequality for `Y_p t2 - Y_p t1 + 2∫G_p`, not the pointwise fact `0 ≤ (1 / p) * Y_p' t + B * Y_p t` needed at this line.

8. `ShenWork/Paper2/IntervalDomainMoserClosure.lean` is also pointwise: `MoserDissipationDropBefore`, `RelativeMoserInterpolationBefore`, `moser_step_of_energy_dissipation_relative_interpolation`, and `IntervalDomainStructuredMoserBootstrapData.dissipation` all use the pointwise drop shape.  The abstract single-step `IntervalDomainChain.lp_bootstrap_single_step_abstract` also expects pointwise-in-time `A * G(t) ≤ K * Z(t) + L`.

## Consequence

`IntegratedMoserDissipationDropBefore` cannot be consumed by the existing Moser closure.  A statement-layer patch that merely swaps the carried field from `MoserDissipationDropBeforeNonnegB` to `IntegratedMoserDissipationDropBefore` would not feed any existing theorem.  A patch that tries to prove `MoserDissipationDropBeforeNonnegB` from the integrated predicate would be analytically unsupported by the current APIs and conflicts with the source's counterexample/diagnosis.

## Minimal honest new theorem family

The next real file should be a new integrated closure layer, for example:

```lean
import ShenWork.PDE.P3MoserDissipationShape
import ShenWork.PDE.P3MoserLemmas
import ShenWork.Paper2.IntervalDomainMoserClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

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
      ∃ C0, 0 ≤ C0 ∧ D.integral (fun x => (u 0 x) ^ p) ≤ C0
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

/-
New analytic theorem required; no current source theorem has this shape.

theorem lpPowerBoundedBefore_succ_of_integrated_first_crossing
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hLp : LpPowerBoundedBefore D p T u) :
    LpPowerBoundedBefore D (p + rho) T u
-/

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

Once that single-step theorem is proved, the remaining derived family is routine and should be added under the same namespace:

```lean
moser_iteration_chain_of_integrated_first_crossing
all_exponents_of_integrated_first_crossing_lpmono
intervalDomain_boundedBefore_of_integrated_first_crossing
```

Then `P3MoserActualWiring` can add integrated actual-atom consumers analogous to the current nonnegative-`B` consumers:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_atoms
```

Only after those consumers exist should `IntervalDomainStatementAssembly.lean` add an integrated statement package, e.g.

```lean
IntervalDomainPaper2Prop25ActualIntegratedAtomMassGradientTerminalEndpointFrontierData
```

with fields:

```lean
firstCrossingRegularity
integratedDissipation
relativeMassGradient
terminalEndpoint
```

where `relativeMassGradient` and `terminalEndpoint` reuse the existing shapes from `IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData`, while `integratedDissipation` has target

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

## No-go routes

* Do not add an integrated-to-`MoserDissipationDropBeforeNonnegB` adapter.  The source explicitly treats the integrated estimate as the faithful replacement shape and contains `unitLinearDrop_not_MoserDissipationDropBeforeNonnegB`.
* Do not expect the mass-gradient wrapper to lower dissipation.  It only lowers `RelativeMoserInterpolationBefore`.
* Do not expect the terminal-endpoint wrapper to lower dissipation.  It only lowers the endpoint tower.
* Do not use `OldUnitIntervalPowerGNYoungForMoser`; `IntervalDomainMCL.lean` documents it as false for constant functions.
* Do not use the global `IntervalDomainInterpolation` route; `IntervalDomainStatementAssembly.lean` marks it deprecated because the literal statement is refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.

## Final recommendation

Leave `MoserDissipationDropBeforeNonnegB` as a genuine analytic frontier for the current statement layer.  The next honest reduction is a new integrated-first-crossing Moser closure, not a small statement-layer patch.
