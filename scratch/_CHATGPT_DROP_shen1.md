# Q2352 shen1 — Paper2 actual-atoms wiring audit

Repo: `xiangyazi24/Shen_work`

Target branch for this drop: `chatgpt-scratch`

Scope: audit the proposed `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` wiring that adds structured-Moser and actual-atom Proposition 2.5 frontiers, with the actual-atom route using

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

I inspected the current repository shape through the GitHub connector. The `chatgpt-scratch` branch copy of `IntervalDomainStatementAssembly.lean` is behind `main` and does not show the proposed local patch, so this is a shape/import/cycle audit against the existing exported names and the described local patch, not a successful Lean build of the patch.

## Verdict

The patch direction is sound, with two important shape constraints.

1. The **actual-atom frontier should stay `Prop`**. Its fields are theorem-frontier predicates only: nonnegative-`B` Moser dissipation, relative interpolation, and a quantitative endpoint producer with an existential `pSeq/rootBound`. There is no reason to make this statement-level data a `Type` structure.

2. The **structured `Prop25MoserFrontiers` producer should be `Prop`-valued with an existential wrapper**. Do not expose a directly projected field returning `Prop25MoserFrontiers u T pExp` from a statement-level `: Prop` record. `Prop25MoserFrontiers` carries data fields `pSeq` and `rootBound`, so direct projection is the wrong interface for the surrounding statement-level `Fact`/frontier style. Wrap the data existentially, unpack it only inside proofs of `Prop`, and locally rebuild `Prop25MoserFrontiers` when calling the existing structured-Moser theorem.

3. Do **not** route actual atoms through `Prop25MoserFrontiers`. The structured-Moser theorem and the actual-atom theorem have different shapes: `Prop25MoserFrontiers` packages the old structured route at `rho = 1` with `MoserDissipationDropBefore`; the actual-atom theorem consumes `MoserDissipationDropBeforeNonnegB`, `RelativeMoserInterpolationBefore`, and the endpoint producer directly, and internally builds the needed bootstrap at `rho = 2 * params.γ`.

4. Namespace/imports are correct if you import `P3MoserActualWiring` directly and either open or qualify the two lower namespaces:

```lean
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
```

or just use fully qualified names. Opening `P3MoserActualWiring` alone does **not** expose `MoserDissipationDropBeforeNonnegB`; that predicate lives in `P3MoserDissipationShape`.

5. Avoid both no-go routes in any headline statement assembly:

```lean
OldUnitIntervalPowerGNYoungForMoser
IntervalDomainLemma41.IntervalDomainInterpolation
```

`OldUnitIntervalPowerGNYoungForMoser` is explicitly retained as an old/false-for-constants route in `IntervalDomainMCL.lean`. The global `IntervalDomainInterpolation` premise is also marked as refuted in the current statement assembly comments; use the positive solution-slice interpolation frontiers instead.

## Cycle risk

The safe dependency direction is:

```text
Paper2/IntervalDomainStructuredMoserData
PDE/P3MoserActualWiring
  -> Paper2/IntervalDomainStatementAssembly
```

More explicitly, `P3MoserActualWiring.lean` imports lower modules such as `IntervalDomainMoserActualAtoms`, `P3MoserDissipationShape`, and `IntervalDomainCrossDiffusionBootstrap`; those lower files should not import `IntervalDomainStatementAssembly`. With that direction, importing `ShenWork.PDE.P3MoserActualWiring` from `IntervalDomainStatementAssembly.lean` is cycle-safe.

I would still prefer a tiny Paper2-facing wrapper file for long-term hygiene, but if the local patch intentionally places the wrappers directly in `IntervalDomainStatementAssembly.lean`, that is acceptable as long as the lower PDE actual-atom files never import the statement assembly.

Do **not** import `ShenWork.PDE.IntervalDomainMoserLadderAtoms` just to reach the actual-atom Prop. 2.5 theorem. That file is a heavier route-residual layer. The minimal theorem is already in:

```lean
import ShenWork.PDE.P3MoserActualWiring
```

## Minimal Lean shape

This is the shape I would use inside `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`. The imports are included explicitly; place the definitions after the existing section-2/Prop25/frontier definitions or near the current Theorem 1.2/1.3 positive solution-slice frontier block.

```lean
import ShenWork.Paper2.IntervalLemma31Closure
/-
  Paper2 interval-domain statement-target assembly.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalDomainMass
import ShenWork.Paper2.IntervalDomainTheorem12
import ShenWork.Paper2.IntervalDomainTheorem13
import ShenWork.Paper2.IntervalDomainStructuredMoserData
import ShenWork.PDE.P3MoserActualWiring

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainStructuredMoserData
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring

namespace ShenWork.Paper2

noncomputable section

/-- Prop-valued statement-layer wrapper for the structured-Moser Prop. 2.5
frontier.

`Prop25MoserFrontiers` itself carries data (`pSeq`, `rootBound`), so the
statement-level record keeps the field in `Prop` by existentially hiding that
data.  The theorem below unpacks the witnesses only while proving the Prop-valued
statement `Proposition_2_5 intervalDomain p`. -/
structure IntervalDomainPaper2Prop25StructuredMoserFrontierData
    (p : CM2Params) : Prop where
  frontiers :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          LpBootstrapEnergyInequality intervalDomain u T 1 pExp ∧
          MoserDissipationDropBefore intervalDomain u T 1 pExp ∧
          RelativeMoserInterpolationBefore intervalDomain u T 1 pExp ∧
          (∀ r : ℝ, 1 < r → ∀ t, 0 < t → t < T →
            IntervalIntegrable
              (intervalDomainLift
                (fun x : intervalDomain.Point => (u t x) ^ r))
              MeasureTheory.volume 0 1) ∧
          ((∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound)

/-- Structured-Moser frontier produces interval-domain Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25StructuredMoserFrontierData p) :
    Proposition_2_5 intervalDomain p := by
  refine
    IntervalDomainStructuredMoserData.Proposition_2_5_intervalDomain_of_prop25_moser_frontiers
      ?_
  intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
  rcases hData.frontiers hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨pSeq, rootBound, henergy, hdiss, hrel, hpow, hend⟩
  exact
    { pSeq := pSeq
      rootBound := rootBound
      energy := henergy
      dissipation := hdiss
      relative := hrel
      powerIntegrable := hpow
      endpoint := hend }

/-- Instance-facing structured-Moser wrapper. -/
theorem intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25StructuredMoserFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierData
    p hData.out

/-- Paper2-facing actual-atom frontier for interval-domain Proposition 2.5.

This is the preferred Prop. 2.5 replacement when using the actual Moser atoms:
physical/nonnegative-`B` dissipation, relative Moser interpolation, and the
quantitative endpoint/root-tower producer.  It intentionally does not mention
`Prop25MoserFrontiers`, because the actual-atom theorem consumes these fields
directly. -/
structure IntervalDomainPaper2Prop25ActualAtomFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

/-- Actual-atom frontier produces interval-domain Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    hData.moserDissipation hData.relativeMoserInterpolation
    hData.quantitativeEndpoint

/-- Instance-facing actual-atom wrapper. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25ActualAtomFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData p hData.out

end

end ShenWork.Paper2
```

## Minimal local-free positive-solution variant using actual atoms

If the patch also adds a Theorem 1.2/1.3 or main-theorem frontier that replaces the existing direct

```lean
prop25 : Proposition_2_5 intervalDomain p
```

field, do not make it inherit from the existing record while also keeping the old `prop25` field. Repeat the existing fields and replace only that one field by the actual-atom producer.

The exact minimal pattern is:

```lean
import ShenWork.Paper2.IntervalLemma31Closure
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalDomainMass
import ShenWork.Paper2.IntervalDomainTheorem12
import ShenWork.Paper2.IntervalDomainTheorem13
import ShenWork.Paper2.IntervalDomainStructuredMoserData
import ShenWork.PDE.P3MoserActualWiring

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring

namespace ShenWork.Paper2

noncomputable section

/-- Actual-atom version of the preferred `χ₀ = 0` local-free positive
solution-slice Theorem 1.2/1.3 frontier.  It is identical to
`IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData`
except that `prop25` is replaced by `prop25Actual`. -/
structure
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common :
    IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
  prop25Actual : IntervalDomainPaper2Prop25ActualAtomFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Convert the actual-atom local-free frontier to the existing local-free
frontier by producing the direct `Proposition_2_5` field. -/
def
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData.toLocalFree
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad where
  common := h.common
  prop25 :=
    intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
      p h.prop25Actual
  globalExtension := h.globalExtension
  slowBootstrap := h.slowBootstrap
  criticalBootstrap := h.criticalBootstrap
  criticalEventualSupBound := h.criticalEventualSupBound
  strongBootstrap := h.strongBootstrap
  strongEventualSupBound := h.strongEventualSupBound

/-- Assemble Theorems 1.2 and 1.3 from the actual-atom local-free frontier. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.toLocalFree

end

end ShenWork.Paper2
```

The same pattern can be used for the main-theorem wrapper: define a one-field actual-atom local-free main frontier whose `theorem12And13` field is the actual-atom local-free Theorem 1.2/1.3 frontier, then convert by calling the theorem above.

## Why the existential wrapper matters

`Prop25MoserFrontiers` is not merely a proposition-shaped theorem assumption. It stores:

```lean
pSeq : ℕ → ℝ
rootBound : ℕ → ℝ
```

plus proof fields. That means a statement-level frontier should not be designed around projecting those fields from an arbitrary theorem package. A `Prop` wrapper like this is robust:

```lean
frontiers :
  ∀ ..., ∃ pSeq rootBound : ℕ → ℝ,
    LpBootstrapEnergyInequality intervalDomain u T 1 pExp ∧
    MoserDissipationDropBefore intervalDomain u T 1 pExp ∧
    RelativeMoserInterpolationBefore intervalDomain u T 1 pExp ∧
    ...
```

Then the only place that constructs the `Type`-level `Prop25MoserFrontiers` value is the theorem proof, whose goal is itself a `Prop`. This keeps the statement assembly compatible with `Fact (...)` wrappers and avoids computational data leaking into the top-level theorem-frontier API.

A shorter but slightly less explicit alternative is:

```lean
frontiers :
  ∀ ..., Nonempty (Prop25MoserFrontiers u T pExp)
```

That also keeps the field in `Prop`, but I prefer the explicit existential over `pSeq/rootBound` and the proof fields because it makes the frontier boundary auditable.

## Actual-atom frontier should remain Prop

The actual-atom frontier already has the right proof-only shape. The endpoint field is already existential:

```lean
quantitativeEndpoint :
  ∀ ...,
    LpPowerBoundedBefore intervalDomain pExp T u →
      ∃ pSeq rootBound : ℕ → ℝ,
        (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
          IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

So the enclosing structure can and should be:

```lean
structure IntervalDomainPaper2Prop25ActualAtomFrontierData
    (p : CM2Params) : Prop where
  ...
```

Making it `Type` would be a regression: it would prevent the usual `Fact`-based instance-facing wrappers and would make a statement-level theorem package look computational when it is not.

## Namespace/import audit

Use these names exactly or qualify them fully:

```lean
-- structured route
ShenWork.Paper2.IntervalDomainStructuredMoserData.Prop25MoserFrontiers
ShenWork.Paper2.IntervalDomainStructuredMoserData.Proposition_2_5_intervalDomain_of_prop25_moser_frontiers

-- actual atom route
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.MoserDissipationDropBeforeNonnegB
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

The minimal new imports are:

```lean
import ShenWork.Paper2.IntervalDomainStructuredMoserData
import ShenWork.PDE.P3MoserActualWiring
```

`P3MoserActualWiring` already imports the physical/nonnegative-`B` predicate path, but importing `IntervalDomainStructuredMoserData` directly is clearer if the patch mentions `Prop25MoserFrontiers` or `Proposition_2_5_intervalDomain_of_prop25_moser_frontiers`.

Avoid:

```lean
import ShenWork.PDE.IntervalDomainMoserLadderAtoms
```

unless the patch actually needs the later route-residual package in that file. For just Prop. 2.5 actual-atoms wiring, it is too heavy.

## Warnings about the two no-go frontiers

Do not use this in new headline routes:

```lean
OldUnitIntervalPowerGNYoungForMoser
```

It is explicitly marked as legacy and false for constant functions. In particular, do not use

```lean
relativeMoserInterpolationBefore_of_unitIntervalPowerGNYoung
```

as the source of the actual-atom `relativeMoserInterpolation` field. For the actual-atom frontier, `relativeMoserInterpolation` should remain an independent frontier until the corrected relative interpolation proof is supplied.

Also do not use the global arbitrary-function interpolation statement:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
```

The preferred current statement assembly path is the positive solution-slice route:

```lean
IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
```

and the actual-atom variant should extend/convert into that route, not into the deprecated global-interpolation route.

## Final recommendation

For the local patch described in Q2352:

- Keep `IntervalDomainPaper2Prop25ActualAtomFrontierData : Prop`.
- If adding a structured-Moser `Prop25MoserFrontiers` producer, make the producer field `Prop` via an existential wrapper; rebuild `Prop25MoserFrontiers` only inside the theorem proof.
- Import `ShenWork.PDE.P3MoserActualWiring` directly; optionally import `ShenWork.Paper2.IntervalDomainStructuredMoserData` directly for clarity.
- Qualify or open both `P3MoserActualWiring` and `P3MoserDissipationShape`.
- Do not introduce `OldUnitIntervalPowerGNYoungForMoser` or `IntervalDomainLemma41.IntervalDomainInterpolation` into the new headline wiring.
- Prefer a small wrapper file for dependency hygiene, but direct insertion into `IntervalDomainStatementAssembly.lean` is cycle-safe if lower PDE/Paper2 files never import the statement assembly.
