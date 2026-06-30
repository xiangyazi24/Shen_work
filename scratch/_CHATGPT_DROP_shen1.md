# Q2648 shen1 — IntegratedStep sup-norm thin route audit

Repo: `xiangyazi24/Shen_work`

Target file: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

Current context: the file already has:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
```

with generic `K : CompactnessData intervalDomain`, plus the LowerUpper headline route already has both generic-K Stability24 and sup-norm+Stability24 thin surfaces.

## Recommendation

**Generic-K IntegratedStep Stability24 is enough by default.**

Do **not** add the IntegratedStep sup-norm thin route unless you want IntegratedStep to be a public, co-equal fallback headline next to LowerUpper.  The preferred headline is already LowerUpper thin, which is strictly closer to the intended producer split.  Adding another IntegratedStep thin route is valid and easy, but it is API bloat unless direct `IntegratedMoserFirstCrossingStep` producers are expected to be consumed directly by statement-level callers.

My recommended policy:

```text
Preferred headline:     LowerUpperThinP2MainData       keep/use
Useful fallback:        IntegratedStepStability24P2MainData  already enough
Optional fallback:      IntegratedStepThinP2MainData    add only if direct-step callers want same compactness-thin surface
Avoid proliferating:    CETerminal/CERawGrad/CEGrad/ClosedEnergy/base Moser thin variants
```

## Why generic-K is probably enough

The generic-K IntegratedStep Stability24 wrapper already removes the largest statement-layer bloat in that route: the full Theorem 2.3--2.5 stability package.  It keeps compactness generic:

```lean
compactness :
  IntervalDomainPaper3ConcreteCompactnessRegularizationData
    p M0 uBar vLower K
```

That is useful because it works for any future `CompactnessData intervalDomain`, not just the canonical sup-norm envelope package.

The remaining compactness fields are real for arbitrary `K`:

```lean
upperEq
compact
initialContinuity
minimalUpper
resolvent
```

The sup-norm thin route removes only the structural/vacuous parts of this compactness data:

```text
upperEq          definitional for intervalDomainSupNormCompactnessData
minimalUpper     impossible from 0 < p.a
initialContinuity shared once
```

This is nice, but not essential unless this IntegratedStep route is meant to be another public headline.

## When adding the IntegratedStep thin route is justified

Add it if one of these is true:

1. Another worker will produce a direct `IntegratedMoserFirstCrossingStep` atom but not `IntegratedMoserFirstCrossingLowerUpperFrontiers`.
2. You want the IntegratedStep route to be a public fallback headline with the same compactness-thin call surface as `LowerUpperThinP2MainData`.
3. Existing statement callers are already using the canonical sup-norm compactness package and repeatedly carrying `upperEq`, `minimalUpper`, and duplicate `initialContinuity`.

Do not add it just for symmetry.  Symmetry alone will create many near-identical wrappers and make the file harder to navigate.

## Exact fields if you add it

Use a new `Thin` structure, analogous to the LowerUpper thin structure but with the IntegratedStep core type.

```lean
structure IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
  initialContinuity : IntervalDomainInitialContinuityRaw p
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)
```

The statement-level route should be:

```lean
structure IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
```

## Lean skeleton if you decide yes

Insert this after the generic-K IntegratedStep Stability24 route and before the LowerUpper section, or after the LowerUpper thin section before the final namespace `end`.  The first import is only for standalone scratch checking; omit it when inserting into the existing file.

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Thin IntegratedStep mainline frontiers for the actual-linear fallback route.
This chooses the canonical sup-norm compactness package, shares initial continuity
once, uses `0 < a` to discharge the minimal-upper branch, and carries only the
non-vacuous Theorem 2.4 stability frontiers. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
  initialContinuity : IntervalDomainInitialContinuityRaw p
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the thin
IntegratedStep actual-linear fallback route. -/
theorem intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ
    { core := hData.core
      compactness :=
        (hData.compactness.toSupNormData ha hData.initialContinuity).toConcrete
      stability24 := hData.stability24 }

/-- Instance-facing concrete interval-domain Paper3 mainline from the thin
IntegratedStep actual-linear fallback route. -/
theorem intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
    p M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the thin IntegratedStep
actual-linear fallback route, with Proposition 1.3/1.4 routed through Paper2 main
theorem targets. -/
structure IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the full interval-domain Paper3 statement target from the thin
IntegratedStep actual-linear fallback route and Paper2 main theorem target inputs. -/
theorem intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
        p C M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
      ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the thin
IntegratedStep actual-linear fallback route and Paper2 main theorem target inputs. -/
theorem intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
        p C M0 uBar vLower locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

end

end ShenWork.Paper3
```

## Placement

If adding it, place it immediately after the generic-K IntegratedStep Stability24 P2Main route and before the LowerUpper section:

```lean
/-! ### Integrated first-crossing step route with Stability24 input -/
...
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainDataFact

/-! ### IntegratedStep route with thin compactness and Stability24 input -/
-- new declarations here

/-! ### Lower-average / upper-gap split route -/
```

This keeps the file organized by strength/refinement:

```text
IntegratedStep full
IntegratedStep Stability24
IntegratedStep Thin
LowerUpper full
LowerUpper Stability24
LowerUpper Thin
```

## `#print axioms` additions if yes

Add only the public theorem prints, not every conversion:

```lean
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
```

## Pitfalls

1. **Use `IntegratedStepFacts`, not residuals, for `core`:**

```lean
IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
```

not

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals p
```

2. **Use `intervalDomainPaper3Constants` for Stability24:**

```lean
IntervalDomainPaper3Stability24ActualLinearFrontierData p
  (intervalDomainPaper3Constants p M0 uBar vLower)
```

Do not use `intervalDomainSectorialPaper3Constants`; that belongs only to raw-linear Theorem 2.2 fields.

3. **Use `IntervalDomainPaper3SupNormCompactnessAPosData`, not full concrete compactness:**

```lean
compactness :
  IntervalDomainPaper3SupNormCompactnessAPosData
    p M0 uBar vLower locallyConverges neumannResolventGradientBound
```

and convert with:

```lean
(hData.compactness.toSupNormData ha hData.initialContinuity).toConcrete
```

4. **The target `K` is fixed:**

```lean
intervalDomainSupNormCompactnessData locallyConverges neumannResolventGradientBound
```

This route is not generic-K; the existing IntegratedStep Stability24 route remains the generic-K surface.

5. **Keep all actual-linear hypotheses on theorems:**

```lean
ha hb hχ0 hm hβ hχ
```

Only `ha` and `hχ0` are used directly in the compactness/stability thinning, but the existing route still needs `hb hm hβ hχ` for actual-linear persistence.

6. **Do not add this same thin route for CETerminal/CERawGrad/CEGrad/ClosedEnergy/base Moser unless a caller needs it.**

The IntegratedStep thin route is the only optional fallback that has a clear API story.  Beyond it, route proliferation will outweigh the reduction.

## Final answer

For current coordination, I would **not add it immediately** unless someone has a direct IntegratedStep caller asking for the compactness-thin surface.  The generic-K IntegratedStep Stability24 wrapper is sufficient and cleaner as a fallback.  If the team wants IntegratedStep to be a public alternate headline beside LowerUpper, then the thin route above is safe and should be the only additional thin variant added.
