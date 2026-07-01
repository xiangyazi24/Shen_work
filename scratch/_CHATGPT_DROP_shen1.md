# Q2772 (shen1) — safest next non-Zinan Paper3 Moser patch

Repo: `xiangyazi24/Shen_work`  
Current main noted by user: latest pushed commit `abd0aa1c` adds closure-side gradient-energy nonnegativity utilities in `ShenWork/PDE/P3MoserIntegratedClosure.lean`  
Delivery branch: `chatgpt-scratch`

I treated these Zinan-owned files as off-limits and did **not** inspect, rely on, or propose edits to them:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`

Inspected non-Zinan candidate/current consumer files:

- `ShenWork/PDE/P3MoserIntegratedClosure.lean`
- `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`
- `ShenWork/PDE/P3MoserRegularityProducer.lean`
- `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`
- `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`

## Recommendation

The safest next Codex patch is in:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

Add a **NoNeg wrapper for the current thin integrated-step actual-linear Paper3 headline route**:

```lean
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
```

plus theorem and `Fact` wrapper.

This is the lowest-conflict way to reduce Paper3 headline assumptions because it removes the independent `negativeBound` residual from the preferred integrated-step/P2Main statement surface. It does not touch Zinan files, does not import a Zinan producer, and uses only already-proved wrappers in the same file.

## Why this is safer than using the Zinan threshold producer now

The file already has a good integrated-step statement route:

```lean
structure IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
```

whose fields are:

```lean
propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
mainline : IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
  p M0 uBar vLower locallyConverges neumannResolventGradientBound
```

But `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData` still contains:

```lean
negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p
paper2Main : IntervalDomainPaper2MainTheoremTargets p C
```

In the actual-linear-small route we already assume:

```lean
hχ0 : 0 < p.χ₀
```

and the same file already proves the needed vacuity theorem:

```lean
theorem intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
    (p : CM2Params) (hχ0 : 0 < p.χ₀) :
    NegativeSensitivityGlobalEventualBound intervalDomain p
```

So the next patch can replace the full `propositions` field by only:

```lean
paper2Main : IntervalDomainPaper2MainTheoremTargets p C
```

This exactly mirrors the earlier non-Moser wrapper:

```lean
IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
```

but targets the current integrated-step Moser/headline route.

## Patch sketch

Place this after the existing theorem:

```lean
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainDataFact
```

and before the lower-average / upper-data-gap section.

If pasted directly into `IntervalDomainActualLinearStatementAssembly.lean`, do **not** include the import block below; it is only for orientation.

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Full interval-domain Paper3 statement frontiers for the thin integrated-step
actual-linear headline route, with the negative-sensitivity Proposition 1.2
residual discharged by `0 < χ₀` and Proposition 1.3/1.4 routed through Paper2
main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the full interval-domain Paper3 statement target from the thin
integrated-step actual-linear headline route and Paper2 main theorem targets,
without carrying a separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainNoNegData
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
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing full interval-domain Paper3 statement target from the thin
integrated-step actual-linear headline route and Paper2 main theorem targets,
with the negative-sensitivity residual discharged by `0 < χ₀`. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainNoNegDataFact
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
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainNoNegData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

end ShenWork.Paper3
```

## Why this should compile

It is only a packaging wrapper. It reuses names that already exist in the same file:

- `IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData`
- `intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData`
- `IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData`
- `intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos`
- `intervalDomainSupNormCompactnessData`

No new math, no new import, no Zinan dependency.

## What assumption it removes

Before this wrapper, the current thin integrated-step Paper3 statement route asks for:

```lean
propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
```

which includes both:

```lean
negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p
paper2Main : IntervalDomainPaper2MainTheoremTargets p C
```

After this wrapper, the route asks only for:

```lean
paper2Main : IntervalDomainPaper2MainTheoremTargets p C
```

because `negativeBound` is constructed from `hχ0 : 0 < p.χ₀`.

This is a genuine headline-frontier reduction and stays fully non-Zinan.

## Optional second patch, not first

After the above compiles, the analogous NoNeg wrapper can be added for the component lower-average/upper-data-gap route:

```lean
IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
```

But I would not do that first. The integrated-step thin P2Main route is already the most concise headline surface and is likely the one downstream users should target once any producer supplies `IntegratedMoserFirstCrossingStep`.

## Do not do this yet

Do not import or consume the Zinan threshold producer in `IntervalDomainMoserLadderAtoms.lean` or `Paper3/IntervalDomainActualLinearStatementAssembly.lean` right now. Even if the theorem exists, it is an active worker-owned producer surface. The wrapper above gives an immediate assumption reduction without depending on that moving API.
