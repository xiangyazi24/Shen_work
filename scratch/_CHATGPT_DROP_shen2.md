# Q2239 R3 Paper2 preferred interval-domain headline route cleanup audit for `Shen_work` main around `e3aa461e`

## Short answer

Yes, there is a small pure-wiring cleanup worth adding: a **documented alias type plus a short theorem alias** for the existing preferred route

```lean
intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
```

This should not introduce a new structure with copied fields, and it should not claim to discharge any new analysis. The preferred route is already present and correctly avoids the refuted global `IntervalDomainInterpolation` premise by using the positive solution-slice interpolation package.

## Why this route is preferred

`ShenWork/Paper2/IntervalDomainInterpolationCounterexample.lean` explicitly proves that the global `IntervalDomainInterpolation` statement is false as literally stated. Its header says the proposition quantifies over all positive interval functions with pointwise classical derivative as `gradNorm`, so a positive step-function counterexample has zero gradient almost everywhere but nonzero `L²` mass. Therefore, routes whose data include `IntervalDomainLemma41.IntervalDomainInterpolation` must not be promoted as headline routes.

The preferred route does **not** use that global premise. Its nested `common` package is

```lean
IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
```

whose interpolation field is

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation p
```

This is the positive solution-slice interface, not the refuted global arbitrary-function interpolation statement.

## Existing theorem chain

The current theorem is:

```lean
intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
```

It proves:

```lean
IntervalDomainPaper2StatementTargets p C
```

from parameter hypotheses `p.χ₀ = 0`, `0 < p.a`, `0 < p.b`, `1 ≤ p.α`, `1 ≤ p.γ`, plus the data package:

```lean
IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData p C cGrad
```

The theorem maps fields as follows:

```lean
⟨
  intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData
    p C cGrad
    (hData.localAndMain.main.theorem12And13.toPositive hχ0 ha hb hα hγ)
    hData.section2,
  intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
    p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.localAndMain
⟩
```

So it is already pure assembly:

1. section-2/corollary/bootstrap targets come from the positive solution-slice common data plus the thin section-2 data;
2. Lemma 3.1/Lemma 4.1 a priori targets use the solution-slice interpolation field;
3. local-plus-main targets use the local-free `χ₀ = 0` positive solution-slice route.

## Residual field audit

The preferred data structure is:

```lean
structure
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad
```

### `section2`

`section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p` still carries genuine analytic residuals:

- `lemma26` — bootstrap/Moser bound branch for Lemma 2.6;
- `lemma27` — differential inequality bound branch for Lemma 2.7;
- `prop22` — weighted gradient estimate branch;
- `prop23` — weighted signal estimate branch.

Inside the wrapper `intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData`, two components are already supplied elsewhere:

- Proposition 2.4 is produced by the exact theorem `intervalDomain_Proposition_2_4 p`;
- Proposition 2.5 is supplied by the nested Theorem 1.2/1.3 data field `prop25`, not by `section2`.

So `section2` is thinner than the older bootstrap bundle, but it is still a real frontier package.

### `localAndMain.proposition11`

`localAndMain.proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p` still carries the finite-horizon alternative residual:

```lean
finiteHorizonAlternative : ...
```

The local-existence part is already produced internally by the exact theorem:

```lean
intervalDomain_localExistence_chiZero_unconditional
```

through

```lean
intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
```

So this field is partly discharged by existing code, but the finite-horizon alternative remains genuine.

### `localAndMain.main.theorem12And13`

`localAndMain.main.theorem12And13` has type:

```lean
IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData p C cGrad
```

Its fields are:

- `common : IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad`;
- `prop25 : Proposition_2_5 intervalDomain p`;
- `globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p`;
- `slowBootstrap`;
- `criticalBootstrap`;
- `criticalEventualSupBound`;
- `strongBootstrap`;
- `strongEventualSupBound`.

The `localExistence` field used by the non-local-free positive solution-slice route is not present here. It is produced by:

```lean
IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData.toPositive
```

which fills it using:

```lean
intervalDomain_localExistence_chiZero_unconditional
```

Theorem 1.1 in the main bundle is also already produced by:

```lean
intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
```

through:

```lean
intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
```

The remaining fields are genuine analytic residuals unless separately supplied by another package in a future route.

### `common`

`common : IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad` remains a genuine solution-slice analytic package. Its fields are:

- `solutionInterpolation : IntervalDomainClassicalSolutionPositiveInterpolation p`;
- `dissipation : IntervalDomainPaper2DissipationFrontier`;
- `gradConstantPositive : IntervalDomainPaper2GradientConstantPositive cGrad`;
- `gradientChain : IntervalDomainPaper2GradientChainFrontier cGrad`;
- `massControl : IntervalDomainPaper2MassControlFrontier`;
- `powerIntegrability : IntervalDomainPaper2PowerIntegrabilityFrontier`;
- `energyFromCrossDiffusion : IntervalDomainPaper2EnergyFromCrossDiffusionFrontier p`.

Existing wrappers already use `common` to produce intermediate theorem components:

- Corollary 2.1 is produced by `IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_solution_interpolation_frontier` inside `intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData` and the positive-solution variants.
- Lemma 4.1 is produced from the solution-slice interpolation field by `intervalDomainPaper2_Lemma_4_1_of_solutionInterpolationFrontier`, which delegates to `IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_solution_interpolation_frontier`.
- The positive-constant field is dropped for corollary-only use by `IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData.toSolution`, using `IntervalDomainClassicalSolutionInterpolation_of_positive`.

These are conversions from the supplied solution-slice package; they are not producers of the package itself.

## Recommended cleanup

Add a preferred-name alias and theorem alias. Do **not** add a new structure copying the fields, because that would create another layer to audit and might hide residuals. An `abbrev` keeps the exact existing type transparent.

Place this near the existing preferred theorem, immediately before or after `intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData` in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`.

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain

namespace ShenWork.Paper2

noncomputable section

/-- Preferred `χ₀ = 0` interval-domain Paper2 statement-frontier package.

This is just a transparent alias for
`IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.
It avoids the refuted global `IntervalDomainInterpolation` route by using the
positive solution-slice interpolation package.  It is still conditional on the
thin section-2 frontiers, the finite-horizon alternative, the positive
solution-slice interpolation/energy package, `Proposition_2_5`, global
extension, bootstrap, and eventual-sup frontiers. -/
abbrev IntervalDomainPaper2PreferredChiZeroStatementFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad

/-- Preferred `χ₀ = 0` interval-domain Paper2 full-statement wrapper.

Pure wiring alias for
`intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.
It does not construct any residual package; it only gives the current preferred
route a shorter, grep-visible name. -/
theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2PreferredChiZeroStatementFrontierData
      p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData

/-- Instance-facing alias for the preferred `χ₀ = 0` interval-domain Paper2
full-statement route. -/
theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact (IntervalDomainPaper2PreferredChiZeroStatementFrontierData
      p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

end

end ShenWork.Paper2
```

When inserting into `IntervalDomainStatementAssembly.lean`, omit the repeated `import`, `open`, `namespace`, and `end` lines; keep only the declarations inside the existing namespace and section.

## If the team wants an even smaller edit

Skip the `abbrev` and add only this theorem alias with the existing data type:

```lean
/-- Preferred `χ₀ = 0` interval-domain Paper2 full-statement wrapper.

Pure wiring alias for the local-free positive solution-slice, section-2-thin
route.  Still conditional on all fields of
`IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`. -/
theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData
```

That is the smallest honest Lean edit. It improves discoverability without reintroducing `IntervalDomainInterpolation`, without inventing producers, and without obscuring the residual status of the nested fields.

## Do not add

Do not add any alias or theorem that depends on:

```lean
IntervalDomainPaper2StatementChiZeroInterpolationFrontierData
IntervalDomainPaper2InterpolationEnergyFrontierData
IntervalDomainLemma41.IntervalDomainInterpolation
```

as the preferred headline route. Those names belong to the known-false global interpolation branch documented by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.
