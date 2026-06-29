# Q2239 R3 Paper2 preferred interval-domain headline route cleanup audit for `Shen_work` main around `e3aa461e`

## Bottom line

Yes, there is a useful small cleanup, but it should be only a **transparent preferred-name alias plus theorem alias**, not a new field-copying structure. The existing route

```lean
intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
```

is already the right preferred `χ₀ = 0` interval-domain Paper2 statement route: it uses the positive solution-slice interpolation package and does not reintroduce the refuted global `IntervalDomainInterpolation` premise. A new alias can make that status grep-visible without hiding residuals.

## Why this route is the preferred one

`ShenWork/Paper2/IntervalDomainInterpolationCounterexample.lean` states and proves `not_intervalDomainInterpolation`, with the file header explaining that the literal global `IntervalDomainInterpolation` proposition is false because it quantifies over all positive interval functions with pointwise classical derivative as `gradNorm`; a positive step-function counterexample has zero gradient almost everywhere but nonzero `L²` mass.

The preferred route avoids that proposition. Its nested positive route uses:

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation p
```

inside:

```lean
IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
```

rather than the globally quantified `IntervalDomainLemma41.IntervalDomainInterpolation` field used by the older interpolation-frontier routes.

## Existing preferred theorem chain

The existing theorem has shape:

```lean
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C
```

It assembles the three components of `IntervalDomainPaper2StatementTargets` as follows:

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

That is pure statement wiring. It does not invent a new producer for any frontier package.

## Residual field audit

The preferred data package is:

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

`section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p` still has four genuine analytic residual fields:

```lean
lemma26
lemma27
prop22
prop23
```

The wrapper

```lean
intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
```

already supplies two other section-2 targets from elsewhere:

- `Proposition_2_4 intervalDomain p` is produced by `intervalDomain_Proposition_2_4 p`.
- `Proposition_2_5 intervalDomain p` is supplied from the nested Theorem 1.2/1.3 data as `prop25`, not by `section2`.

Thus the thin section-2 package is genuinely thinner, but not closed.

### `localAndMain.proposition11`

`localAndMain.proposition11` has type:

```lean
IntervalDomainPaper2Proposition11ChiZeroFrontierData p
```

Its remaining field is the finite-horizon alternative. The local-existence slot is produced internally by:

```lean
intervalDomain_localExistence_chiZero_unconditional
```

through:

```lean
intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
```

So this component is partially produced by current code, but the finite-horizon alternative remains a residual.

### `localAndMain.main.theorem12And13`

`localAndMain.main.theorem12And13` has type:

```lean
IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
  p C cGrad
```

It carries:

```lean
common
prop25
globalExtension
slowBootstrap
criticalBootstrap
criticalEventualSupBound
strongBootstrap
strongEventualSupBound
```

The local-existence field present in the non-local-free positive route is produced by:

```lean
IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData.toPositive
```

which fills it using:

```lean
intervalDomain_localExistence_chiZero_unconditional
```

Theorem 1.1 in the main bundle is produced by:

```lean
intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
```

inside:

```lean
intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
```

The remaining `common`, `prop25`, `globalExtension`, bootstrap, and eventual-sup fields are genuine residual/frontier inputs.

### `common`

`common : IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad` remains an analytic solution-slice package. Its residual fields are:

```lean
solutionInterpolation
dissipation
gradConstantPositive
gradientChain
massControl
powerIntegrability
energyFromCrossDiffusion
```

Existing code already converts this package into some statement targets:

- `IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_solution_interpolation_frontier` produces Corollary 2.1 from the solution-slice common fields.
- `intervalDomainPaper2_Lemma_4_1_of_solutionInterpolationFrontier` delegates to `IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_solution_interpolation_frontier` to produce Lemma 4.1 from the solution-slice interpolation field.
- `IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData.toSolution` drops the positive-constant field for routes that only need the non-positive solution-slice package, using `IntervalDomainClassicalSolutionInterpolation_of_positive`.

These are conversions after the package is supplied; they are not producers of the package itself.

## Recommended smallest Lean edit

Add a transparent alias and theorem alias near the preferred theorem in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`. This makes the preferred route explicit without duplicating fields.

When inserted into that file, omit the repeated `import`, `open`, `namespace`, and `end` lines below; keep only the declarations inside the existing namespace/section.

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain

namespace ShenWork.Paper2

noncomputable section

/-- Preferred `χ₀ = 0` interval-domain Paper2 statement-frontier package.

This is a transparent alias for
`IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.
It avoids the refuted global `IntervalDomainInterpolation` route by using the
positive solution-slice interpolation package.  It is still conditional on the
thin section-2 frontiers, finite-horizon alternative, positive solution-slice
interpolation/energy package, `Proposition_2_5`, global extension, bootstrap,
and eventual-sup frontiers. -/
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

## If an even smaller edit is desired

Skip the `abbrev` and add only a theorem alias that takes the existing long data type. That is the absolute smallest Lean edit. The abbreviation is slightly better because it creates a stable preferred-route name without copying any fields.

## Do not add

Do not add a preferred alias that depends on any of:

```lean
IntervalDomainPaper2StatementChiZeroInterpolationFrontierData
IntervalDomainPaper2InterpolationEnergyFrontierData
IntervalDomainLemma41.IntervalDomainInterpolation
```

Those names belong to the refuted global interpolation route and should remain legacy/diagnostic, not preferred headline-facing entry points.
