# Q2802 shen2: current frontier landscape and next wrapper step

Repo target: `xiangyazi24/Shen_work`, default branch `main`.

Scope honored: I did not propose edits to Zinan-owned producer files:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

Files inspected directly:

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
ShenWork/Paper1/StatementAssembly.lean
```

I treat Q2802 as the active request; Q2781's Paper1--3 classification is folded in where relevant.

## 1. Headline-facing fronts that are pure wrappers / already wireable

### Paper2: Agmon and positive solution interpolation are closed

The following are now proved/wired and should be considered stale as future suggestions:

```lean
unitIntervalPositiveAgmonInterpolation
intervalDomain_classicalSolutionPositiveInterpolation
intervalDomainPaper2_Lemma_4_1_of_provedAgmon
intervalDomainPaper2_aprioriTargets_of_provedAgmon
```

The preferred raw-drop terminal-endpoint mass-gradient route no longer carries Agmon as an assumption. The current wrapper chain is already present:

```lean
IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData.toAgmon

intervalDomainPaper2_statementTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
```

The local/main and main theorem extractors from that full statement route are also already present:

```lean
intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData

intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
```

The preferred aliases are also present:

```lean
IntervalDomainPaper2PreferredChiZeroStatementActualAtomRawDropMassGradientTerminalEndpointCor21ProvedAgmonFrontierData

intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomRawDropMassGradientTerminalEndpointCor21ProvedAgmonFrontierData
```

So any recommendation to add the proved-Agmon Paper2 statement route or its main extractors is stale.

### Paper2: theorem/data conversions already wired

These are pure wrappers, not analytic producers:

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.toTerminalEndpoint
IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData.toMassGradient
IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms

intervalDomainPaper2_Proposition_2_5_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData
intervalDomainPaper2_Corollary_2_1_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData

IntervalDomainPaper2Theorem12And13ChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData.toTerminalEndpointCor21
IntervalDomainPaper2MainTheoremChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData.toTerminalEndpointCor21
```

They should be used as wrappers around lower-level atoms, not counted as open headline assumptions.

### Paper3: NoNeg and actual-linear wrapper families are already landed

The following suggestions are now stale because the declarations exist on `main`:

```lean
intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos

IntervalDomainPaper3StatementActualLinear22P2MainNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22P2MainNoNegData

IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData

IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData

IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainNoNegData

IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainNoNegData

IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData

IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainNoNegData

IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainNoNegData

IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainNoNegData
```

These are all pure statement-layer assumption cleanup: `0 < p.χ₀` discharges `NegativeSensitivityGlobalEventualBound intervalDomain p`, and Paper2 main targets supply Paper3 Proposition 1.3/1.4.

### Paper1: only Lemma 2.5 is closed at headline level

Already closed and wired:

```lean
paper1_Lemma_2_5
paper1_Lemma_2_5_JensenStep
paper1_lemma25Targets
```

The remaining Paper1 headline packages are not empty declarations, but most are genuine frontiers rather than mere wrapper work.

## 2. Genuine analytic producers / open atoms

### Paper2 genuine frontiers

These should not be renamed as wrappers; they are real math/PDE obligations.

```lean
IntervalDomainPaper2BootstrapEstimateThinFrontierData.lemma26
IntervalDomainPaper2BootstrapEstimateThinFrontierData.lemma27
IntervalDomainPaper2BootstrapEstimateThinFrontierData.prop22
IntervalDomainPaper2BootstrapEstimateThinFrontierData.prop23
```

These are the thin Section 2 estimate package.

```lean
IntervalDomainPaper2Proposition11ChiZeroFrontierData.finiteHorizonAlternative
```

Local existence is already discharged in the `χ₀ = 0` route, but finite-horizon continuation/alternative is still genuine.

The current preferred Prop. 2.5/Moser atoms remain genuine:

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.rawMoserDrop
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.relativeMassGradient
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.terminalEndpoint
```

The Theorem 1.2/1.3 branch/global fronts remain genuine:

```lean
IntervalDomainPaper2GlobalExtensionFrontier
slowBootstrap
criticalBootstrap
criticalEventualSupBound
strongBootstrap
strongEventualSupBound
```

Those field names occur in the `IntervalDomainPaper2Theorem12And13...` / preferred `ChiZero...LocalFree...` route families.

### Paper3 genuine frontiers

Current actual-linear routes have many wrapper layers, but these fields are still real frontiers:

```lean
IntervalDomainPaper3CoreStatementActualLinear22Data.initialContinuity
IntervalDomainPaper3CoreStatementActualLinear22Data.theorem22Nonminimal
IntervalDomainPaper3CoreStatementActualLinear22Data.theorem22Minimal
```

For a-priori/mainline routes:

```lean
IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.spectralSemigroupOrbitBound
IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.continuation
IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.massLpSmoothing

IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData.compactness
IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData.stability
```

For terminal/lower-upper Moser surfaces:

```lean
IntervalDomainMoserActualLinearSmallBoundednessCore.alphaAbsorption
IntervalDomainMoserActualLinearSmallBoundednessCore.gammaDimension

IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.closedEnergyTrace
IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.rawMoserDrop
IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.relativeMassGradient
IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.terminalPointwise

IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.integratedStep

IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.classicalContinuityRegularity
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.integratedDissipation
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.relativeMoserInterpolation
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.lowerAverage
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.upperDataGap
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.quantitativeEndpoint

IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals.lowerUpperFrontiers
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals.quantitativeEndpoint
```

If a proof route for `lowerAverage`, `upperDataGap`, `lowerUpperFrontiers`, or `terminalPointwise` needs the high-excursion/threshold producers, that part belongs to Zinan. Non-Zinan work should remain wrapper/assembly around already-exported facts.

The non-vacuous stability frontiers in the actual-linear-small route are:

```lean
IntervalDomainPaper3Stability24ActualLinearFrontierData.global24
IntervalDomainPaper3Stability24ActualLinearFrontierData.exp24
```

`toStability23To25` already makes the Theorem 2.3 and 2.5 branches vacuous from `0 < p.χ₀` and `0 < p.a`, so only those Theorem 2.4 fields are real.

### Paper1 genuine frontiers

The current Paper1 residuals are real mathematical fronts:

```lean
Paper1MainResultsData
ConstructionNegSMPProvider
Paper1PositiveCriticalFrozenStationaryBranch
Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
Paper1PositiveCriticalFrozenStationaryContactBranch
Paper1PositiveLowerPinnedContactBranchData
Paper1PositiveLowerPinnedRawContactBranchData
Paper1PositiveLowerPinnedSchauderContactData
Paper1PositiveLowerPinnedCapSchauderContactData
Paper1MainlineExistence
Paper1Lemma51FrontierData
Paper1Lemma52FrontierData
Paper1PropositionFrontierData
```

For example, `Paper1Lemma51FrontierData` carries real fields such as `resolvent`, `continuous`, `deriv_tends`, `deriv_bound`, and `deriv_exp`; `Paper1PropositionFrontierData` carries whole-line Cauchy existence/bounds/convergence fields. These are not empty placeholders.

## 3. Next low-risk wrapper to add

The best current non-producer cleanup is a generic Paper2 projection from the full statement bundle to its local/main and main theorem components.

Why this is still useful despite the route-specific extractors already landed:

* The route-specific proved-Agmon extractors exist, but downstream Paper3 routes only need `IntervalDomainPaper2MainTheoremTargets p C`.
* `IntervalDomainPaper2StatementTargets p C` already contains that target as a nested component.
* A generic projector avoids adding a new route-specific extractor every time a statement route changes.
* It is pure structure projection, no new analysis, no producer files.

Insert in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` immediately after the definition of `IntervalDomainPaper2StatementTargets` or near the other statement-target wrappers.

```lean
/-- Extract the local-plus-main theorem targets from the full interval-domain
Paper 2 statement bundle.  This is pure projection. -/
theorem intervalDomainPaper2_localAndMainTheoremTargets_of_statementTargets
    {p : CM2Params} {C : Paper2Constants p}
    (h : IntervalDomainPaper2StatementTargets p C) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  h.2.2

/-- Extract the Paper 2 main theorem targets from the full interval-domain
statement bundle.  This lets downstream Paper3 wrappers consume any completed
Paper2 statement route without knowing which lower-level route produced it. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_statementTargets
    {p : CM2Params} {C : Paper2Constants p}
    (h : IntervalDomainPaper2StatementTargets p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  h.2.2.2

/-- Instance-facing local-plus-main extractor from a full Paper2 statement
bundle. -/
theorem intervalDomainPaper2_localAndMainTheoremTargets_of_statementTargetsFact
    (p : CM2Params) (C : Paper2Constants p)
    [h : Fact (IntervalDomainPaper2StatementTargets p C)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_statementTargets h.out

/-- Instance-facing main theorem extractor from a full Paper2 statement bundle. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_statementTargetsFact
    (p : CM2Params) (C : Paper2Constants p)
    [h : Fact (IntervalDomainPaper2StatementTargets p C)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_statementTargets h.out
```

Expected result: this should compile by projection only. No extra imports if appended to `IntervalDomainStatementAssembly.lean`.

### Optional follow-up wrapper using the projector

After the projector exists, Paper3 can add statement-consuming variants without knowing the Paper2 route. For example, for the thin lower/upper route:

```lean
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2StatementNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Statement : IntervalDomainPaper2StatementTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
```

Then its theorem simply calls the already-landed
`intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainNoNegData`, feeding
`intervalDomainPaper2_mainTheoremTargets_of_statementTargets hData.paper2Statement`.

This follow-up is also pure wiring, but the generic Paper2 projector is the better first patch because it helps all Paper3 P2Main wrappers.

## 4. Prioritized actionable non-producer tasks

| Priority | Task | Provable by wiring? | File | Notes |
|---:|---|---:|---|---|
| 1 | Add `intervalDomainPaper2_localAndMainTheoremTargets_of_statementTargets` and `intervalDomainPaper2_mainTheoremTargets_of_statementTargets` plus Fact wrappers. | Yes | `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` | Best low-risk cleanup. Pure projection from `IntervalDomainPaper2StatementTargets`. |
| 2 | Add Paper3 P2Statement-consuming NoNeg wrappers, starting with `IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2StatementNoNegData`. | Yes, after task 1 | `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` | Avoids requiring downstream callers to extract Paper2 main theorem targets manually. |
| 3 | Add analogous P2Statement-consuming variants for `...CETerminalP2MainNoNegData` and `...IntegratedStepP2MainNoNegData`. | Yes, after task 1 | Same Paper3 file | Repetitive but useful if those routes are used by current campaigns. |
| 4 | Add Paper1 projection helpers from `Paper1CombinedStatementTargets` to main/proposition/lemma bundles. | Yes | `ShenWork/Paper1/StatementAssembly.lean` | Very low risk, but lower value than Paper2/Paper3. |
| 5 | Do **not** attempt to prove `IntervalDomainPaper2BootstrapEstimateThinFrontierData` or Paper3 Moser frontiers as a wrapper patch. | No | N/A | These are genuine analytic fronts; high-excursion/threshold parts may be Zinan-owned. |

## 5. Explicit stale suggestions already covered

Do not suggest these again:

```lean
-- Agmon / positive solution interpolation
unitIntervalPositiveAgmonInterpolation
intervalDomain_classicalSolutionPositiveInterpolation
intervalDomainPaper2_Lemma_4_1_of_provedAgmon
intervalDomainPaper2_aprioriTargets_of_provedAgmon

-- Paper2 proved-Agmon full statement route and extractors
IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData.toAgmon
intervalDomainPaper2_statementTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomRawDropMassGradientTerminalEndpointCor21ProvedAgmonFrontierData

-- Paper2 proved-positive local-free route, per current landed wrappers
intervalDomainPaper2_statementTargets_of_chiZeroProvedPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData

-- Paper3 NoNeg routes
intervalDomain_paper3_statementTargets_of_actualLinear22P2MainNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainNoNegData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainNoNegData
```

## Bottom line

The next non-producer patch should not target Agmon, NoNeg, or route-specific Paper2 main extractors; those are already landed. The highest-signal remaining pure wrapper is a generic projection from any completed `IntervalDomainPaper2StatementTargets p C` to `IntervalDomainPaper2MainTheoremTargets p C`, followed by optional Paper3 wrappers that accept a full Paper2 statement bundle instead of a manually extracted Paper2 main bundle.
