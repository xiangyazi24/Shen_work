# Q2773 shen2: Paper1--3 headline frontier audit after bc64/b81/f950/abd0

Repo target: `xiangyazi24/Shen_work`, Lean 4, default branch `main`.

Baseline supplied by user: full `lake build ShenWork` is clean, true `sorry`/`admit` scan is zero, and declaration-level explicit axiom scan is zero.

Scope honored: no proposed edits to Zinan-owned files:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

Files inspected for this audit:

```text
ShenWork/Paper1/StatementAssembly.lean
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
ShenWork/Paper3/StatementAssembly.lean
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

## Classification key

| Class | Meaning |
|---|---|
| A | Already proved and wired to a current route. |
| B | Proved somewhere, but not yet wired to the relevant preferred headline surface, or only wired to a sibling/older route. |
| C | Real open mathematical/analytic frontier. The package has meaningful fields and is not an empty declaration. |
| D | Pure empty declaration / placeholder. |

## Top-level answer

I did **not** find any pure empty declaration / placeholder among the inspected Paper1--3 headline input packages. The remaining packages are either proved/wiring interfaces or genuine mathematical frontier records with concrete fields. So class **D is empty** for the current inspected headline surfaces.

The largest post-Agmon improvement is already present on main:

```lean
unitIntervalPositiveAgmonInterpolation
intervalDomain_classicalSolutionPositiveInterpolation
IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData.toAgmon
intervalDomainPaper2_statementTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
```

The preferred Paper2 `χ₀ = 0` raw-drop terminal-endpoint mass-gradient route no longer carries `agmon : UnitIntervalPositiveAgmonInterpolation`.

A second post-audit improvement is also already present: Paper3 actual-linear-small has a no-negative-residual route:

```lean
intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
```

That discharges `NegativeSensitivityGlobalEventualBound intervalDomain p` from `0 < p.χ₀` for the thin Paper2-main route.

## Paper1 audit

### A. Already proved and wired

| Name | File | Status |
|---|---|---|
| `paper1_Lemma_2_5` | `ShenWork/Paper1/StatementAssembly.lean` | Closed by `Lemma_2_5_proved`. |
| `paper1_Lemma_2_5_JensenStep` | same | Closed by `Lemma_2_5_JensenStep_proved`. |
| `paper1_lemma25Targets` | same | Bundles the two closed Lemma 2.5 targets. |
| `paper1_positiveCriticalBranch_of_strictBarrier` | same | Pure conversion from strict `MChi` barrier to `ShenUpperBoundPositive`. |
| `paper1_positiveStrictBarrierBranch_of_contactBranch` | same | Pure conversion from no-contact facts to strict barrier. |
| `paper1_positiveContactBranch_of_lowerPinnedContactData` | same | Wires lower-pinned data to contact branch; the tail is produced from the lower pin. |
| `paper1_positiveContactBranch_of_lowerPinnedRawContactData` | same | Same for raw lower pin. |
| `paper1_positiveLowerPinnedContactData_of_schauderContactData` | same | Wires lower-pinned Schauder/contact data to lower-pinned contact data. |

### B. Proved/wiring but not headline-closing by itself

These are useful theorem/data wiring surfaces, not analytic proof producers:

```lean
paper1_mainStatementTargets_of_mainResultsData
paper1_mainStatementTargets_of_smpMainlineData
paper1_mainStatementTargets_of_strictBarrierData
paper1_mainStatementTargets_of_lowerPinnedContactData
paper1_mainStatementTargets_of_lowerPinnedRawContactData
paper1_mainlineStatementTargets_of_mainlineExistence
paper1_lemma51And52Targets_of_frontierData
paper1_propositionTargets_of_frontierData
paper1_combinedStatementTargets_of_data
paper1_combinedStatementTargets_of_strictBarrierData
paper1_combinedStatementTargets_of_lowerPinnedContactData
paper1_combinedStatementTargets_of_lowerPinnedRawContactData
```

They assemble targets once the named frontiers are supplied. They should not be counted as empty declarations.

### C. Real open mathematical frontiers

| Package | Why it is real |
|---|---|
| `Paper1MainResultsData cStarStarFn` | Monolithic main-results data; not constructed in `StatementAssembly`. |
| `ConstructionNegSMPProvider` | Negative branch construction provider for Theorem 1.1. |
| `Paper1PositiveCriticalFrozenStationaryBranch` | Requires positive critical frozen-stationary profile, `ShenUpperBoundPositive`, and sharp right-tail asymptotic. |
| `Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch` | Replaces upper bound by strict `MChi` barrier, but still needs strict comparison and tail asymptotics. |
| `Paper1PositiveCriticalFrozenStationaryContactBranch` | Needs local no-contact facts and tail asymptotics. |
| `Paper1PositiveLowerPinnedContactBranchData` / `Paper1PositiveLowerPinnedRawContactBranchData` | Lower-pinned profile plus no-contact data; real construction/no-contact residual. |
| `Paper1PositiveLowerPinnedSchauderContactData` / `Paper1PositiveLowerPinnedCapSchauderContactData` | Schauder principle/map data, stationarity, flat-left identification, and no-contact facts. |
| `Paper1MainlineExistence cStarStarFn` | Mainline existence/stability package for Theorems 1.2 and 1.3. |
| `Paper1Lemma51FrontierData` | Resolvent identity, continuity, derivative tending to zero, derivative bounds. |
| `Paper1Lemma52FrontierData` | Monotonicity frontier for Lemma 5.2. |
| `Paper1PropositionFrontierData` | Whole-line Cauchy existence, bounds, and convergence frontiers. |

### D. Empty declarations/placeholders

None found in the inspected Paper1 statement/headline route. The remaining inputs are `structure`/`def : Prop` packages with concrete mathematical fields.

## Paper2 audit

### A. Already proved and wired

| Name | File | Status |
|---|---|---|
| `unitIntervalPositiveAgmonInterpolation` | `ShenWork/PDE/IntervalAgmonInterpolation.lean` | Proved; user reports axiom print only standard classical/propext/quot. |
| `intervalDomain_classicalSolutionPositiveInterpolation` | same | Proved and usable as the positive solution-slice interpolation field. |
| `IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData.toAgmon` | `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` | Fills old `agmon` field using `unitIntervalPositiveAgmonInterpolation`. |
| `intervalDomainPaper2_statementTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData` | same | Preferred post-Agmon statement wrapper. |
| `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` | same | Theorem 1.1 in proved `χ₀ = 0` route, no half-step frontier package. |
| `intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData` | same | Local existence part is discharged internally by `intervalDomain_localExistence_chiZero_unconditional`; finite-horizon alternative remains. |
| `intervalDomain_Proposition_2_4` as used in `intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData` | same | Prop. 2.4 supplied by interval-domain mass proof. |
| `intervalDomainPaper2_Lemma_3_1` | same | Closed by `Lemma31Closure.Lemma_3_1_intervalDomain`. |
| `intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier` | same | With the proved positive solution-slice interpolation, Lemma 4.1/a-priori package is no longer an Agmon residual. |

### A/B wiring surfaces that are correct and should be used

These wrappers collapse lower-level Moser/frontier records into theorem targets; they are not empty placeholders.

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.toTerminalEndpoint
IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData.toMassGradient
IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms
intervalDomainPaper2_Proposition_2_5_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData
intervalDomainPaper2_Corollary_2_1_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData
intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
```

### B. Proved somewhere but not wired to all preferred consumers

| Proved/wired fact | Gap |
|---|---|
| `IntervalDomainPaper2StatementTargets p C` contains the main theorem package as its third component. | Paper3 no-negative routes often want `IntervalDomainPaper2MainTheoremTargets p C` directly. A small extractor from preferred Paper2 statement data to Paper2 main targets would reduce duplication for downstream Paper3 consumers. |
| `unitIntervalPositiveAgmonInterpolation` and `intervalDomain_classicalSolutionPositiveInterpolation` | Wired to the preferred proved-Agmon route, but older `...AgmonFrontierData` and `...PositiveSolutionInterpolation...` routes remain as compatibility surfaces. They are not preferred headline residuals. |
| `intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData` | Local existence is wired internally, but the finite-horizon alternative is still a real residual. |

### C. Real open mathematical frontiers

Current preferred Paper2 full statement data:

```lean
structure
  IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
  (p : CM2Params) (C : Paper2Constants p) : Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData p C
```

Unfolding those fields, the real residuals are:

| Residual | Exact names / fields | Suggested owner/file family |
|---|---|---|
| Thin section-2 estimates | `IntervalDomainPaper2BootstrapEstimateThinFrontierData.lemma26`, `.lemma27`, `.prop22`, `.prop23` | Paper2 estimate/PDE files. Non-Zinan. Likely around interval Lp/bootstrap/signal estimate files. |
| Finite-horizon alternative | `IntervalDomainPaper2Proposition11ChiZeroFrontierData.finiteHorizonAlternative` | Paper2 continuation/existence side. Non-Zinan. |
| Global extension | `IntervalDomainPaper2GlobalExtensionFrontier p` | Paper2 continuation/globalization; likely `IntervalDomainTheorem11*`, `IntervalDomainAPrioriGlobal`, or nearby continuation files. |
| Raw Moser drop | `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.rawMoserDrop` | Moser energy/dissipation side. Non-Zinan wrappers can live in `P3MoserDissipationShape.lean`, `P3MoserLemmaDischarge.lean`, or `P3MoserLemmas.lean`. Do not edit Zinan producer files. |
| Relative mass-gradient package | `...relativeMassGradient` in the same raw-drop terminal endpoint package | Moser mass-gradient / interpolation algebra side. Agmon is now closed, so remaining obstruction is gradient-chain/mass/lower-order data, not uniform Agmon. |
| Terminal endpoint | `...terminalEndpoint` in the same package | Real Moser endpoint / pointwise-power-control frontier. If the proof requires high-excursion/window/threshold producers, that part is Zinan-owned. Non-Zinan work should only add wrappers around already-exported outputs. |
| Branch bootstrap seeds | `slowBootstrap`, `criticalBootstrap`, `strongBootstrap` in the `ChiZero...Cor21LocalFreeFrontierData` families | Paper2 bootstrap/global boundedness. Some subgoals may depend on Zinan-owned Moser producers; avoid editing those files. |
| Eventual sup bounds | `criticalEventualSupBound`, `strongEventualSupBound` | Long-time/global boundedness. Non-Zinan theorem assembly okay; hard Moser/high-excursion producer work belongs to the relevant owner. |

### D. Empty declarations/placeholders

None found in the inspected Paper2 preferred statement route. The remaining packages have substantive fields; they are not vacuous declarations.

## Paper3 audit

### A. Already proved and wired

| Name | File | Status |
|---|---|---|
| `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall` | `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` | Persistence package produced internally by `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`. |
| `intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall` | same | Same, with named parts. |
| `intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall` | same | Sectorial-constant version of actual-linear persistence. |
| `IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25` | same | Vacates Theorem 2.3 branches by `0 < χ₀` and Theorem 2.5 branches by `0 < a`; only Theorem 2.4 frontiers remain. |
| `intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos` | same | Proves `NegativeSensitivityGlobalEventualBound intervalDomain p` from `0 < p.χ₀` by contradiction. |
| `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData` | same | Removes separate negative-sensitivity field from the thin Paper2-main actual-linear route. |
| `intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData` | same | Full Paper3 statement target from Paper2 main theorem targets and thin actual-linear mainline, with negative sensitivity discharged. |
| `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.to_coreExistence` | same | Produces sectorial core existence from actual-linear a-priori facts plus actual-linear persistence. |
| `intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData` | same | Wires a-priori actual-linear mainline data to Paper3 mainline targets. |

### B. Proved somewhere but not wired to preferred headline

| Proved fact / route | Current gap |
|---|---|
| `intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos` | It is wired to `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData`, but the a-priori actual-linear statement route `IntervalDomainPaper3StatementAprioriActualLinearSmallFrontierData` still takes `propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C`, which carries a negative-sensitivity field through `proposition12And14`. |
| Paper2 main targets imply Paper3 Proposition 1.3/1.4 via `paper3_Proposition_1_3_of_Paper2_Theorem_1_3` and `paper3_Proposition_1_4_of_Paper2_Theorem_1_2`. | The a-priori actual-linear Paper3 statement route has no `P2MainNoNeg` variant yet. |
| `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.to_coreExistence` | It is wired to a-priori mainline, but not yet combined with the no-negative Paper2-main proposition route. |

### C. Real open mathematical frontiers

| Residual | Exact names / fields | Suggested owner/file family |
|---|---|---|
| Paper2 main theorem input for Paper3 | `paper2Main : IntervalDomainPaper2MainTheoremTargets p C` in `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData` | Paper2 route; use preferred proved-Agmon `χ₀ = 0` only when parameters match. Actual-linear small has `0 < χ₀`, so it needs a positive-sensitivity Paper2 main theorem route. |
| Initial continuity | `IntervalDomainInitialContinuityRaw p` inside `IntervalDomainPaper3CoreStatementActualLinear22Data` / thin mainline data | Paper3 stability/initial-continuity files. Non-Zinan. |
| Raw linear Theorem 2.2 | `LinearStabilityInstabilityNonminimalRaw ...`, `LinearStabilityInstabilityMinimalRaw ...` | Paper3 linear/sectorial stability owner. Non-Zinan unless otherwise assigned. |
| Compactness | `IntervalDomainPaper3SupNormCompactnessAPosData.compact : TimeTranslateCompactnessRaw ...` | Paper3 compactness/regularization side. |
| Resolvent gradient bound | `IntervalDomainPaper3SupNormCompactnessAPosData.resolvent : NeumannResolventGradientBoundExistsRaw ...` | Paper3 elliptic/sectorial support. |
| Theorem 2.4 stability | `IntervalDomainPaper3Stability24ActualLinearFrontierData.global24`, `.exp24` | Paper3 nonlinear stability/convergence side. These are the non-vacuous actual-linear stability fields. |
| A-priori sectorial facts | `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.spectralSemigroupOrbitBound`, `.continuation`, `.massLpSmoothing` | Paper3/Paper2 a-priori global existence route. `massLpSmoothing` eventually depends on Moser residuals. Do not edit Zinan-owned producer files. |
| Moser actual-linear small residuals | `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals` fields: `closedEnergyTrace`, `rawMoserDrop`, `relativeMassGradient`, `terminalPointwise`, plus boundedness core | Paper3/Paper2 Moser wrappers. High-excursion/threshold production, if needed, is Zinan-owned. |

### D. Empty declarations/placeholders

None found in the inspected Paper3 statement/headline route. The generic `RawData`, `BranchData`, and `FrontierData` packages are theorem-input structures with concrete fields, not empty declarations.

## Summary table across papers

| Paper | A: closed/wired | B: proved but not wired everywhere | C: real frontier | D: empty placeholder |
|---|---|---|---|---|
| Paper1 | Lemma 2.5/Jensen; positive-branch normalization and lower-pinned wiring | Main/combined wrappers are only wiring | Construction, no-contact, Schauder/contact, mainline, Lemma 5, Cauchy frontiers | None found |
| Paper2 | Agmon; positive solution interpolation; `χ₀ = 0` Theorem 1.1/local existence; Prop. 2.4; Lemma 3.1; proved-Agmon preferred statement wrapper | Extractors from preferred statement data to Paper2 main targets would help downstream Paper3 | Thin section-2, finite-horizon alternative, global extension, raw-drop/mass-gradient/terminal endpoint, branch bootstraps, eventual sup bounds | None found |
| Paper3 | Actual-linear persistence; negative-sensitivity vacuity under `0 < χ₀`; thin P2Main no-neg route | No-neg/P2Main not yet wired to a-priori actual-linear statement route | Paper2 main target for matching regimes, initial continuity, raw linear T2.2, compactness/resolvent, T2.4 stability, a-priori/massLp/Moser residuals | None found |

## Recommended next lowest-conflict non-Zinan patch

Implement a no-negative Paper2-main variant for the **a-priori actual-linear** Paper3 statement route.

Why this is the best next patch:

1. It touches only `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.
2. It reuses already-proved `intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos`.
3. It reuses already-proved Paper2-to-Paper3 proposition bridges:
   ```lean
   paper3_Proposition_1_4_of_Paper2_Theorem_1_2
   paper3_Proposition_1_3_of_Paper2_Theorem_1_3
   ```
4. It avoids Zinan-owned Moser producer files.
5. It removes a remaining unnecessary negative-sensitivity/proposition wrapper from the a-priori actual-linear headline route.

### Patch sketch

Append this in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` near the existing no-negative thin-P2Main route or near the a-priori route.

```lean
/-- Full interval-domain Paper3 statement frontiers in the actual-linear-small
regime, using Paper2 main theorem targets for Proposition 1.3/1.4 and discharging
negative sensitivity from `0 < χ₀`. -/
structure IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData
      p M0 uBar vLower K

/-- A-priori actual-linear-small Paper3 statement target from Paper2 main theorem
targets, with the negative-sensitivity residual discharged by `0 < χ₀`. -/
theorem
    intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { proposition12And14 :=
            { negativeBound :=
                intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
                  p hχ0
              criticalExistence :=
                paper3_Proposition_1_4_of_Paper2_Theorem_1_2
                  hData.paper2Main.2.1 }
          theorem13 := hData.paper2Main.2.2 }
      mainline := hData.mainline }

/-- Instance-facing a-priori actual-linear-small Paper3 statement target from
Paper2 main theorem targets, with no separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out
```

Expected imports: none if appended to the same file. If placed in a new file, import:

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

### Secondary optional Paper2-only patch

Add an extractor from preferred proved-Agmon Paper2 statement data to Paper2 main theorem targets, useful for Paper3 consumers that only need `IntervalDomainPaper2MainTheoremTargets p C`.

```lean
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  (intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData
    p C hχ0 ha hb hα hγ hData.localAndMain).2
```

This is also non-Zinan and low conflict, but the Paper3 a-priori no-negative wrapper reduces headline assumptions more directly.
