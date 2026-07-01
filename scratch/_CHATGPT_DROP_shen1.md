# Q2954 (shen1) — short independent headline-residual audit

Repo: `xiangyazi24/Shen_work`  
Audited ref: current main `ff729271c64ad6ab20c0ee099c30cde6037fee02`  
Scope: source audit only; no project source edits.

## Short verdict

Yes: the shen1 classification is materially correct. I found no missing top-level residual field in the three named preferred routes. The only important caveat is regime compatibility: the Paper3 actual-linear-small route assumes `0 < p.χ₀`, so its `paper2Main : IntervalDomainPaper2MainTheoremTargets p C` field is **not** supplied by the Paper2 `χ₀ = 0` route. It remains a separate Paper2-main input for that positive-χ regime.

## 1. Correctness of the listed preferred routes

### Paper1

Path: `ShenWork/Paper1/StatementAssembly.lean`.

The listed route is correct:

* `paper1_mainStatementTargets_of_lowerPinnedContactData`
* `paper1_mainStatementTargets_of_lowerPinnedRawContactData`

The corresponding input records have exactly the listed fields:

```lean
structure Paper1MainStatementLowerPinnedContactData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveLowerPinnedContact : Paper1PositiveLowerPinnedContactBranchData
  mainline : Paper1MainlineExistence cStarStarFn

structure Paper1MainStatementLowerPinnedRawContactData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveLowerPinnedRawContact : Paper1PositiveLowerPinnedRawContactBranchData
  mainline : Paper1MainlineExistence cStarStarFn
```

No top-level Paper1 residual field is missing from shen1's list. The file also has further reductions such as `paper1_positiveContactBranch_of_schauderContactData` and `paper1_positiveRawContactData_of_routeAParamData` in `ShenWork/Paper1/PositiveRawRouteAAssembly.lean`, but these replace one positive-branch residual by smaller route-A/Schauder residuals; they are not unconditional producers of the listed top-level residual.

### Paper2 interval-domain, `χ₀ = 0`

Path: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`.

The listed least-residual route is correct:

```lean
intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
```

Its top-level record is intentionally a one-field wrapper:

```lean
structure
    IntervalDomainPaper2MainTheoremChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
      p C
```

Expanding `theorem12And13`, shen1's list is complete:

```lean
structure
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  prop25RawDropTerminal :
    IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap : ...
  criticalBootstrap : ...
  criticalEventualSupBound : ...
  strongBootstrap : ...
  strongEventualSupBound : ...
```

And `prop25RawDropTerminal` expands exactly as listed:

```lean
structure
    IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
    (p : CM2Params) : Prop where
  rawMoserDrop : ...
  relativeMassGradient : ...
  terminalEndpoint : ...
```

No top-level field is missing. The theorem arguments `hχ0 : p.χ₀ = 0`, `ha : 0 < p.a`, `hb : 0 < p.b`, `hα : 1 ≤ p.α`, and `hγ : 1 ≤ p.γ` are parameter-side hypotheses, not residual frontier fields. Theorem 1.1 and local existence are indeed produced internally by the χ-zero route; they are not residual fields of this preferred wrapper.

### Paper3 actual-linear-small interval-domain route

Paths:

* `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`
* `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`

The listed preferred route is correct:

```lean
intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
```

with input record:

```lean
structure IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
```

Expanding `mainline`, shen1's list is complete:

```lean
structure IntervalDomainPaper3MainlineActualLinear22ThinFrontierData ... where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  theorem22Nonminimal : LinearStabilityInstabilityNonminimalRaw ...
  theorem22Minimal : LinearStabilityInstabilityMinimalRaw ...
  compactness : IntervalDomainPaper3SupNormCompactnessAPosData ...
  stability24 : IntervalDomainPaper3Stability24ActualLinearFrontierData ...
```

Further expansion is also as listed:

```lean
structure IntervalDomainPaper3SupNormCompactnessAPosData ... where
  compact : TimeTranslateCompactnessRaw intervalDomain p locallyConverges
  resolvent : NeumannResolventGradientBoundExistsRaw intervalDomain neumannResolventGradientBound

structure IntervalDomainPaper3Stability24ActualLinearFrontierData ... where
  global24 : ...
  exp24 : ...
```

The negative-sensitivity residual is indeed vacuous in this route, via:

```lean
intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
```

and Theorem 2.1 persistence is produced internally by:

```lean
intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
```

## 2. Missed top-level residual fields?

No. I did not find an omitted top-level residual field in the three preferred routes.

Small clarification: Paper3's `locallyConverges` and `neumannResolventGradientBound` are parameters of `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData`, not record fields. The actual residual fields involving them are `compactness.compact` and `compactness.resolvent`, which shen1 listed.

Also, the parameter-side hypotheses for Paper3 actual-linear-small,

```lean
ha : 0 < p.a
hb : 0 < p.b
hχ0 : 0 < p.χ₀
hm : p.m = 1
hβ : 1 ≤ p.β
hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))
```

are theorem assumptions, not residual fields.

## 3. Any listed residual already produced and only missing one wiring theorem?

Not in a materially useful way.

* Paper1: `Paper1PositiveLowerPinnedRawContactBranchData` can be produced from `Paper1PositiveLowerRawCapRouteAParamData` by `paper1_positiveRawContactData_of_routeAParamData`, but that just shifts the residual to the route-A param/contact package. `ConstructionNegSMPProvider` and `Paper1MainlineExistence` are not produced unconditionally in the preferred route's import graph.
* Paper2: `prop25RawDropTerminal`, `globalExtension`, and the slow/critical/strong bootstrap/eventual-bound fields remain genuine inputs. The route does contain pure conversions (`toTerminalEndpointCor21`, `toMassGradientCor21`, etc.), but no closed theorem producing the listed residual package.
* Paper3: persistence and the negative-sensitivity residual are already produced internally, but they are not among the listed residual fields. The listed fields `paper2Main`, `initialContinuity`, raw Theorem 2.2 nonminimal/minimal, compactness compact/resolvent, and stability24 global/exp remain inputs.

Important caveat: a one-line composition from the Paper2 `χ₀ = 0` route into Paper3's actual-linear-small `paper2Main` field is impossible because the regimes conflict (`p.χ₀ = 0` versus `0 < p.χ₀`). Any Paper3 headline wrapper using this actual-linear-small route must supply `paper2Main` from a Paper2 route valid in the positive-χ regime, or carry it as an input as the current record does.

## 4. Circular or empty packages?

No circular or empty frontier package in these preferred routes, with one caveat about interpretation.

* `IntervalDomainPaper2MainTheoremChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData` is a thin one-field wrapper, but not empty: its single field expands to the real Theorem 1.2/1.3 residual package.
* `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData` is also thin, but not empty: `paper2Main` and `mainline` are real fields.
* `IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25` legitimately fills several branches by contradiction from `0 < p.χ₀` and `0 < p.a`; only `global24` and `exp24` remain non-vacuous.
* `P3MoserAgmonDirectRoute` is sorry-free, but `AgmonNoDropEnergyReductionBefore` is an explicit frontier, not a hidden proof. It is therefore not misleading if treated as a conditional/WIP route, and it is not the preferred live headline route.

Bottom line: shen1's classification is sound. The main thing to avoid saying is that Paper3's actual-linear-small `paper2Main` is supplied by the Paper2 χ-zero theorem route; it is a separate residual because the parameter regimes differ.
