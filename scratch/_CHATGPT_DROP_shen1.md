# Q2950 (shen1) — headline residual audit at `ff729271`

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Audited source ref: `ff729271c64ad6ab20c0ee099c30cde6037fee02`  
Scope: source audit only; no project code edits.

## Classification legend

* **A — produced / wiring:** current imported source contains a theorem or pure conversion that produces the item, so the remaining work is parameter plumbing or choosing the wrapper.
* **B — reduced frontier:** the item is not closed, but source has reduced it to smaller named atoms/frontiers.
* **C — genuine open analytic/frontier assumption:** the item is still an actual mathematical/PDE/formalization input in current Lean.
* **D — historical / alternative / no-go route:** useful for documentation or older experiments, but not the least-residual live headline route.

The clean proof-term scan and green builds are good news, but they do **not** mean the headline theorems are unconditional. The statement files are mostly honest conditional assembly layers.

## 1. Paper 1 statement assembly

Path: `ShenWork/Paper1/StatementAssembly.lean`.

### Current preferred / least-residual route

The source exposes several progressively thinner Paper1 main-statement packages. The most relevant live wrappers are:

* `paper1_mainStatementTargets_of_smpMainlineData`
  from `Paper1MainStatementSMPMainlineData`.
* `paper1_mainStatementTargets_of_strictBarrierData`
  from `Paper1MainStatementStrictBarrierData`.
* `paper1_mainStatementTargets_of_lowerPinnedContactData`
  from `Paper1MainStatementLowerPinnedContactData`.
* `paper1_mainStatementTargets_of_lowerPinnedRawContactData`
  from `Paper1MainStatementLowerPinnedRawContactData`.

The preferred least-residual family is the lower-pinned/contact family: it keeps Theorem 1.1 on the weakened negative construction provider plus a reduced positive branch, and keeps Theorems 1.2/1.3 on the mainline package.

The most explicit top-level wrapper in the file is:

```lean
paper1_mainStatementTargets_of_lowerPinnedContactData
  (hData : Paper1MainStatementLowerPinnedContactData cStarStarFn) :
  Paper1MainStatementTargets
```

with raw variant:

```lean
paper1_mainStatementTargets_of_lowerPinnedRawContactData
  (hData : Paper1MainStatementLowerPinnedRawContactData cStarStarFn) :
  Paper1MainStatementTargets
```

### Remaining inputs and classification

For `Paper1MainStatementLowerPinnedContactData`:

* `constructionNeg : ConstructionNegSMPProvider` — **C**. The statement assembly imports and consumes this provider; it does not construct it.
* `positiveLowerPinnedContact : Paper1PositiveLowerPinnedContactBranchData` — **B/C**. This is a reduced positive-branch package. It removes the separate tail asymptotic field by preserving a lower pin and rate cover, but the producer field remains analytic.
* `mainline : Paper1MainlineExistence cStarStarFn` — **C**. Theorem 1.2/1.3 mainline existence/stability package is consumed, not produced.

For `Paper1PositiveLowerPinnedContactBranchData`, the residual is:

* `produce : ... ∃ κtilde D U, ... FrozenStationaryWaveProfile ... InLowerPinnedMonotoneTrap ... PositiveUpperBarrierContactContradictions ...` — **B/C**. The route has reduced the positive branch to a lower-pinned profile plus local no-contact facts. The wrapper `paper1_positiveContactBranch_of_lowerPinnedContactData` then produces the old `Paper1PositiveCriticalFrozenStationaryContactBranch` and discharges the tail using `lowerPinnedMonotoneTrap_tail_family_for_branch`.

For the raw version `Paper1PositiveLowerPinnedRawContactBranchData`:

* `produce : ... InLowerPinnedMonotoneTrap ... (lowerBarrierRaw ...) ... PositiveUpperBarrierContactContradictions ...` — **B/C**. Same status; the raw lower-barrier tail is discharged by `paper1_positiveContactBranch_of_lowerPinnedRawContactData`.

For the Schauder-reduced positive branch:

* `Paper1PositiveLowerPinnedSchauderContactData` — **B/C**. The source comments call this the shortest current route through existing lower-pinned fixed-point machinery. Its fields include `LocalUniformSchauderFixedPointPrinciple`, `FrozenStationaryMapSchauderData`, stationary/flat-left identification, and no-contact facts. The theorem `paper1_positiveLowerPinnedContactData_of_schauderContactData` turns it into `Paper1PositiveLowerPinnedContactBranchData`.

Already-produced pieces:

* `paper1_lemma25Targets` — **A**. `paper1_Lemma_2_5` and `paper1_Lemma_2_5_JensenStep` are closed by `Lemma_2_5_proved` and `Lemma_2_5_JensenStep_proved`.
* Pure conversions such as `paper1_positiveCriticalBranch_of_strictBarrier`, `paper1_positiveStrictBarrierBranch_of_contactBranch`, `paper1_positiveContactBranch_of_lowerPinnedContactData`, and `paper1_positiveContactBranch_of_schauderContactData` — **A** once their input packages are supplied.

Historical / non-preferred alternatives:

* `paper1_mainStatementTargets_of_mainResultsData` consuming `Paper1MainResultsData` — **D** for headline accounting. It is a monolithic conditional package.
* `Paper1MainStatementStrictBarrierData` — **B/D** relative to the lower-pinned route. It is still honest, but carries the strict-barrier branch directly.
* `Paper1Lemma51FrontierData` and `Paper1Lemma52FrontierData` — **C** lemma-level frontier records in the same assembly file, not closed producers. They are not the least-residual main-statement route.

### Empty or circular-looking packages

`Paper1MainStatementSMPMainlineData`, `Paper1MainStatementLowerPinnedContactData`, and the raw variant are thin wrapper records, but not circular: their fields are real external frontier packages. They do not pretend to prove the fields they carry.

## 2. Paper 2 interval-domain statement assembly

Path: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`.

### Current preferred / least-residual main route

For the `χ₀ = 0` interval-domain headline route, the least-residual named main theorem wrapper is:

```lean
intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
```

It consumes:

```lean
IntervalDomainPaper2MainTheoremChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData p C
```

and proves:

```lean
IntervalDomainPaper2MainTheoremTargets p C
```

under the explicit parameter hypotheses:

```lean
hχ0 : p.χ₀ = 0
ha  : 0 < p.a
hb  : 0 < p.b
hα  : 1 ≤ p.α
hγ  : 1 ≤ p.γ
```

This route is preferred because:

* Theorem 1.1 is produced internally by `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional`.
* The Theorem 1.2/1.3 local-existence slot is produced internally by `intervalDomain_localExistence_chiZero_unconditional`.
* Corollary 2.1 and Proposition 2.5 are produced from actual Moser atoms.
* The relative-Moser input is reduced to mass-gradient data.
* The endpoint is reduced to terminal pointwise control.
* The Moser dissipation input is lowered to raw physical-drop data.

### Remaining input structure and fields

The top-level input is only:

```lean
structure IntervalDomainPaper2MainTheoremChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData p C
```

This is a wrapper-only record. The real residuals are in the `theorem12And13` field:

```lean
structure IntervalDomainPaper2Theorem12And13ChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
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

Classifications:

* `prop25RawDropTerminal` — **B**. This is a reduced Proposition 2.5 / Corollary 2.1 package. It is not closed, but it is smaller than the old monolithic `Proposition_2_5` input.
* `globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p` — **C**. This is the continuation/globalization principle from bounded finite-time classical solutions.
* `slowBootstrap` — **C**. Supplies the finite-horizon bootstrap output for the slow-diffusion branch.
* `criticalBootstrap` — **C**. Supplies finite-horizon bootstrap output in the `m = 1`, small-χ branch.
* `criticalEventualSupBound` — **C**. Turns all finite-horizon bootstrap outputs into eventual sup-bound for the critical global solution.
* `strongBootstrap` — **C**. Supplies finite-horizon bootstrap output under `StrongLogisticCondition`.
* `strongEventualSupBound` — **C**. Turns all finite-horizon bootstrap outputs into eventual sup-bound under the strong logistic regime.

The reduced Proposition 2.5 atom package expands as:

```lean
structure IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
    (p : CM2Params) : Prop where
  rawMoserDrop : ...
  relativeMassGradient : ...
  terminalEndpoint : ...
```

Classifications:

* `rawMoserDrop` — **C**. This is still a raw pointwise physical-drop frontier. The conversion `toTerminalEndpoint` packages it into `MoserDissipationDropBeforeNonnegB`, but does not prove it.
* `relativeMassGradient` — **B/C**. It is a reduced relative-Moser frontier. The conversion `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms` uses `P3MoserLemmas.intervalDomain_relativeMoserInterpolationBefore_of_massGradient`, but the mass-gradient interpolation, gradient comparison, and lower-order mass-to-current-`Lp` control remain inputs.
* `terminalEndpoint` — **C**. This is still an endpoint pointwise-control frontier, though smaller than the earlier quantitative root-tower endpoint.

Already-produced or internally wired pieces in this preferred route:

* `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` — **A** for Theorem 1.1 in the stated `χ₀ = 0`, `a,b>0`, `α,γ≥1` regime.
* `intervalDomain_localExistence_chiZero_unconditional` — **A** for local existence in the local-free Theorem 1.2/1.3 route.
* `intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData` — **A** once `prop25RawDropTerminal` is supplied.
* `intervalDomain_Proposition_2_4 p` — **A** in the thin section-2 wrapper `intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData`.
* `intervalDomainPaper2_aprioriTargets_of_provedAgmon` — **A** for `Lemma_3_1 ∧ Lemma_4_1` on the interval domain.

### Other Paper2 routes and status

#### Section 2 / Proposition 2.5 routes

* `IntervalDomainPaper2BootstrapEstimateThinFrontierData` — **C** for `lemma26`, `lemma27`, `prop22`, `prop23`; Proposition 2.4 can be filled by `intervalDomain_Proposition_2_4 p`, and Proposition 2.5 can be supplied by one of the Moser routes.
* `IntervalDomainPaper2Prop25ActualAtomFrontierData` — **B/C**. Fields: `moserDissipation`, `relativeMoserInterpolation`, `quantitativeEndpoint`.
* `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData` — **B/C**. Reduces `relativeMoserInterpolation` to `relativeMassGradient` but still carries `moserDissipation` and `quantitativeEndpoint`.
* `IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData` — **B/C**. Reduces endpoint to `terminalEndpoint`; still carries nonnegative-B Moser dissipation and relative mass-gradient data.
* `IntervalDomainPaper2Prop25IntegratedStepFrontierData` — **B/D** for the preferred headline route. Fields: `integratedStep`, `quantitativeEndpoint`.
* `IntervalDomainPaper2Prop25IntegratedMoserFrontierData` — **B/D**. Fields: `classicalRegularity`, `integratedDissipation`, `relativeMoserInterpolation`, `quantitativeEndpoint`; converted to integrated-step data by `toIntegratedStepFrontierData`.
* `IntervalDomainPaper2Prop25LowerUpperFrontierData` — **B/D**. Fields: `lowerUpperFrontiers`, `quantitativeEndpoint`; converted to the integrated-step route.

#### Theorem 1.2/1.3 common-data routes

* `IntervalDomainPaper2Theorem12And13InterpolationFrontierData` — **D** for headline use. It carries the deprecated/no-go global `IntervalDomainInterpolation` premise, explicitly marked refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.
* `IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData` — **B/C**. Avoids false global interpolation but carries solution-slice interpolation and the common energy/dissipation/mass/power fields.
* `IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData` — **B/C**. Positive solution-slice version, suitable for Lemma 4.1 and Corollary 2.1.
* `IntervalDomainPaper2Theorem12And13ProvedPositiveSolutionInterpolationFrontierData` — **B/C**. The interpolation field is discharged by the proved interval-domain positive Agmon theorem, but the common fields remain:
  * `dissipation` — **C**.
  * `gradConstantPositive` — **C** as carried; could be easy for concrete `cGrad`, but the record leaves it abstract.
  * `gradientChain` — **C**.
  * `massControl` — **C**.
  * `powerIntegrability` — **C** as packaged here.
  * `energyFromCrossDiffusion` — **A/B**. There is a visible producer `intervalDomain_LpBootstrapEnergyInequality_of_regularity`; however many current frontier records still carry this field explicitly rather than selecting that theorem.

#### P3MoserAgmonDirectRoute

Path: `ShenWork/PDE/P3MoserAgmonDirectRoute.lean`.

The file is now sorry-free, but the no-drop route is conditional on:

```lean
AgmonNoDropEnergyReductionBefore u T rho p0
```

This is **C**, not a closed theorem. It records exactly the missing no-drop energy reduction needed before `IntervalDomainChain.moser_iteration_chain`. The theorems:

```lean
intervalDomain_all_Lp_of_agmon_bootstrap_no_drop
intervalDomain_Proposition_2_5_of_agmon_no_drop
```

are **A conditional on hreduce**, not unconditional headline producers. This route is **D** relative to the live interval-domain statement route unless some theorem later produces `AgmonNoDropEnergyReductionBefore`.

### Empty or circular-looking packages

* `IntervalDomainPaper2MainTheoremChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData` is intentionally a one-field wrapper. It is not circular; it points to the real `theorem12And13` frontier.
* The many `MainTheoremChiZero...FrontierData` records are wrapper records, not analytic producers.
* In `ShenWork/Paper2/Statements.lean`, `Paper2MainSolutionBranchData` and the `.of_assumed_solutions_branch` wrappers are tautological statement-layer packages: they take essentially the branch conclusions as hypotheses. They are **D** for headline residual accounting.

## 3. Paper 3 interval-domain statement assembly

Primary paths:

* `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`
* `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`
* generic support: `ShenWork/Paper3/StatementAssembly.lean`

### Proposition 1.x routes

Base interval-domain proposition package:

```lean
IntervalDomainPaper3Proposition1FrontierData p
```

fields:

* `negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p` — **C** in general.
* `criticalExistence : ...` — **C**, unless routed through Paper2 Theorem 1.2 in the Paper2-main route.

More reduced proposition routes:

* `IntervalDomainPaper3Proposition1FromPaper2TheoremsData` — **B**. Fields: `negativeBound`, `theorem12`, `theorem13`; Proposition 1.3 and 1.4 are produced from Paper2 Theorems 1.3 and 1.2.
* `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData` — **B**. Fields:
  * `negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p` — **C** in general.
  * `paper2Main : IntervalDomainPaper2MainTheoremTargets p C` — **B**, supplied by the Paper2 route above.

In the actual-linear-small positive-sensitivity regime, the negative-sensitivity residual is discharged by:

```lean
intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
```

This is **A** and intentionally vacuous, because `0 < p.χ₀` contradicts the negative-sensitivity hypothesis `p.χ₀ ≤ 0`.

### Core Theorem 2.x routes

Base core route in `IntervalDomainStatementAssembly.lean`:

```lean
intervalDomain_paper3_coreStatementTargets_of_coreExistence
```

inputs:

* `hcont : IntervalDomainInitialContinuityRaw p` — **C**.
* `hcore : IntervalDomainSectorialMainlineCoreExistence p uBar` — **B/C** monolithic core package.

Reduced raw-linear route:

```lean
IntervalDomainPaper3CoreStatementLinear22Data p M0 uBar vLower
```

fields:

* `initialContinuity : IntervalDomainInitialContinuityRaw p` — **C**.
* `persistence : IntervalDomainSectorialTheorem21Persistence p uBar` — **C** in the base route; **A** in actual-linear-small via `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`.
* `theorem22Nonminimal : LinearStabilityInstabilityNonminimalRaw ...` — **C**.
* `theorem22Minimal : LinearStabilityInstabilityMinimalRaw ...` — **C**.

The theorem `intervalDomain_paper3_coreStatementTargets_of_linear22Data` is **A** once these fields are supplied.

### Preferred actual-linear-small full statement route

For the actual-linear-small regime, the least-residual full-statement route visible in source is the thin P2-main/no-negative route:

```lean
intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
```

from:

```lean
IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
```

under parameter hypotheses:

```lean
ha   : 0 < p.a
hb   : 0 < p.b
hχ0  : 0 < p.χ₀
hm   : p.m = 1
hβ   : 1 ≤ p.β
hχ   : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))
```

Top-level fields:

* `paper2Main : IntervalDomainPaper2MainTheoremTargets p C` — **B**. This should be supplied by the Paper2 least-residual route above.
* `mainline : IntervalDomainPaper3MainlineActualLinear22ThinFrontierData ...` — **B/C**.

The `mainline` fields are:

```lean
structure IntervalDomainPaper3MainlineActualLinear22ThinFrontierData ... where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  theorem22Nonminimal : LinearStabilityInstabilityNonminimalRaw ...
  theorem22Minimal : LinearStabilityInstabilityMinimalRaw ...
  compactness : IntervalDomainPaper3SupNormCompactnessAPosData ...
  stability24 : IntervalDomainPaper3Stability24ActualLinearFrontierData p ...
```

Classifications:

* `initialContinuity` — **C**.
* `theorem22Nonminimal` — **C**.
* `theorem22Minimal` — **C**.
* `compactness : IntervalDomainPaper3SupNormCompactnessAPosData` — **B/C**. It reduces compactness/regularization to:
  * `compact : TimeTranslateCompactnessRaw ...` — **C**.
  * `resolvent : NeumannResolventGradientBoundExistsRaw ...` — **C**.
  The upper-envelope equality is definitional in the sup-norm compactness data, and the minimal-upper branch is vacuous from `0 < p.a`.
* `stability24 : IntervalDomainPaper3Stability24ActualLinearFrontierData` — **B/C**. Only the nonminimal positive-sensitivity Theorem 2.4 branches remain:
  * `global24` — **C**.
  * `exp24` — **C**.
  The Theorem 2.3 negative-sensitivity branches are vacuous from `0 < p.χ₀`, and the Theorem 2.5 minimal branches are vacuous from `0 < p.a`.

Already-produced pieces in this actual-linear-small route:

* `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` — **A** for Theorem 2.1 persistence under the actual-linear-small parameter hypotheses.
* `intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos` — **A** for the negative-sensitivity residual in the positive-χ route.
* Pure conversions:
  * `IntervalDomainPaper3MainlineActualLinear22ThinFrontierData.toCurrent` — **A** once thin fields are supplied.
  * `IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25` — **A** once `global24`/`exp24` are supplied.
  * `IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData` — **A** once compact/resolvent/initial continuity are supplied.

### Alternative actual-linear a-priori route

The file also provides:

```lean
intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData
```

with input:

```lean
IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
```

fields:

* `paper2Main : IntervalDomainPaper2MainTheoremTargets p C` — **B**.
* `mainline : IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData ...` — **B/C**.

The a-priori mainline package carries:

* `core : IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p`, with fields:
  * `spectralSemigroupOrbitBound` — **C**.
  * `continuation` — **C**.
  * `massLpSmoothing : IntervalDomainMassLpSmoothingRouteResiduals p` — **B/C**; source has further Moser-ladder residual packages reducing pieces such as L² seed, Moser dissipation, relative interpolation, and endpoint.
* `compactness : IntervalDomainPaper3ConcreteCompactnessRegularizationData ...` — **C/B** depending on the supplied compactness route.
* `stability : IntervalDomainPaper3Stability23To25FrontierData ...` — **C**, unless replaced by the actual-linear `stability24` thin route.

This route is useful but not as thin as the actual-linear raw-Theorem-2.2 thin route for headline residual counting.

### Generic Paper3 statement routes

In `ShenWork/Paper3/StatementAssembly.lean`:

* `Paper3Proposition1FrontierData` — **C** generic statement-layer record.
* `Paper3Proposition1FromPaper2Theorem13Data` — **B**; uses Paper2 Theorem 1.3 for Proposition 1.3, still carries negativeBound and proposition14.
* `Paper3Proposition1FromPaper2TheoremsData` — **B**; uses Paper2 Theorems 1.2/1.3 for Proposition 1.4/1.3, still carries negativeBound.
* `Paper3Proposition1FromPaper2MainTargetsData` — **B**; uses the Paper2 main bundle, still carries negativeBound.

These are honest bridges, not unconditional producers.

### Empty or circular-looking packages

* `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData` looks small because the negative-sensitivity residual is discharged by contradiction from `0 < χ₀`, and actual-linear persistence is produced internally. It is not empty: `paper2Main` and `mainline` remain real inputs.
* `IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25` intentionally fills many branches by contradiction; only `global24` and `exp24` are non-vacuous.
* `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData` is not circular, but it does **not** derive Proposition 1.2 from Paper2; it still carries `negativeBound` unless using the positive-χ no-negative wrapper.

## 4. Summary of least-residual live headline surfaces

### Paper1

Preferred source route:

```lean
paper1_mainStatementTargets_of_lowerPinnedContactData
```

or raw variant:

```lean
paper1_mainStatementTargets_of_lowerPinnedRawContactData
```

Remaining live inputs:

* `ConstructionNegSMPProvider` — **C**.
* `Paper1PositiveLowerPinnedContactBranchData` or `Paper1PositiveLowerPinnedRawContactBranchData` — **B/C**.
* `Paper1MainlineExistence cStarStarFn` — **C**.

### Paper2 interval-domain

Preferred `χ₀ = 0` source route:

```lean
intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
```

Remaining live input fields after expanding the wrapper:

* `prop25RawDropTerminal` — **B** with C subfields `rawMoserDrop`, `relativeMassGradient`, `terminalEndpoint`.
* `globalExtension` — **C**.
* `slowBootstrap` — **C**.
* `criticalBootstrap` — **C**.
* `criticalEventualSupBound` — **C**.
* `strongBootstrap` — **C**.
* `strongEventualSupBound` — **C**.

Produced internally:

* Theorem 1.1 in the `χ₀ = 0` regime — **A**.
* Theorem 1.2/1.3 local existence in the `χ₀ = 0` local-free route — **A**.
* Positive solution interpolation via proved Agmon, when using the positive-solution route — **A**.

### Paper3 interval-domain

Preferred actual-linear-small full-statement route:

```lean
intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
```

Remaining live inputs:

* `paper2Main : IntervalDomainPaper2MainTheoremTargets p C` — **B**, supplied by Paper2’s route.
* `mainline : IntervalDomainPaper3MainlineActualLinear22ThinFrontierData ...` — **B/C**, with fields:
  * `initialContinuity` — **C**.
  * `theorem22Nonminimal` — **C**.
  * `theorem22Minimal` — **C**.
  * `compactness.compact` — **C**.
  * `compactness.resolvent` — **C**.
  * `stability24.global24` — **C**.
  * `stability24.exp24` — **C**.

Produced internally:

* Actual-linear Theorem 2.1 persistence — **A**.
* Negative-sensitivity Proposition 1.2 residual in the `0 < χ₀` route — **A** by contradiction.
* Vacuous Theorem 2.3 / Theorem 2.5 branches in the actual-linear-small positive regime — **A** by contradiction.

## Final assessment

The repository can honestly claim a 0-sorry/0-axiom source state for the inspected modules. It cannot honestly claim unconditional Paper1/Paper2/Paper3 headline theorems. The current source is best understood as a set of increasingly thin conditional statement assemblies. The strongest progress is that several previously large headline inputs have been reduced to smaller named atoms: Paper1 to lower-pinned/no-contact positive branch data, Paper2 to raw-drop/mass-gradient/terminal endpoint Moser atoms plus bootstrap/globalization frontiers, and Paper3 to actual-linear-small persistence plus thin raw Theorem 2.2, compactness, and stability24 frontiers.
