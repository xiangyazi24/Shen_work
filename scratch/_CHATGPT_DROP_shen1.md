# Q2221 R2 Paper1/Paper2 residual wireability audit

Audited current `main` at commit `09140eae`.

## Paper1 map

### `Paper1MainResultsData`

`construction_neg`: wireable by an existing chain, and should be thinned. Current full field is the old negative construction branch. The existing reduced route is `ConstructionNegSMPProvider` → `constructionNeg_of_provider_smp` → `Theorem_1_1.of_constructionNeg_provider_smp` → `paper1_Theorem_1_1_of_constructionNegSMPProvider`. This removes the full carried `ShenUpperBoundNegative` field and replaces it with the scalar strong-maximum-principle obligation `U 0 < 1`, while still carrying the sharp right-tail asymptotic.

`construction_pos`: genuine analytic residual. I found construction/witness helpers for positive fixed-point outputs, but no exact producer for the full positive branch field of `Paper1MainResultsData`.

`cStarStar_spec` and `stability`: genuine B5 stability frontiers in this old main bundle. There is a better route through `Paper1MainlineExistence`, but no theorem produces these old fields from lower data without carrying the stability analysis.

`wave_cont`, `cauchy_unique`, `resolvent`, `tail_asymp`: old regularity/uniqueness/tail frontiers. `resolvent` is wireable if the interface is changed to carry `TravelingWaveRegularity`, via `IsTravelingWave.V_eq_frozenElliptic_full` and related C2 uniqueness lemmas. In the current exact field shape, no producer exists. `tail_asymp` remains genuine; the repository has consumers such as Remark 4.3 bridges, not a producer for arbitrary waves.

### `Paper1MainlineExistence`

This is the preferred Paper1 B5 route. It already thins the old `Paper1MainResultsData` stability interface. The theorem chain is `Paper1MainlineExistence` → `Theorem_1_2.of_mainlineExistence` and `Theorem_1_3.of_mainlineExistence` → `Theorem_1_2_and_1_3.of_mainlineExistence` → `paper1_mainlineStatementTargets_of_mainlineExistence`.

Field classification:

- `cStarStar_spec`: genuine stability-threshold frontier.
- `regularity`: genuine wave-regularity frontier, but it usefully replaces the separate old `wave_cont` and `resolvent` fields. Once supplied, `IsTravelingWave.V_eq_frozenElliptic_full` is used downstream.
- `energyDissipation`: genuine perturbation PDE frontier. The repository already supplies the weighted signal estimates from Lemma 2.5; this field is the remaining energy package.
- `l2ToUniform`: genuine analytic upgrade frontier. The file explicitly separates `WeightedL2ToUniformMovingFrameUpgrade`; weighted L2 convergence alone is not claimed to imply uniform convergence.
- `cauchyUnique`: genuine whole-line Cauchy uniqueness residual.

### `Paper1PropositionFrontierData`

All five fields are genuine analytic residuals for arbitrary Cauchy data: `existence`, `max_neg`, `bound_pos`, `conv_neg`, and `conv_pos`. There are direct constant/equilibrium branches elsewhere, but no exact producer for these universal proposition fields. The wrapper `paper1_propositionTargets_of_frontierData` only routes them into `Proposition_1_1.of_global_existence_and_bounds` and `Proposition_1_2.of_global_existence_and_convergence`.

### `Paper1Lemma51FrontierData`

`resolvent`: exact current field has no producer. It is wireable after an interface change that carries `TravelingWaveRegularity`, using `IsTravelingWave.V_eq_frozenElliptic_full`, `IsTravelingWave.V_eq_frozenElliptic_via_C2`, or `V_eq_frozenElliptic_via_C2_uniqueness`.

`continuous`: exact current field has no producer; it is naturally part of `TravelingWaveRegularity` but not derivable from bare `IsTravelingWave` in the current API.

`deriv_tends`, `deriv_bound`, `deriv_exp`: genuine derivative/asymptotic residuals. The file has strong downstream consumers such as `Lemma_5_1.of_resolvent_derivative_bounds`; it does not prove these universal derivative fields.

### `Paper1Lemma52FrontierData`

`monotone`: genuine analytic residual in the exact universal field shape. Existing chains prove Lemma 5.2 from this monotonicity assumption: `Lemma_5_2_explicit_under_monotone` and `Lemma_5_2_under_monotone`. There are special-case direct branches such as `Lemma_5_2_frozen_monotone_trap_direct`, but they do not produce monotonicity for all traveling waves.

### `ConstructionNegSMPProvider`

Already produced after the provider: `FrozenStationaryWaveProfile`, `deriv U ≤ 0`, and `deriv (frozenElliptic p U) ≤ 0` are discharged by the lower-pinned Schauder wrapper and trap monotonicity inside `constructionNeg_of_lowerPinnedSchauderData_smp`. `ShenUpperBoundNegative` is reduced by `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple` to the scalar `U 0 < 1`.

Still genuine residuals inside the provider: the lower-pinned Schauder principle/data, the map-to-stationarity bridge, left-flatness, the scalar strong maximum principle `U 0 < 1`, and the sharp right-tail asymptotic. `StationaryUpperTail.lean` explicitly records that no producer exists for `U 0 < 1` or `HasWaveRightTailAsymptotic` from stationarity/trap alone; `HasWaveRightTailAsymptotic_of_stationary` is only a carried-interface lemma.

## Paper2 map for the Q2214 route

Target route: `intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.

This is indeed the best current interval-domain route. Its top-level input has only:

- `section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p`
- `localAndMain : IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeFrontierData p C cGrad`

The assembly chain is:

`intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData` uses `intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData`, `intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier`, and `intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData`.

### `section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData`

Fields `lemma26`, `lemma27`, `prop22`, and `prop23` are genuine section-2 residuals in this statement-target bundle. The wrapper `intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData` only packages them through `Lemma_2_6.of_assumed_bound_branch`, `Lemma_2_7.of_assumed_bound_branch`, `Proposition_2_2.of_assumed_estimate_branch`, and `Proposition_2_3.of_assumed_estimate_branch`.

What is already produced here: Proposition 2.4 is inserted by `intervalDomain_Proposition_2_4 p`, and Proposition 2.5 is supplied from the nested Theorem 1.2/1.3 data rather than from the section-2 record. Corollary 2.1 is produced from the positive solution-slice common data by `IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_solution_interpolation_frontier`.

### `localAndMain`

`proposition11.finiteHorizonAlternative`: genuine continuation/blow-up alternative residual. The local-existence slot is already closed in the χ-zero route by `intervalDomain_localExistence_chiZero_unconditional`, through `intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData`.

`main.theorem12And13.common.solutionInterpolation`: genuine solution-slice interpolation frontier, but this is the correct non-vacuous replacement for the false global `IntervalDomainInterpolation` statement. It is used both for Lemma 4.1 through `intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier` and for Corollary 2.1 through `IntervalDomainClassicalSolutionInterpolation_of_positive` followed by `Corollary_2_1_intervalDomain_of_solution_interpolation_frontier`.

`common.dissipation`, `gradConstantPositive`, `gradientChain`, `massControl`, `powerIntegrability`, `energyFromCrossDiffusion`: genuine PDE/Moser-route residuals. The route composes them, but I found no exact producers in the statement assembly.

`prop25`: genuine endpoint boundedness residual for this route. It is no longer duplicated in section-2 thin data, but it is still required by the Theorem 1.2/1.3 machinery.

`globalExtension`: genuine continuation/globalization residual.

`slowBootstrap`, `criticalBootstrap`, `criticalEventualSupBound`, `strongBootstrap`, `strongEventualSupBound`: genuine regime-specific bootstrap/eventual-bound frontiers. The wrapper uses them to close Theorem 1.2 and Theorem 1.3; no producer was found in the route files.

### Paper2 no-go evidence

Do not reintroduce the old global interpolation field. `IntervalDomainInterpolationCounterexample.lean` proves `not_intervalDomainInterpolation`; its header states the exact `IntervalDomainInterpolation` prop is false because positive step functions have zero classical derivative almost everywhere while retaining nonzero mass. The current positive solution-slice route is therefore the right sound interface, not just a cosmetic thinning.

## Smallest next edit

Paper1 has the clearest small Lean cleanup: add a bundled full-main wrapper that combines the already existing `ConstructionNegSMPProvider` route for Theorem 1.1 with `Paper1MainlineExistence` for Theorems 1.2 and 1.3. This would stop the preferred headline surface from carrying the old full `construction_neg`, `stability`, `wave_cont`, `resolvent`, and `tail_asymp` fields directly. It changes no mathematical claim; it only reuses existing chains:

`ConstructionNegSMPProvider` → `Theorem_1_1.of_constructionNeg_provider_smp`, and `Paper1MainlineExistence` → `Theorem_1_2_and_1_3.of_mainlineExistence`.

For Paper2, the route is already thinned correctly. The smallest useful edit is documentation: mark `intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData` as the preferred interval-domain χ-zero statement route, and explicitly warn not to use the deprecated global `IntervalDomainInterpolation` route because `not_intervalDomainInterpolation` refutes it.
