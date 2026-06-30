# Q2301 shen2: Papers 1--3 headline statement assembly audit

Repo: `xiangyazi24/Shen_work`, branch `main`.

## Classification rule used

I classified statement/header wrappers by their Lean source shape, not by README claims.

* **A. Closed/unconditional producer**: theorem has no frontier/branch/data structure argument. It may have ordinary parameter hypotheses such as `2 < c`, `p.χ₀ = 0`, or `0 < p.a`, but it does not consume a package whose fields are the target theorem or the missing analytic branch.
* **B. Conditional/plausible wire-up**: theorem consumes a `...Data`, `...FrontierData`, `...BranchData`, or `...RawData` package; this is real statement wiring if the package fields are lower-level analytic atoms, but it is not a headline proof.
* **C. Unsupported/vacuous/known-false/impostor**: route uses a refuted premise, a deliberately degenerate zero-data model, or a package that merely carries target-level statements/branches and should not be reported as proved.

## Concise audit table

| Paper/file | Name | Shape | Class | Audit note |
|---|---|---:|---:|---|
| Paper1 `ShenWork/Paper1/StatementAssembly.lean` | `paper1_lemma25Targets` | no data argument | A | Closed bundle `Lemma_2_5 ∧ Lemma_2_5_JensenStep`, via `Lemma_2_5_proved` and `Lemma_2_5_JensenStep_proved`. |
| Paper1 `StatementAssembly.lean` | `paper1_mainStatementTargets_of_mainResultsData`, `paper1_Theorem_1_1_of_mainResultsData` | consumes `Paper1MainResultsData` | B/C | Conditional. Treat as C if advertised as proof: the main-results data is the headline package. |
| Paper1 `StatementAssembly.lean` | `paper1_Theorem_1_1_of_constructionNegSMPProvider` | consumes `ConstructionNegSMPProvider` and positive branch argument | B | Plausible high-level wiring, but still conditional on negative construction and positive branch. |
| Paper1 `StatementAssembly.lean` | `Paper1PositiveCriticalFrozenStationaryBranch` | `def` target branch | B/C | Not a theorem. This is the old monolithic positive branch target. |
| Paper1 `StatementAssembly.lean` | `PositiveUpperBarrierContactContradictions`, `Paper1PositiveCriticalFrozenStationaryContactBranch` | contact residual / branch package | B | Good decomposition; no-contact is still analytic residual. |
| Paper1 `StatementAssembly.lean` | `Paper1PositiveLowerPinnedContactBranchData`, `Paper1PositiveLowerPinnedRawContactBranchData` | data packages | B | Useful: tail is no longer carried separately; lower pin discharges it. Still carries no-contact. |
| Paper1 `StatementAssembly.lean` | `Paper1PositiveLowerPinnedSchauderContactData`, `Paper1PositiveLowerPinnedCapSchauderContactData` | Schauder/contact frontiers | B | Plausible wiring to existing lower-pinned producers, but still contains Schauder/map/stationarity/flat/no-contact inputs. |
| Paper1 `StatementAssembly.lean` | `Paper1MainStatementSMPMainlineData`, `Paper1MainStatementStrictBarrierData`, `Paper1MainStatementLowerPinnedContactData`, `Paper1MainStatementLowerPinnedRawContactData` | bundled data | B | Conditional main statement wrappers. They reduce positive branch shape but still carry `ConstructionNegSMPProvider`, a positive branch package, and `Paper1MainlineExistence`. |
| Paper1 `StatementAssembly.lean` | `Paper1Lemma51FrontierData`, `Paper1Lemma52FrontierData` | explicit analytic fields | B | Honest frontier records for Lemma 5.1/5.2; not closed. |
| Paper1 `StatementAssembly.lean` | `Paper1PropositionFrontierData` | explicit Cauchy/PDE fields | B | Honest proposition frontier; not closed. |
| Paper1 `StatementAssembly.lean` | `Paper1CombinedStatementData`, `Paper1CombinedStrictBarrierStatementData`, `Paper1CombinedLowerPinnedContactStatementData`, `Paper1CombinedLowerPinnedRawContactStatementData` | bundled data | B/C | Conditional statement bundles. They assemble targets from packages; they do not prove Paper1 headline statements. |
| Paper1 `ShenWork/Paper1/StationaryUpperTail.lean` | `HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap`, `lowerPinnedRawMonotoneTrap_tail_family_for_branch` | no stationary residual | A | Closed pure squeeze route from lower/raw lower pin to tail. Good closed atom. |
| Paper1 `StationaryUpperTail.lean` | `HasWaveRightTailAsymptotic_of_stationary` | assumes `htail` and returns it | C | Carry/no-op wrapper; do not count as producer. |
| Paper2 `ShenWork/Paper2/UnitPointStatementAssembly.lean` | `unitPointPaper2_mainStatementTargets`, `unitPointPaper2_logisticNonminimalPackage`, `unitPointPaper2_Theorem_1_1`, `unitPointPaper2_Theorem_1_3` | no data argument | A | Closed unit-point logistic targets. |
| Paper2 `UnitPointStatementAssembly.lean` | `unitPointPaper2_Theorem_1_2_when_not_a_pos_b_zero` | ordinary exclusion hypothesis | A/B | Honest conditional theorem: no frontier data, but excludes the known bad ODE slice `0 < p.a ∧ p.b = 0`. |
| Paper2 `ShenWork/Paper2/StatementAssembly.lean` | `paper2_statementTargets_of_data`, `paper2_localAndMainTheoremTargets_of_data`, `paper2_mainTheoremTargets_of_solutionBranchData` | consumes branch/data | B | Generic Paper2 is only statement assembly from data. |
| Paper2 `StatementAssembly.lean` | `Paper2Proposition11ExistenceData` | carries local existence branch | B | Conditional local-existence package. |
| Paper2 `StatementAssembly.lean` | `Paper2LocalAndMainTheoremData`, `Paper2StatementData` | bundles branch data | B/C | Conditional. Do not describe as Paper2 headline proof. |
| Paper2 `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` | `intervalDomainPaper2_Lemma_3_1` | no data argument | A | Closed interval-domain Lemma 3.1 via `Lemma31Closure.Lemma_3_1_intervalDomain`. |
| Paper2 `IntervalDomainStatementAssembly.lean` | `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` | parameter hypotheses only | A | Closed chi-zero interval-domain Theorem 1.1 route; local existence produced internally. |
| Paper2 `IntervalDomainStatementAssembly.lean` | `intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData` | finite-horizon frontier remains | B | Local existence discharged internally, but finite-horizon alternative still carried. |
| Paper2 `IntervalDomainStatementAssembly.lean` | `IntervalDomainPaper2BootstrapEstimateThinFrontierData` | carries Lemma 2.6/2.7/Prop 2.2/2.3; Prop 2.4 closed; Prop 2.5 supplied | B | Useful thinning, not closed. |
| Paper2 `IntervalDomainStatementAssembly.lean` | `intervalDomainPaper2_Lemma_4_1_of_GN_frontier`, `intervalDomainPaper2_aprioriTargets_of_GN_frontier` | consumes `IntervalDomainInterpolation` | C | Deprecated/no-go route: premise is refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`. |
| Paper2 `IntervalDomainStatementAssembly.lean` | `IntervalDomainPaper2InterpolationEnergyFrontierData`, `IntervalDomainPaper2Theorem12And13InterpolationFrontierData` | includes false global interpolation field | C | Do not use as headline route. |
| Paper2 `IntervalDomainStatementAssembly.lean` | `IntervalDomainPaper2SolutionInterpolationEnergyFrontierData`, `IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData` | solution-slice interpolation packages | B | Plausible replacement route: avoids known false global interpolation. |
| Paper2 `IntervalDomainStatementAssembly.lean` | `IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData`, chi-zero local-free variant | many analytic fields | B | Best interval-domain main route shape, but still conditional on solution interpolation, dissipation, bootstrap, eventual sup bounds, global extension, etc. |
| Paper2 `ShenWork/Paper2/Statements.lean` | `Lemma_2_1_zero_data`, `Lemma_2_2_zero_data`, `Lemma_2_3_zero_data`, `Lemma_2_4_zero_data`, `lemmas_2_1_to_2_4_zero_data` | zero semigroup model | C | Explicitly marked impostor/vacuous; not analytic semigroup proof. |
| Paper3 `ShenWork/Paper3/StatementAssembly.lean` | `paper3_proposition1Targets_of_frontierData` | consumes `Paper3Proposition1FrontierData` | B | Conditional. Proposition 1.2 is `negativeBound`; 1.3/1.4 existence branches are carried. |
| Paper3 `StatementAssembly.lean` | `paper3_Proposition_1_3_of_Paper2_Theorem_1_3`, `paper3_Proposition_1_4_of_Paper2_Theorem_1_2` | consumes Paper2 theorems | B | Good bridge; not independent Paper3 proof. |
| Paper3 `StatementAssembly.lean` | `Paper3Proposition1FromPaper2MainTargetsData` | carries `negativeBound` + Paper2 main | B/C | Correctly leaves Proposition 1.2 residual independent. Do not claim Paper2 Theorem 1.1 implies Paper3 Proposition 1.2. |
| Paper3 `StatementAssembly.lean` | `paper3_uniformPersistenceTargets_of_rawData`, `paper3_Theorem_2_1_of_rawData` | consumes `Paper3UniformPersistenceRawData` | B | Conditional persistence assembly. |
| Paper3 `StatementAssembly.lean` | `paper3_Theorem_2_2_of_branchData`, `paper3_stability23To25Targets_of_branchData`, `paper3_compactnessRegularizationTargets_of_rawData` | branch/raw-data packages | B | Conditional statement-layer assembly. |
| Paper3 `StatementAssembly.lean` | `Paper3MainlineData`, `Paper3MainlineFromPaper2Theorem13Data`, `Paper3MainlineFromPaper2TheoremsData`, `Paper3MainlineFromPaper2MainTargetsData` | bundled frontiers | B/C | Conditional mainline bundles; do not describe as proved main theorem. |
| Paper3 `ShenWork/Paper3/IntervalDomainStatementAssembly.lean` | `intervalDomainPaper3_negativeSensitivityResidual_of_frontierData` | decomposes negative residual | B | Good atomization of Proposition 1.2 residual into global solution + eventual sup bound; still residual. |
| Paper3 `IntervalDomainStatementAssembly.lean` | `IntervalDomainPaper3Proposition1FrontierData` | carries `negativeBound` and critical existence branch | B | Conditional Proposition 1.x package. |
| Paper3 `IntervalDomainStatementAssembly.lean` | `intervalDomain_paper3_coreStatementTargets_of_coreExistence` | consumes `IntervalDomainInitialContinuityRaw` and `IntervalDomainSectorialMainlineCoreExistence` | B | Stronger than pure statement package, but still conditional on core existence and initial-continuity frontiers. |
| Paper3 `IntervalDomainStatementAssembly.lean` | `intervalDomain_paper3_Theorem_2_1_of_persistence` | consumes persistence package | B | Conditional wrapper. |
| Paper3 `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` | `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall`, `...partTargets...`, `...sectorial...` | no frontier data | A | Closed actual-linear small-sensitivity persistence producer for interval domain, under parameter hypotheses. |
| Paper3 `IntervalDomainActualLinearStatementAssembly.lean` | `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts`, `IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData`, `IntervalDomainPaper3StatementAprioriActualLinearSmallFrontierData` | frontier packages | B | Persistence fields produced internally, but spectral/orbit/continuation/mass-Lp/compactness/stability/proposition frontiers remain. |
| Paper3 `ShenWork/Paper3/Statements.lean` | `PositiveGlobalBoundedSolution` | weakened definition note | C warning | Source explicitly notes it is pointwise positivity, not paper-faithful per-time spatial floor; not a false theorem, but a faithfulness gap to track. |

## Paper-by-paper assessment

### Paper 1

Closed pieces are small and real.  `paper1_lemma25Targets` is a no-assumption theorem and should be counted as closed.  The lower-pinned tail squeeze in `StationaryUpperTail.lean` is also closed and should be used to avoid carrying `HasWaveRightTailAsymptotic` whenever the raw or plateau lower pin is preserved.

The Paper1 headline route remains conditional.  The main theorem wrappers consume packages:

```lean
paper1_mainStatementTargets_of_mainResultsData
paper1_Theorem_1_1_of_constructionNegSMPProvider
paper1_mainStatementTargets_of_smpMainlineData
paper1_mainStatementTargets_of_strictBarrierData
paper1_mainStatementTargets_of_lowerPinnedContactData
paper1_mainStatementTargets_of_lowerPinnedRawContactData
```

The best current positive branch accounting is the raw lower-pinned contact route:

```lean
Paper1PositiveLowerPinnedRawContactBranchData
paper1_positiveContactBranch_of_lowerPinnedRawContactData
paper1_positiveStrictBarrierBranch_of_lowerPinnedRawContactData
```

This is honest B-class wiring: the tail is produced from the raw lower pin, but `PositiveUpperBarrierContactContradictions` remains a real no-contact/upper strong-comparison residual.  Do not call the older `HasWaveRightTailAsymptotic_of_stationary` a producer; it assumes the exact tail conclusion and returns it.

### Paper 2

There are two real closed islands:

1. `UnitPointStatementAssembly.lean`: `unitPointPaper2_mainStatementTargets`, `unitPointPaper2_Theorem_1_1`, and `unitPointPaper2_Theorem_1_3` are closed for `unitPointDomain`.  `unitPointPaper2_Theorem_1_2_when_not_a_pos_b_zero` is also honest under its explicit exclusion hypothesis.
2. `IntervalDomainStatementAssembly.lean`: `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` is a no-frontier chi-zero route; `intervalDomainPaper2_Lemma_3_1` is closed.

The generic Paper2 statement wrappers are conditional assemblies from branch-data packages:

```lean
Paper2StatementData
Paper2LocalAndMainTheoremData
Paper2Proposition11ExistenceData
Paper2MainSolutionBranchData
Paper2BootstrapEstimateBranchData
```

The major C-class item is the global interpolation route:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
intervalDomainPaper2_Lemma_4_1_of_GN_frontier
intervalDomainPaper2_aprioriTargets_of_GN_frontier
IntervalDomainPaper2InterpolationEnergyFrontierData
IntervalDomainPaper2Theorem12And13InterpolationFrontierData
```

`IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation` proves the global interpolation premise false as stated.  Any route that includes it is not merely conditional; it is currently unsupported/vacuous.  Prefer the solution-slice structures:

```lean
IntervalDomainPaper2SolutionInterpolationEnergyFrontierData
IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
```

Also treat `Lemma_2_1_zero_data` through `Lemma_2_4_zero_data` in `Paper2/Statements.lean` as C-class impostors: source comments explicitly state they prove estimates only for `zeroSemigroupEstimateData`.

### Paper 3

Generic Paper3 is mostly B-class statement assembly.  The proposition route correctly keeps `NegativeSensitivityGlobalEventualBound` independent:

```lean
Paper3Proposition1FrontierData
Paper3Proposition1FromPaper2Theorem13Data
Paper3Proposition1FromPaper2TheoremsData
Paper3Proposition1FromPaper2MainTargetsData
```

The source comment on `Paper3Proposition1FromPaper2MainTargetsData` is important: `negativeBound` is not derived from Paper2 Theorem 1.1.  The interval-domain version also decomposes the negative residual usefully:

```lean
IntervalDomainPaper3NegativeSensitivityFrontierData
intervalDomainPaper3_negativeSensitivityResidual_of_frontierData
```

The Paper3 mainline wrappers are conditional on raw/branch data:

```lean
Paper3UniformPersistenceRawData
Paper3Theorem22BranchData
Paper3CompactnessRegularizationRawData
Paper3Stability23To25BranchData
Paper3MainlineData
```

The best closed Paper3 island is in `IntervalDomainActualLinearStatementAssembly.lean`:

```lean
intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall
intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall
intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall
```

These are A-class for the actual-linear small-sensitivity interval-domain Theorem 2.1/persistence statements.  The later mainline actual-linear structures are still B-class because they carry spectral semigroup orbit bounds, continuation, mass-Lp smoothing, compactness, stability, and proposition frontiers.

Finally, `Paper3/Statements.lean` contains a faithfulness warning: `PositiveGlobalBoundedSolution` uses pointwise positivity on the interior, not the paper's per-time spatial floor.  This is not an empty proof, but it is a statement-fidelity cleanup item.

## Recommended cleanup priority order

1. **Rename or quarantine C-class routes.** Mark all `IntervalDomainInterpolation`-based Paper2 wrappers as deprecated/no-headline in names or comments. They rely on a premise refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.

2. **Move `zeroSemigroupEstimateData` lemmas out of headline inventory.** Keep them as sanity tests/examples, but never list them as Paper2 Lemma 2.1--2.4 proofs.

3. **Promote closed islands separately.** Publish explicit lists for A-class endpoints: Paper1 Lemma 2.5, lower-pinned tail squeeze, Paper2 unit-point, Paper2 interval chi-zero Theorem 1.1, Paper2 interval Lemma 3.1, Paper3 actual-linear interval Theorem 2.1.

4. **For Paper1, make raw lower-pinned contact the preferred positive branch interface.** This minimizes the residual: Route-A/cubeApprox supplies profile + raw lower pin; tail is closed; only no-contact remains.

5. **For Paper2 interval main results, prefer positive solution-slice interpolation frontiers.** Avoid global interpolation. The immediate target should be filling fields in `IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData` and the chi-zero local-free variant.

6. **For Paper3 Proposition 1.2, keep the negative-sensitivity residual decomposed.** Work on `IntervalDomainPaper3NegativeSensitivityFrontierData.globalSolution` and `.eventualSupBound` separately. Do not route it through Paper2 Theorem 1.1.

7. **For Paper3 mainline, isolate actual-linear closed persistence from the remaining mainline frontiers.** The actual-linear Theorem 2.1 producer is real; the full statement target still needs core/apriori/compactness/stability data.

8. **Track Paper3 positivity fidelity.** Decide whether a future domain interface should encode compactness/infimum so `PositiveGlobalBoundedSolution` can match the paper's per-time spatial floor rather than pointwise interior positivity.
