# Q2214 R1 global headline-input audit for `Shen_work` commit `5fc60d48ba060e2b30439b77315537aa9a956c3c`

## Bottom line

The Lean tree has real statement wiring, but the Paper1--Paper3 headline theorem packages are not all no-assumption paper theorems. Most public `...Data`, `...FrontierData`, `...BranchData`, and `...Fact` wrappers are conditional assembly interfaces. A safe reading is:

- **A**: no analytic input-package remains, apart from ordinary parameter/regime hypotheses.
- **B**: a formerly explicit input is produced by another named wrapper.
- **C**: honest analytic frontier/residual still remains.
- **D**: deprecated/no-go/same-as-goal route that should not be advertised as a producer.

## Paper 1

### Classification

| Package or theorem | Class | Source-backed audit |
|---|---:|---|
| `paper1_Lemma_2_5`, `paper1_Lemma_2_5_JensenStep`, `paper1_lemma25Targets` | **A** | These are closed wrappers in `ShenWork/Paper1/StatementAssembly.lean`, around the Lemma 2.5 block. They return the proved Lemma 2.5/Jensen targets without a frontier package. |
| `paper1_mainStatementTargets_of_mainResultsData` | **C** | It proves `Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3` only from `Paper1MainResultsData`. The structure is a headline input package, not currently produced by a no-frontier wrapper. |
| `paper1_mainlineStatementTargets_of_mainlineExistence` | **C** | It proves Theorems 1.2/1.3 from `Paper1MainlineExistence`; that existence package remains an input. |
| `paper1_Theorem_1_1_of_constructionNegSMPProvider` | **C**, with **B** sub-progress | The theorem still needs `ConstructionNegSMPProvider` plus a positive branch. The old negative upper-bound task is partly wired: `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple` reduces it to the scalar `U 0 < 1`, with supporting bounds in `StationaryUpperTail.lean`. |
| `paper1_combinedStatementTargets_of_data` | **C** | Combines `Paper1MainResultsData`, `Paper1PropositionFrontierData`, `Paper1Lemma51FrontierData`, and `Paper1Lemma52FrontierData`; only the Lemma 2.5 component is closed internally. |
| `HasWaveRightTailAsymptotic_of_stationary` | **D-risk / honest residual** | In `StationaryUpperTail.lean`, this theorem takes `htail : HasWaveRightTailAsymptotic c κ₁ U` and returns the same predicate. It is documented as a carried tail-asymptotic residual, not a producer. |

### Main remaining Paper1 residuals

`Paper1MainResultsData`, `Paper1MainlineExistence`, proposition frontiers, Lemma 5.1/5.2 frontiers, the positive construction branch, fixed-point/stationarity/SMP inputs in `ConstructionNegSMPProvider`, and the sharp right-tail asymptotic remain open or externally supplied.

## Paper 2

### Generic packages

| Package or theorem | Class | Source-backed audit |
|---|---:|---|
| `paper2_bootstrapEstimateTargets_of_branchData` | **C** | In `ShenWork/Paper2/StatementAssembly.lean`, it assembles Lemmas 2.6--2.7 and Propositions 2.2--2.5 from `Paper2BootstrapEstimateBranchData`. |
| `paper2_Proposition_1_1_of_existenceData` | **C** | Consumes `Paper2Proposition11ExistenceData`; the local-existence/blow-up alternative is an input. |
| `paper2_mainTheoremTargets_of_solutionBranchData` | **C** | `Paper2MainTheoremTargets` is exactly Theorems 1.1--1.3, but the wrapper needs `Paper2MainSolutionBranchData`. |
| `paper2_statementTargets_of_data` | **C** | Combines bootstrap and local/main packages from `Paper2StatementData`; still conditional. |

### Interval-domain packages

| Package or theorem | Class | Source-backed audit |
|---|---:|---|
| `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` | **A** | In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`, this consumes only the regime/parameter hypotheses `p.χ₀ = 0`, `0 < p.a`, `0 < p.b`, `1 ≤ p.α`, `1 ≤ p.γ`, and delegates to `intervalDomain_theorem_1_1_chiZero_unconditional`. No half-step frontier package remains. |
| `intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData` | **B/C** | Local existence is produced by `intervalDomain_localExistence_chiZero_unconditional`; the finite-horizon alternative remains a residual. |
| `IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData.toPositive` | **B/C** | Fills the Theorem 1.2/1.3 local-existence slot with `intervalDomain_localExistence_chiZero_unconditional`, but keeps solution-slice interpolation/energy, `prop25`, global extension, bootstrap, and eventual-sup fields. |
| `intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData` | **B/C** | Produces Theorem 1.1 internally via the χ₀=0 unconditional route and uses the local-free Theorem 1.2/1.3 route, but still carries the Theorem 1.2/1.3 frontiers. |
| `intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData` | **B/C**, best current full Paper2 route | This is the most credible full statement wrapper: positive solution-slice route, thin section-2 package, and local-free χ₀=0 local/main route. It remains conditional on the common interpolation/energy, bootstrap, eventual-sup, finite-horizon, and related fields. |
| H2/logistic source main/statement routes | **C** | `intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData`, `...of_halfStepLogisticSourceFrontierData`, and their statement bundles carry half-step frontier packages. |
| Routes consuming `IntervalDomainInterpolation` | **D** | `ShenWork/Paper2/IntervalDomainInterpolationCounterexample.lean` proves `not_intervalDomainInterpolation`. Therefore GN-frontier/interpolation-frontier headline routes using the globally quantified `IntervalDomainInterpolation` should be treated as deprecated no-go interfaces, not theorem producers. |

### Main remaining Paper2 residuals

Finite-horizon alternative; positive solution-slice interpolation/energy; dissipation; positive gradient constant and gradient chain; mass control; power integrability; energy from cross diffusion; `Proposition_2_5`; global extension; slow/critical/strong bootstrap; critical/strong eventual sup-norm bounds; and thin section-2 fields for Lemma 2.6, Lemma 2.7, Proposition 2.2, and Proposition 2.3.

## Paper 3

### Generic and interval-domain packages

| Package or theorem | Class | Source-backed audit |
|---|---:|---|
| `paper3_uniformPersistenceTargets_of_rawData` | **C** | In `ShenWork/Paper3/StatementAssembly.lean`, it proves Theorem 2.1 and parts from `Paper3UniformPersistenceRawData`; the raw package is still an input. |
| `paper3_Theorem_2_2_of_branchData` | **C** | Consumes `Paper3Theorem22BranchData`. |
| `paper3_compactnessRegularizationTargets_of_rawData` | **C** | Consumes `Paper3CompactnessRegularizationRawData`. |
| `paper3_Proposition_1_3_of_Paper2_Theorem_1_3` | **B** | Legitimately derives Paper3 Proposition 1.3 from Paper2 Theorem 1.3. |
| `paper3_Proposition_1_4_of_Paper2_Theorem_1_2` | **B** | Legitimately derives Paper3 Proposition 1.4 from Paper2 Theorem 1.2. |
| `Paper3Proposition1FromPaper2MainTargetsData` and interval version | **B/C** | Despite the name, these still contain `negativeBound`. The bridge extracts only `main.2.1` and `main.2.2` from Paper2 main targets for Paper3 Propositions 1.4 and 1.3. |
| `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall`, `...partTargets...`, `...sectorial...` | **A** | In `IntervalDomainActualLinearStatementAssembly.lean`, these call `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` internally; no persistence package is carried. |
| `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.to_coreExistence` | **B/C** | It produces persistence fields from `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` and global-solution fields from continuation plus mass/Lp smoothing, but still needs spectral semigroup, continuation, and smoothing inputs. |
| `intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData` | **B/C** | Terminal Moser converts through `core.to_CERawGradFacts hb`; compactness and stability are passed through. The terminal core, compactness, and stability packages remain residual. |
| `intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainData` | **B/C**, best current full Paper3 route | This combines the terminal Moser mainline with Paper2-main routing for Propositions 1.3/1.4. It still carries `negativeBound` for Proposition 1.2 and all mainline terminal/compactness/stability residuals. |
| Paper2 Theorem 1.1 -> Paper3 Proposition 1.2 | **D** | `ShenWork/Paper3/Statements.lean` proves `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`. So `negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p` cannot be silently derived from Paper2 Theorem 1.1 under the current abstract API. |

### Main remaining Paper3 residuals

`negativeBound`; terminal Moser `boundednessCore`, `closedEnergyTrace`, `rawMoserDrop`, `relativeMassGradient`, and `terminalPointwise`; spectral semigroup orbit bound; continuation; compactness/regularization fields (`upperEq`, compactness, `initialContinuity`, `minimalUpper`, resolvent); and stability frontiers for Theorems 2.3--2.5.

## Cleanup plan

1. Rename or alias `Paper3Proposition1FromPaper2MainTargetsData` and `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData` to names such as `...FromNegativeBoundAndPaper2MainTargetsData`.
2. Add doc comments to `negativeBound` saying it is the independent Paper3 Proposition 1.2 residual and is not supplied by Paper2 Theorem 1.1; cite `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`.
3. Mark routes consuming `IntervalDomainInterpolation` as deprecated/no-go and point to `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`; steer users to solution-slice/positive solution-slice routes.
4. Add “frontier package, not theorem producer” comments to headline structures: `Paper1MainResultsData`, `Paper1MainlineExistence`, `Paper2MainSolutionBranchData`, `Paper2StatementData`, `IntervalDomainPaper2Theorem12And13...FrontierData`, and `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData`.
5. Add explicit “best current route” aliases with names that include `fromFrontiers` or `fromResiduals`, so conditional wrappers cannot be mistaken for no-assumption paper headlines.
6. Keep a short status table in `UNDERSTANDING.md` separating closed theorems, produced-subfield wrappers, honest residual packages, and deprecated/no-go routes.
