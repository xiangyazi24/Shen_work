# Q2675 shen2: Paper1--3 headline/frontier audit

Repo target: `xiangyazi24/Shen_work`, Lean 4.

Scope honored: I inspected the non-Zinan statement/headline/assembly surfaces and the named Moser residual packages. I did **not** edit, inspect for proof content, or rely on `ShenWork/PDE/P3MoserHighExcursionProducer.lean` or `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

## Legend

| Class | Meaning |
|---|---|
| A | Already discharged/proved locally: no headline input package remains at that layer, apart from ordinary theorem parameters/inequalities. |
| B | Pure wiring likely available now: theorem/def converts named packages into headline targets, but the package itself is still supplied. |
| C | Honest analytic residual/frontier: no local producer found in the inspected surfaces; the field names real PDE/compactness/stability/endpoint content. |

## Executive summary

| Area | Status | Exact Lean names |
|---|---:|---|
| Paper1 Lemma 2.5 | A | `paper1_Lemma_2_5`, `paper1_Lemma_2_5_JensenStep`, `paper1_lemma25Targets` |
| Paper1 main statements | B over C | B: `paper1_mainStatementTargets_of_*`; C: `ConstructionNegSMPProvider`, `Paper1Positive*Branch*Data`, `Paper1MainlineExistence` |
| Paper1 Lemma 5.x and Propositions | B over C | B: `paper1_lemma51And52Targets_of_frontierData`, `paper1_propositionTargets_of_frontierData`; C: `Paper1Lemma51FrontierData`, `Paper1Lemma52FrontierData`, `Paper1PropositionFrontierData` |
| Generic Paper2 statement layer | B over C | B: `paper2_statementTargets_of_data`; C: `Paper2BootstrapEstimateBranchData`, `Paper2Proposition11ExistenceData`, `Paper2MainSolutionBranchData` |
| Interval Paper2 section-2 / Moser | B over C, with one local A component | A: `intervalDomain_Proposition_2_4`; B: `intervalDomainPaper2_*_of_*FrontierData`; C: thin section-2 frontiers and Prop. 2.5 Moser atoms |
| Paper2 Theorem 1.1/1.2 chain | B over C | B: `IntervalDomainTierChain.*`, `IntervalDomainTheorem12.*`; C: energy-from-cross-diffusion, continuation, bootstrap seeds, eventual sup/global boundedness |
| P3 Moser regularity/endpoint continuity | B over C | B: `intervalDomain_*Regularity*` wrappers; C: `atZero`, `gradientTimeIntegrable` or `gradientEnergyContinuous` |
| Moser ladder/apriori route | B over C | B: `.corollary21`, `.proposition25`, `.to_routeResiduals`, `.aprioriBound`; C: L2 seed regularity, Moser step/drop/relative/endpoint frontiers |
| Generic Paper3 statement layer | B over C | B: `paper3_mainlineTargets_of_*`; C: persistence raw data, Theorem 2.2 branch data, compactness raw data, stability data, negative-sensitivity bound |
| Interval Paper3 core | A/B over C | A: `Lemma_3_1_proved`, `intervalDomain_upperEnvelopeMonotonicityRaw_supNorm`, actual-linear persistence producer; B: core/linear assembly wrappers; C: `IntervalDomainInitialContinuityRaw`, sectorial core/linear/compactness/stability frontiers |

## Paper1 details

| Class | Names | Audit |
|---|---|---|
| A | `paper1_Lemma_2_5`, `paper1_Lemma_2_5_JensenStep`, `paper1_lemma25Targets` | Closed locally via `Lemma_2_5_proved` and `Lemma_2_5_JensenStep_proved`. |
| B | `paper1_mainStatementTargets_of_mainResultsData`, `paper1_mainStatementTargets_of_smpMainlineData`, `paper1_mainStatementTargets_of_strictBarrierData`, `paper1_mainStatementTargets_of_lowerPinnedContactData`, `paper1_mainStatementTargets_of_lowerPinnedRawContactData` | Pure headline assembly for `Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3`. These wrappers do not construct the branch data. |
| B | `paper1_positiveCriticalBranch_of_strictBarrier`, `paper1_positiveStrictBarrierBranch_of_contactBranch`, `strict_upperBarrier_MChi_of_contactContradictions`, `paper1_positiveContactBranch_of_lowerPinnedContactData`, `paper1_positiveContactBranch_of_lowerPinnedRawContactData`, `paper1_positiveLowerPinnedContactData_of_schauderContactData`, `paper1_positiveSchauderContactData_of_capSchauderContactData` | Good normalization/wiring chain for the positive branch: contact/no-contact -> strict barrier -> `ShenUpperBoundPositive`; lower pin supplies tail squeeze. |
| B | `paper1_mainlineStatementTargets_of_mainlineExistence`, `paper1_Theorem_1_2_of_mainlineExistence`, `paper1_Theorem_1_3_of_mainlineExistence` | Pure consumers of `Paper1MainlineExistence`. |
| B | `paper1_lemma51And52Targets_of_frontierData`, `paper1_Lemma_5_1_of_frontierData`, `paper1_Lemma_5_2_explicit_of_frontierData`, `paper1_Lemma_5_2_of_frontierData` | Pure wrappers over Lemma 5 frontier records. |
| B | `paper1_propositionTargets_of_frontierData`, `paper1_Proposition_1_1_of_frontierData`, `paper1_Proposition_1_2_of_frontierData` | Pure wrappers over Cauchy frontier data. |
| B | `paper1_combinedStatementTargets_of_data`, `paper1_combinedStatementTargets_of_strictBarrierData`, `paper1_combinedStatementTargets_of_lowerPinnedContactData`, `paper1_combinedStatementTargets_of_lowerPinnedRawContactData` | Combined wrappers. Only Lemma 2.5 is closed internally; the rest is carried. |
| C | `ConstructionNegSMPProvider` | Negative critical construction input for Theorem 1.1. I did not find a local unconditional producer in the inspected statement surface. |
| C | `Paper1PositiveCriticalFrozenStationaryBranch`, `Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch`, `Paper1PositiveCriticalFrozenStationaryContactBranch`, `Paper1PositiveLowerPinnedContactBranchData`, `Paper1PositiveLowerPinnedRawContactBranchData`, `Paper1PositiveLowerPinnedSchauderContactData`, `Paper1PositiveLowerPinnedCapSchauderContactData` | These are increasingly thin positive-branch frontiers. The routing is pure, but the lower-pinned Schauder principle/map data, no-contact facts, and construction content remain analytic. |
| C | `Paper1MainlineExistence` | Mainline B5 existence/stability package for Theorems 1.2/1.3 remains a supplied input. |
| C | `Paper1Lemma51FrontierData` | Real Lemma 5.1 frontiers: resolvent identity, continuity, derivative tending to zero, derivative bound, exponential derivative estimate. |
| C | `Paper1Lemma52FrontierData` | Monotonicity frontier for Lemma 5.2. |
| C | `Paper1PropositionFrontierData` | Whole-line Cauchy existence, max/bound branches, and convergence branches are still explicit analytic frontiers. |

## Paper2 details

| Class | Names | Audit |
|---|---|---|
| A | `intervalDomain_Proposition_2_4` | Interval mass/proposition component is already supplied in interval statement assembly. |
| B | `paper2_bootstrapEstimateTargets_of_branchData`, `paper2_Proposition_1_1_of_existenceData`, `paper2_mainTheoremTargets_of_solutionBranchData`, `paper2_localAndMainTheoremTargets_of_data`, `paper2_statementTargets_of_data` | Generic statement-layer wrappers only. The corresponding data records remain inputs. |
| B | `intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData` | Thin section-2 wrapper: consumes thin Lemma 2.6/2.7/Prop.2.2/Prop.2.3 data, uses local Prop.2.4, and takes Prop.2.5 from any route. |
| B | `intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierData`, `intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData`, `intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData`, `intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientTerminalEndpointFrontierData`, `intervalDomainPaper2_Proposition_2_5_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData` | Pure Prop.2.5 producers once the chosen Moser frontier is supplied. The raw-drop/mass-gradient/terminal endpoint package is the thinnest actual-atom statement surface I saw. |
| B | `intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData`, `intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientFrontierData`, `intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientTerminalEndpointFrontierData`, `intervalDomainPaper2_Corollary_2_1_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData` | Pure Cor.2.1 producers from the same atoms. |
| B | `IntervalDomainPaper2Prop25LowerUpperFrontierData.toIntegratedStepFrontierData`, `intervalDomainPaper2_Proposition_2_5_of_lowerUpperFrontierData`, `intervalDomainPaper2_Corollary_2_1_of_lowerUpperFrontierData` | Lower/upper split frontiers collapse to an integrated step and then to Prop.2.5/Cor.2.1. |
| B | `boundedBefore_of_corollary21_and_proposition25` | Cor.2.1 + Prop.2.5 + a bootstrap seed imply `IsPaper2BoundedBefore`. This is genuine wiring. |
| B | `Theorem_1_2_intervalDomain_slow_branch_of_corollary21_and_proposition25`, `Theorem_1_2_intervalDomain_critical_branch_of_corollary21_and_proposition25`, `Theorem_1_2_intervalDomain_of_corollary21_and_proposition25` | Theorem 1.2 assembly once Cor.2.1/Prop.2.5, continuation, and branch bootstraps/bounds are available. |
| B | `Theorem_1_2_intervalDomain_critical_regime_of_parameter_fields_and_eventual_sup_bound`, `Theorem_1_2_intervalDomain_critical_regime_of_Lemma_2_6_energy_and_eventual_sup_bound` | Good reductions: critical long-time boundedness can be supplied as an eventual sup-norm estimate; Cor.2.1 can be produced from Lemma 2.6 plus the energy derivation. |
| B | `intervalDomain_tier1_theorem11_chain_of_frontiers`, `intervalDomain_tier1_theorem11_chain_of_frontiers_bounded_initial`, `intervalDomain_tier1_theorem11_branch_chain_of_frontiers_bounded_initial`, `intervalDomain_tier1_theorem11_branch_chain_of_frontiers_inside_nonneg_bounded_initial` | One-shot Tier-1/Tier-2 chain wrappers. They return `Lemma_2_6`, `Lemma_4_1`, `Corollary_2_1`, and `Theorem_1_1` once the named frontiers are supplied. |
| C | `Paper2BootstrapEstimateBranchData`, `Paper2Proposition11ExistenceData`, `Paper2MainSolutionBranchData`, `Paper2LocalAndMainTheoremData`, `Paper2StatementData` | Generic branch-data packages remain frontiers unless interval-domain wrappers replace them. |
| C | `IntervalDomainPaper2BootstrapEstimateThinFrontierData` | Residual section-2 estimate package: `lemma26`, `lemma27`, `prop22`, `prop23`. |
| C | `IntervalDomainPaper2Prop25ActualAtomFrontierData` | Residual fields: `moserDissipation`, `relativeMoserInterpolation`, `quantitativeEndpoint`. |
| C | `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData` | Residual fields: `moserDissipation`, `relativeMassGradient`, `quantitativeEndpoint`. The relative field is lower-level than raw `RelativeMoserInterpolationBefore`. |
| C | `IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData` | Residual fields: `moserDissipation`, `relativeMassGradient`, `terminalEndpoint`. The endpoint is reduced to one terminal pointwise power-control estimate. |
| C | `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData` | Thinnest actual-atom surface inspected: `rawMoserDrop`, `relativeMassGradient`, `terminalEndpoint`. These are honest analytic atoms. |
| C | `IntervalDomainPaper2Prop25IntegratedStepFrontierData`, `IntervalDomainPaper2Prop25LowerUpperFrontierData` | Integrated-step path still needs either `integratedStep` or `lowerUpperFrontiers` plus `quantitativeEndpoint`. |
| C | `hEnergyFromCrossDiffusion` in Theorem 1.2 routes | Explicit weak/PDE energy derivation frontier from cross-diffusion estimate to `LpBootstrapEnergyInequality`. This is still analytic. |
| C | `hlocal`, `hglobalExtension`, `hslowBootstrap`, `hcriticalBootstrap`, `hcriticalGlobalBound` / `hcriticalEventualSupBound` in `IntervalDomainTheorem12` | Continuation and branch-specific bootstrap/long-time boundedness remain real PDE frontiers. |

## P3 Moser regularity and ladder packages

| Class | Names | Audit |
|---|---|---|
| A | `intervalDomain_initialPowerBound` | Algebraic real upper bound for the initial power integral is closed. |
| B | `intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical` | Right endpoint is wireable from global classical regularity on a longer horizon. Left endpoint remains `atZero`. |
| B | `intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity` | Closed energy continuity follows from interior energy continuity plus endpoint package. |
| B | `intervalDomain_powerTimeIntegrable_of_energyContinuous` | Power time-integrability follows from closed-time energy continuity on compact `[0,T]`. |
| B | `intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous` | Gradient time-integrability follows from closed-time gradient-energy continuity. This lowers the gradient residual from raw integrability to continuity if desired. |
| B | `intervalDomain_classicalRegularityData_of_globalClassicalRegularityData`, `intervalDomain_classicalRegularityData_of_gradientContinuityData`, `intervalDomain_regularFrontierData_of_lite`, `intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData`, `intervalDomain_integratedMoserFirstCrossingRegularity_of_lite`, `intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData`, `intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalRegularityData` | Regularity producers are now good wrappers. They correctly expose only endpoint/gradient residuals. |
| B | `intervalDomain_regularity_and_nonnegativity_of_classical`, `intervalDomain_regularity_and_nonnegativity_of_lite_classical` | Nonnegativity is supplied by the classical solution; regularity is supplied by the explicit data. |
| B | `intervalDomain_lowerAverageEpsilonData_of_classical`, `intervalDomain_lowerAverageEpsilonData_of_lite_classical`, and the corresponding lower-average/upper-data-gap wrappers in `P3MoserRegularityProducer.lean` | Data assembly only; it does not prove the dissipation, interpolation, lower-average, or upper-gap frontiers. |
| B | `IntervalDomainChemotacticDriftBound_of_LinfBound` | Finite-horizon pointwise/L∞ control of `u` gives the drift bound for the elliptic `v` slice. |
| B | `IntervalDomainMassLpSmoothingMoserLadderResiduals.corollary21`, `.proposition25`, `.to_routeResiduals`, `.aprioriBound` | The older mass/Lp/smoothing route is reconstructed once L2 seed regularity and actual Moser atoms are supplied. Drift is no longer a primitive residual here. |
| B | `IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21`, `.proposition25`, `.to_routeResiduals`, `.aprioriBound` | Same route with a supplied integrated first-crossing step. |
| B | `IntervalDomainMassLpSmoothingWindowFrontierResiduals.to_integratedStepResiduals`, `.to_routeResiduals`, `.aprioriBound` | Window frontier collapses to the integrated-step residual package. |
| C | `IntervalDomainPowerEnergyEndpointContinuity.atZero` and `IntervalDomainIntegratedMoserGlobalClassicalRegularityData.atZero` | Honest endpoint residual. `InitialTrace` controls positive times but does not identify the stored slice `u 0`. |
| C | `IntervalDomainIntegratedMoserClassicalRegularityData.gradientTimeIntegrable` | Honest gradient-energy time-integrability residual if kept in raw form. |
| C | `IntervalDomainIntegratedMoserClassicalGradientContinuityData.gradientEnergyContinuous` | Slightly better analytic frontier: closed-time gradient-energy continuity implies the raw integrability field, but is still not produced by the current classical API. |
| C | `IntervalDomainMassLpSmoothingMoserLadderResiduals.l2SeedRegularity` | Honest L2 seed regularity residual; comments correctly note the classical-solution interface does not determine `u 0`. |
| C | `IntervalDomainMassLpSmoothingMoserLadderResiduals.moserDissipation`, `.relativeMoserInterpolation`, `.quantitativeEndpoint` | Actual Moser atom frontiers. |
| C | `IntervalDomainMassLpSmoothingIntegratedStepResiduals.integratedStep`, `.quantitativeEndpoint` | Integrated first-crossing and endpoint/root-tower frontiers. |
| C | `IntervalDomainMassLpSmoothingWindowFrontierResiduals.windowFrontier`, `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.lowerUpperFrontiers` | Still analytic first-crossing/window frontiers; currently just routed to the integrated-step surface. |

## Paper3 details

| Class | Names | Audit |
|---|---|---|
| A | `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall`, `intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall`, `intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall` | Actual-linear small-sensitivity persistence is produced internally by `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`; no separate persistence package is carried in these theorems. |
| A | `Lemma_3_1_proved intervalDomain p`, `intervalDomain_upperEnvelopeMonotonicityRaw_supNorm p` | These concrete interval support targets are closed and used inside core statement assembly. |
| B | `paper3_Proposition_1_3_of_Paper2_Theorem_1_3`, `paper3_Proposition_1_4_of_Paper2_Theorem_1_2`, `paper3_proposition1Targets_of_paper2TheoremsData`, `paper3_proposition1Targets_of_paper2MainTargetsData` | Paper3 Proposition 1.3/1.4 can be routed from Paper2 Theorem 1.3/1.2. Proposition 1.2 remains independent. |
| B | `paper3_uniformPersistenceTargets_of_rawData`, `paper3_Theorem_2_2_of_branchData`, `paper3_compactnessRegularizationTargets_of_rawData`, `paper3_stability23To25Targets_of_branchData`, `paper3_mainlineTargets_of_data`, `paper3_mainlineTargets_of_paper2Theorem13Data`, `paper3_mainlineTargets_of_paper2TheoremsData`, `paper3_mainlineTargets_of_paper2MainTargetsData` | Generic Paper3 statement assembly is pure wrapping over raw/branch data. |
| B | `intervalDomainPaper3_negativeSensitivityResidual_of_frontierData` | Decomposes negative-sensitivity residual into global solution and eventual sup-bound fields. |
| B | `intervalDomain_paper3_proposition1Targets_of_frontierData`, `intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData`, `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData`, `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData` | Interval proposition routing is ready; negative-sensitivity remains a separate residual. |
| B | `intervalDomain_paper3_coreStatementTargets_of_coreExistence` | Core interval targets from `IntervalDomainInitialContinuityRaw` and `IntervalDomainSectorialMainlineCoreExistence`. Produces Lemma 3.1, Lemma 3.3, upper-envelope monotonicity, stability-chain Theorem 2.1 target, and sectorial Theorem 2.1/2.2 target. |
| B | `intervalDomain_paper3_coreStatementTargets_of_linear22Data` | Splits Theorem 2.1 persistence from raw linear Theorem 2.2 branches. |
| B | `intervalDomain_paper3_Theorem_2_1_of_persistence`, `intervalDomain_paper3_Theorem_2_1_partTargets_of_persistence`, `intervalDomain_paper3_Theorem_2_1_sectorial_of_persistence` | Theorem 2.1-specific entry points from `IntervalDomainSectorialTheorem21Persistence`. |
| B | `IntervalDomainPaper3CoreStatementActualLinear22Data.to_linear22Data`, `intervalDomain_paper3_coreStatementTargets_of_actualLinear22Data`, `intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData` | Actual-linear route produces persistence internally; raw linear Theorem 2.2 branches remain input. |
| B | `IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25` | In the actual-linear-small regime, Theorem 2.3 branches are vacuous from `0 < χ₀`, Theorem 2.5 branches are vacuous from `0 < a`, and only Theorem 2.4 fields remain. |
| B | `IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData`, `IntervalDomainPaper3MainlineActualLinear22ThinFrontierData.toCurrent`, `intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData`, `intervalDomain_paper3_statementTargets_of_actualLinear22FrontierData` | Thin actual-linear wrappers are good. They reduce the active stability frontiers to the positive nonminimal Theorem 2.4 pair plus compactness/resolvent and raw linear Theorem 2.2. |
| C | `NegativeSensitivityGlobalEventualBound`, `IntervalDomainPaper3NegativeSensitivityResidual`, `IntervalDomainPaper3NegativeSensitivityFrontierData.globalSolution`, `.eventualSupBound` | Honest Paper3 Proposition 1.2 residual. It is explicitly not derived from Paper2 main targets. |
| C | `IntervalDomainPaper3Proposition1FrontierData.criticalExistence` | Critical existence branch for Proposition 1.4 if not routed through Paper2 Theorem 1.2. |
| C | `Paper3UniformPersistenceRawData`, `Paper3Theorem22BranchData`, `Paper3CompactnessRegularizationRawData`, `Paper3Stability23To25BranchData` | Generic raw/branch Paper3 frontiers. The interval actual-linear route thins some of these but does not eliminate the core analytic content. |
| C | `IntervalDomainInitialContinuityRaw` | Concrete initial-continuity frontier for interval Lemma 3.3/stability norm routing. |
| C | `IntervalDomainSectorialMainlineCoreExistence`, or split fields `IntervalDomainSectorialTheorem21Persistence`, `LinearStabilityInstabilityNonminimalRaw`, `LinearStabilityInstabilityMinimalRaw` | Core sectorial existence and raw linear stability/instability frontiers. Actual-linear persistence is produced, but Theorem 2.2 raw branches are still carried. |
| C | `IntervalDomainPaper3SupNormCompactnessAPosData.compact`, `.resolvent` | Compactness and Neumann resolvent gradient-bound data are still analytic inputs. |
| C | `IntervalDomainPaper3Stability24ActualLinearFrontierData.global24`, `.exp24` | In the actual-linear-small path, these are the non-vacuous stability frontiers left after parameter contradictions remove Theorems 2.3 and 2.5 branches. |

## Minimal residual shortlist

The highest-leverage honest residuals still visible after the current wrappers are:

1. `IntervalDomainIntegratedMoserGlobalClassicalRegularityData.atZero` and either `gradientTimeIntegrable` or the better `IntervalDomainIntegratedMoserClassicalGradientContinuityData.gradientEnergyContinuous`.
2. Prop.2.5 actual Moser atoms, preferably at the thinnest inspected surface: `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.rawMoserDrop`, `.relativeMassGradient`, `.terminalEndpoint`.
3. Paper2 energy derivation: the `hEnergyFromCrossDiffusion` hypothesis used by `IntervalDomainTheorem12` and `IntervalDomainTierChain`.
4. Paper2 continuation/branch frontiers: `hlocal`, `hglobalExtension`, slow/critical bootstrap seeds, and critical eventual sup/global boundedness.
5. Paper1 genuine construction/Cauchy frontiers: `ConstructionNegSMPProvider`, the positive lower-pinned/contact/Schauder packages, `Paper1MainlineExistence`, `Paper1Lemma51FrontierData`, `Paper1Lemma52FrontierData`, `Paper1PropositionFrontierData`.
6. Paper3 independent negative-sensitivity frontier and interval initial-continuity/core sectorial/linear/compactness/stability frontiers.

## Small non-Zinan edit suggestions

No large proof edit is forced by this audit. The small useful edits are organizational, not analytic:

1. In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`, add one combined wrapper for the thinnest Prop.2.5 path:
   `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData -> Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p`. Separate wrappers already exist; a pair wrapper would make downstream calls less noisy.
2. In `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`, add a variant whose proposition field takes `IntervalDomainPaper3NegativeSensitivityFrontierData` directly and routes it through `intervalDomainPaper3_negativeSensitivityResidual_of_frontierData`; this would expose the remaining negative-sensitivity residual at the same granularity as the audit.
3. In `ShenWork/PDE/P3MoserRegularityProducer.lean`, keep future endpoint work focused on an `atZero` producer plus a `gradientEnergyContinuous` producer. The existing wrappers already turn those into the needed integrated-Moser regularity package.
