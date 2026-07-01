# UNDERSTANDING.md — Shen_work

## CURRENT STATE (2026-07-01, code-derived)

Authoritative checks from the current tree:
- Proof-hole scan: no proof-level `sorry`, `admit`, or custom `axiom`
  declaration remains under `ShenWork/**/*.lean`.  The current scanner command
  only matches two documentation/comment false positives:
  `Wiener/EWA/SourceRealizationFrontier.lean` and
  `Paper1/RotheFloorOrbitDataImpl.lean`.
- Last full remote build: after adding the Paper2 structured-Moser and
  actual-atom Proposition 2.5 frontiers, the common-free actual-atom
  Corollary 2.1 / Proposition 2.5 headline route, the mass-gradient reduction
  of the relative-Moser atom, the terminal-endpoint reduction of the
  quantitative endpoint atom, the raw-drop reduction of the nonnegative-B
  Moser dissipation atom, the common-free actual-atom full-statement route
  with explicit or solution-slice-produced a-priori frontiers, the Paper1
  positive upper-contact / Route-A direct remaining-contact refinements, and
  the Paper2/Paper3 integrated-Moser step-consumer closure layer, the
  fixed-interval integrated relative-Moser time-integral bridge, the
  integrated-Moser precrossing/window and high-excursion contradiction
  frontier plumbing, the Paper2 statement-level integrated-step and
  lower/upper split wrappers, and the reusable Paper3/PDE integrated-step and
  lower/upper split mass/Lp/smoothing residual packages,
  `lake build ShenWork` completed successfully on
  `uisai2:/dev/shm/shen_verify`, **8985 jobs**.  Target builds for
  `ShenWork.PDE.P3MoserIntegratedClosure`,
  `ShenWork.PDE.P3MoserActualWiring`, and
  `ShenWork.PDE.IntervalDomainMoserLadderAtoms`,
  `ShenWork.Paper2.IntervalDomainStatementAssembly`, and
  `ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` also completed
  successfully.  The Paper2/Paper3 wrappers and integrated-Moser bridge
  theorems have `#print axioms` output
  `[propext, Classical.choice, Quot.sound]`.
- The 2026-06-28 note below claiming "Paper 2 χ₀<0: 42 sorry" is stale; the
  repo no longer has proof-level `sorry`.
- Current target verification: after wiring the integrated-Moser data frontier
  through `P3MoserRegularityProducer`,
  `IntervalDomainMoserLadderAtoms`, and
  `Paper2.IntervalDomainStatementAssembly`, the remote uisai2 target build
  `lake build ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly` completed successfully
  (3749 jobs).  `P3MoserEnergyContinuity` also builds on uisai2 (3558 jobs).
  The new integrated-Moser wrappers print only
  `[propext, Classical.choice, Quot.sound]`.
  The PDE/Paper3 compatibility-surface cleanup also builds on uisai2 via
  `lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` (8573 jobs).
- The obsolete PDE-level
  `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`
  compatibility package has been removed.  The Paper3 compatibility-named
  lowerAverage/upperDataGap route now converts only to the integrated-step
  actual-linear route; the old PDE converter is no longer a live source
  surface.
- The four legacy first-crossing shortcut theorems in
  `P3MoserRegularityProducer` that still accepted lower-average / upper-gap
  frontier parameters after their proof bodies had switched to the direct
  threshold-plan route have been removed.  The uisai2 target build
  `lake build ShenWork.PDE.P3MoserRegularityProducer
  ShenWork.PDE.IntervalDomainMoserLadderAtoms
  ShenWork.Paper2.IntervalDomainStatementAssembly
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly` completed
  successfully (8573 jobs).
- New integrated-Moser closure status: `P3MoserIntegratedClosure` has the
  coefficient-gap surplus wrapper
  `integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality_coeffGap`.
  `P3MoserEnergyContinuity` proves strict-window derivative integrability of
  interval-domain Moser energies from classical regularity, identifies positive
  global-time derivatives with the explicit
  `intervalDomainPowerEnergyDerivIntegral`, and reduces full closed-window FTC
  to endpoint energy continuity plus the honest left-endpoint residual
  `IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability`.
  That residual is now further reduced, under global classical positivity, to
  the weighted Lp time-term residual
  `IntervalDomainLpWeightedTimeTermInitialWindowIntegrability`, with direct
  consumer wrappers ending at
  `intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm`.
  The weighted residual is further reduced to initial-window integrability of
  the single combined PDE-side scalar profile
  `q * intervalDomainLpDiffusionIntegral q u s -
    q * (params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s) +
    q * intervalDomainLpLogisticIntegral params q u s`, packaged as
  `IntervalDomainLpPDECombinedInitialWindowIntegrability` and consumed by
  `intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined`.
  The stronger componentwise entry point is retained: initial-window
  integrability of the three PDE component profiles
  `intervalDomainLpDiffusionIntegral`,
  `intervalDomainLpChemotaxisIntegral`, and
  `intervalDomainLpLogisticIntegral`, packaged as
  `IntervalDomainLpPDETermInitialWindowIntegrability` and consumed by
  `intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeTerms`;
  `intervalDomain_lpPDECombinedInitialWindowIntegrability_of_terms` bridges the
  componentwise package to the combined package.  Conversely,
  `intervalDomain_lpPDECombinedInitialWindowIntegrability_of_weightedTimeTerm_initial`
  and `intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial`
  identify the weighted-time and combined-PDE initial residuals under global
  classical regularity, using only positive times.
  A separate positive-left-start/initial-edge split is now exposed by
  `IntervalDomainLpPDETermPositiveStartWindowIntegrability`,
  `IntervalDomainLpPDETermPositiveStartWindowContinuity`, and
  `intervalDomain_lpPDETermClosedWindowIntegrability_of_initial_and_positiveStart`;
  the logistic component of the positive-start continuity package is now
  produced from global classical regularity by
  `intervalDomain_lpLogisticIntegral_continuousOn_positiveStart_of_global_classical`,
  and
  `intervalDomain_lpPDETermPositiveStartWindowContinuity_of_diffusionChemotaxis_global_logistic`
  reduces the remaining positive-start continuity frontier to the diffusion
  and chemotaxis scalar profiles.  The remaining positive-start scalar
  continuity is further reduced by
  `IntervalDomainLpDiffusionChemotaxisPositiveStartIntegrandJointContinuity`
  and
  `intervalDomain_lpPDETermPositiveStartWindowContinuity_of_integrandJoint_global_logistic`
  to joint continuity of the two lifted diffusion/chemotaxis integrands on
  `[a,b] × [0,1]`.  Current APIs still do not produce the initial-edge
  combined PDE-profile integrability from `InitialTrace` or endpoint energy
  continuity alone.

Current headline status:
- Short audit table for the Paper1--Paper3 headline wrappers:

  | area | closed or internally produced | honest residual/frontier inputs | deprecated or no-go route |
  | --- | --- | --- | --- |
  | Paper 1 | Lemma 2.5/Jensen; negative construction upper bound is reduced to the scalar stationary strictness `U 0 < 1` in `ConstructionNegSMPProvider`; positive-branch `ShenUpperBoundPositive` is split through the pure strict-`MChi` barrier wrapper; lower-pinned plateau and raw traps now produce right-tail asymptotics by pure squeeze; the positive upper-barrier interface no-contact is discharged from differentiability/kink avoidance; the strict exponential contact residual is closed on the `p.m * kappa c ≤ 1` subregime; Route-A has an hmk-aware constant-left-plateau residual package that converts to the remaining-contact package; `positiveBranchTailCap` and `kappa_lt_positiveBranchTailCap` close the scalar cap/gap arithmetic; `Paper1PositiveLowerPinnedContactBranchData`, `Paper1PositiveLowerPinnedRawContactBranchData`, `Paper1PositiveLowerPinnedRawSmoothContactBranchData`, `Paper1PositiveLowerPinnedSchauderContactData`, and `Paper1PositiveLowerPinnedCapSchauderContactData` keep the lower-pinned witness through the positive route; `Paper1MainStatementSMPMainlineData`, `Paper1MainStatementStrictBarrierData`, `Paper1MainStatementLowerPinnedContactData`, `Paper1MainStatementLowerPinnedRawContactData`, `Paper1MainStatementLowerPinnedRawSmoothContactData`, `Paper1CombinedStrictBarrierStatementData`, `Paper1CombinedLowerPinnedContactStatementData`, `Paper1CombinedLowerPinnedRawContactStatementData`, and `Paper1CombinedLowerPinnedRawSmoothContactStatementData` are the thinner conditional statement routes | `Paper1MainResultsData`, `Paper1MainlineExistence`, proposition frontiers, Lemma 5.1/5.2 frontiers, positive construction lower-pinned cap Schauder/contact data, smooth-branch no-contact comparison outside the `hmκ` subregime, and fixed-point/stationarity/SMP inputs | tail-asymptotic identity wrappers from bare stationarity remain non-producers; the lower-pinned plateau/raw squeeze route is the active tail producer; `hmκ` is not implied by the base positive hypotheses |
  | Paper 2 | interval-domain Theorem 1.1 for `χ₀ = 0`; `χ₀ = 0` local existence in the local-free routes; Proposition 2.4 in the thin section-2 route; `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData` names the current preferred Theorem 1.1--1.3 headline route with both Corollary 2.1 and Proposition 2.5 produced from actual Moser atoms; `IntervalDomainPaper2PreferredChiZeroStatementActualAtomCor21FrontierData` is the matching full-statement route with the a-priori package kept explicit; the `...ActualAtomMassGradientCor21...` variants additionally reduce the relative-Moser atom to mass-gradient inputs; `...ActualAtomMassGradientTerminalEndpointCor21...` variants further replace the endpoint tower field by one terminal pointwise power-control input; `...ActualAtomRawDropMassGradientTerminalEndpointCor21...` variants lower the dissipation atom to raw pointwise physical drop data via `moserDissipationDropBeforeNonnegB_of_raw_drop`; `...SolutionInterpolation...` statement variants produce the a-priori package from positive solution-slice interpolation; `IntervalDomainPaper2Prop25IntegratedStepFrontierData` exposes the same statement-layer Corollary 2.1 / Proposition 2.5 / thin section-2 route from a supplied integrated first-crossing step and quantitative endpoint; `IntervalDomainPaper2Prop25LowerUpperFrontierData` is the matching lower-average / upper-gap split statement route; `P3MoserIntegratedClosure` proves the routine Moser chain/all-exponent/endpoint consequences from a supplied integrated first-crossing one-step predicate, the fixed-interval integrated dissipation / relative-Moser time-integral bounds, the precrossing-to-window upper-bound package, and the pure high-excursion contradiction wrapper needed before the genuine first-crossing argument | finite-horizon alternative, actual Prop25 atoms (raw pointwise Moser drop or nonnegative-B Moser dissipation, plus either quantitative endpoint/root tower or terminal pointwise endpoint; mass-gradient relative data in the reduced route), positive solution-slice interpolation or explicit `IntervalDomainPaper2AprioriTargets` for full statements, global extension, bootstrap/eventual-sup fields, and thin section-2 Lemma 2.6/2.7/Proposition 2.2/2.3 fields; the production of lower-average / upper-gap frontiers, and hence of `IntegratedMoserFirstCrossingStep`, from integrated energy/relative interpolation/regularity remains a genuine analytic frontier | routes carrying global `IntervalDomainInterpolation`, refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`; `OldUnitIntervalPowerGNYoungForMoser` is legacy/false for constants and should not feed new Moser routes; raw pointwise Moser drop, production of the integrated first-crossing step, and terminal endpoint production are still real atoms, not consequences of the current abstract APIs |
  | Paper 3 | actual-linear-small Theorem 2.1 persistence; Proposition 1.3/1.4 can be routed through Paper2 Theorem 1.3/1.2 or Paper2 main targets; terminal pointwise endpoint now has a named quantitative-endpoint bridge; the actual-linear-small mainline has a direct integrated-step route and a thinner lower-average / upper-gap split route that supply route-level Corollary 2.1 / Proposition 2.5 from `IntegratedMoserFirstCrossingStep`, without deriving old pointwise Moser atoms; the reusable cores of those routes are now `IntervalDomainMassLpSmoothingIntegratedStepResiduals` and `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals` in `IntervalDomainMoserLadderAtoms`, while the Paper3 local package only converts closed-energy trace data to the generic `l2SeedRegularity` field; `IntervalDomainPaper3SupNormCompactnessRegularizationData` removes only the structural `upperEq` field by fixing the sup envelope; `IntervalDomainPaper3NegativeSensitivityFrontierData` decomposes `negativeBound` into global-solution and eventual-sup residuals | `negativeBound` or its decomposed global-solution/eventual-sup frontiers, integrated first-crossing step production, terminal Moser inputs, spectral orbit, continuation/gluing, compactness/regularization, and stability frontiers | Paper2 Theorem 1.1 does not imply Paper3 Proposition 1.2 under the current API; see `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`; do not derive `MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore` from Corollary 2.1 |

  Thus the tree is proof-hole-free, but most `...Data` / `...FrontierData`
  headline wrappers are conditional assembly interfaces, not no-assumption
  paper theorems.
- **Paper 1:** statement targets are still reduced to explicit frontier
  packages.  `Paper1MainResultsData` carries the full Theorem 1.1--1.3
  statement bridge; `Paper1MainlineExistence` carries the B5
  stability/uniqueness mainline.  For the B1 construction wrappers, the
  base-barrier Lipschitz condition is now derived from the Lemma 4.2 parameter
  conditions rather than carried as a separate floor field: current wrappers include
  `b1_chiNeg_existence_paper_clean_autoBar_of_cubeApproxData`,
  `b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData`,
  `b1_chiNeg_existence_paper_min_noBar_of_cubeApproxData`,
  `b1_chiPos_existence_paper_min_noBar_of_cubeApproxData`,
  `b1_chiNeg_existence_paper_min_core_noBar_of_cubeApproxData`,
  `b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData`, and
  `b1_chiNeg_existence_paper_routeA_core_noBar_of_cubeApproxData` /
  `b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData`.
  The Route-A producer residual also has thinner source-box parameter wrappers,
  `b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData` and
  `b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData`, which
  replace the monolithic `PaperGreenStepInputRouteACore` input by explicit
  `PerStepBoxParams` / `PerStepBoxZWitness` / Route-A rest / lower-raw aux data.
  The negative construction's upper-bound slot also has a thinner statement
  route: `ConstructionNegSMPProvider` replaces the full carried
  `ShenUpperBoundNegative c U` field by the scalar stationary strictness
  `U 0 < 1` for each produced fixed point.  The wrappers
  `constructionNeg_of_lowerPinnedSchauderData_smp`,
  `constructionNeg_of_provider_smp`,
  `Theorem_1_1.of_constructionNeg_provider_smp`, and the statement-layer
  `paper1_Theorem_1_1_of_constructionNegSMPProvider` then derive the strict
  upper bound from `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple`.
  On the positive construction branch, `ShenUpperBoundPositive` now has the
  pure `MChi` normalization bridge
  `ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi`, and
  `Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch` /
  `Paper1MainStatementStrictBarrierData` expose the upper-bound frontier as
  the stricter analytic comparison
  `∀ x, U x < upperBarrier (kappa c) (MChi p) x`.  The further
  `Paper1PositiveCriticalFrozenStationaryContactBranch` route splits that
  comparison into the non-strict monotone trap bound plus local no-contact
  facts on the constant branch, exponential branch, and interface of the
  nonsmooth upper barrier.  `Paper1PositiveLowerPinnedContactBranchData` keeps
  the produced profile's `InLowerPinnedMonotoneTrap` witness and rate cover, so
  the tail field of the contact branch is discharged by the pure squeeze
  theorem rather than carried.  `Paper1PositiveLowerPinnedSchauderContactData`
  is the corresponding lower-pinned fixed-point route through
  `b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin`
  with `M = MChi p`; despite the name of that reusable theorem, the wrapper is
  sign-agnostic in `p` and the positive assumptions are carried at the
  statement layer.  The scalar branch ceiling is named
  `positiveBranchTailCap`; `kappa_lt_positiveBranchTailCap` proves
  `kappa c < positiveBranchTailCap p c` for `2 < c`, so the cap-specialized
  route `Paper1PositiveLowerPinnedCapSchauderContactData` can set
  `κtilde = positiveBranchTailCap p c` and discharge both the lower-barrier
  gap and rate-cover fields by pure arithmetic.  The current Route-A
  lower-pinned producers expose a raw lower-barrier pin rather than the plateau
  pin, and this is now matched by `Paper1PositiveLowerPinnedRawContactBranchData`
  plus the statement-level `Paper1MainStatementLowerPinnedRawContactData` and
  `Paper1CombinedLowerPinnedRawContactStatementData` routes.  `UpperBarrierContact`
  further splits `PositiveUpperBarrierContactContradictions` into the residual
  `PositiveUpperBarrierSmoothBranchNoContact` plus the closed theorem
  `positiveUpperBarrier_interfaceNoContact_of_regular_stationary`, reusing
  `maxSub_upperBarrier_ne_interface` and the C² regularity frontier.  It also
  proves the exponential-branch operator comparison directly as
  `positiveUpperBarrier_expOperatorCompareAtContact_of_regular_stationary`.
  The surviving smooth residual is now
  `PositiveUpperBarrierRemainingContactResidual`: the generic wrapper still has
  a `no_const_left_plateau` field, but `UpperBarrierContact` proves this field
  from `FrozenStationaryWaveProfile.lim_neg_inf.1` once `0 < p.χ < 1`, via
  `MChi_ne_one_of_chi_pos_lt_one`.  The thinner
  `PositiveUpperBarrierExpStrictContactResidual` therefore leaves only the
  strict exponential superbarrier residual at contact on that profile route.
  `Statements` now proves the strict positive exponential-region operator
  estimate as `frozenWaveOperator_exp_neg_of_chi_nonneg` and
  `frozenWaveOperator_upperBarrier_exp_region_neg_of_chi_nonneg`; with the
  standard scalar side condition `p.m * kappa c ≤ 1`, `UpperBarrierContact`
  packages this as
  `positiveUpperBarrier_expStrictSuperAtContact_of_positive_region`,
  `PositiveUpperBarrierConstLeftPlateauResidual.of_profile_chi_pos`,
  `PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion`,
  `PositiveUpperBarrierRemainingContactResidual.of_positive_region_profile_chi_pos`,
  `positiveUpperBarrierSmoothBranchNoContact_of_positive_region_profile_chi_pos`,
  and
  `PositiveUpperBarrierContactContradictions.of_profile_chi_pos_hmk_regularStationary`.
  This `hmκ` condition is a genuine extra scalar frontier, not a consequence of
  the base positive branch hypotheses: the repo contains
  `not_Lemma_4_1_positive_hypotheses_force_m_kappa_le_one`.
  The direct bridge
  `positiveUpperBarrierSmoothBranchNoContact_of_expStrict_profile_chi_pos`
  closes smooth no-contact from this thinner residual, and
  `PositiveUpperBarrierContactContradictions.of_expStrict_profile_chi_pos_regularStationary`
  closes the full contact package once `0 < kappa c` and regular stationary
  data are present.
  The corresponding raw
  smooth-contact and remaining-contact statement routes are
  `Paper1PositiveLowerPinnedRawSmoothContactBranchData`,
  `Paper1MainStatementLowerPinnedRawSmoothContactData`, and
  `Paper1CombinedLowerPinnedRawSmoothContactStatementData`, plus
  `Paper1PositiveLowerPinnedRawRemainingContactBranchData`,
  `Paper1MainStatementLowerPinnedRawRemainingContactData`, and
  `Paper1CombinedLowerPinnedRawRemainingContactStatementData`.  `PositiveRawRouteAAssembly`
  specializes the exact Lemma 4.2 parameter conditions to
  `positiveBranchTailCap` and wires `Paper1PositiveLowerRawCapRouteAParamData`
  / `Paper1PositiveLowerRawCapRouteASmoothParamData` /
  `Paper1PositiveLowerRawCapRouteARemainingParamData` into those raw-contact,
  raw smooth-contact, and remaining-contact interfaces.  On the `hmκ`
  subregime, `Paper1PositiveLowerRawCapRouteAHmkConstParamData` carries only
  `PositiveUpperBarrierConstLeftPlateauResidual` plus the scalar
  `p.m * kappa c ≤ 1`; `paper1_routeARemainingParamData_of_routeAHmkConstParamData`
  converts it back into the existing remaining-contact route, and
  `paper1_positiveRawRemainingContactData_of_routeARemainingParamData` /
  `paper1_positiveRawRemainingContactData_of_routeAHmkConstParamData`
  now wire Route-A remaining-contact and hmk-aware constant-branch data
  directly to `Paper1PositiveLowerPinnedRawRemainingContactBranchData`.
  The statement wrappers
  `paper1_mainStatementTargets_of_routeARemainingParamData`,
  `paper1_mainStatementTargets_of_routeAHmkConstParamData`,
  `paper1_combinedStatementTargets_of_routeARemainingParamData`, and
  `paper1_combinedStatementTargets_of_routeAHmkConstParamData`
  route the same data directly to Paper1 main/combined statement targets.
  Separately,
  `paper1_positiveRawSmoothContactData_of_routeAHmkConstParamData`,
  `paper1_positiveContactBranch_of_routeAHmkConstParamData`, and
  `paper1_positiveStrictBarrierBranch_of_routeAHmkConstParamData` reuse the
  downstream wrappers.  The remaining positive residuals are the
  Route-A/Schauder analytic data themselves: lower-pin preservation by the
  positive map, map/compactness data, stationarity/flat-left inputs, C²
  regularity data, and either the strict exponential superbarrier at contact or
  the scalar `hmκ` plus constant-left-plateau route above.  The
  no-left-plateau input is no longer separate on profile routes with
  `0 < p.χ < 1`.  The right-tail
  asymptotic itself now has
  the pure lower-pinned squeeze producers
  `HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap` and
  `HasWaveRightTailAsymptotic_of_lowerPinnedRawMonotoneTrap`, with
  `lowerPinnedMonotoneTrap_tail_family_for_branch` and
  `lowerPinnedRawMonotoneTrap_tail_family_for_branch` covering the full branch
  interval once the lower-barrier exponent dominates the branch ceiling.
- **Paper 2:** `intervalDomain_theorem_1_1_chiZero_unconditional` proves
  Theorem 1.1 on the interval for χ₀ = 0.  This producer is now wired through
  `IntervalDomainStatementAssembly` as
  `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` and through the
  `χ₀ = 0` main/local+main/statement-target bundles; those routes carry no
  Theorem 1.1 half-step frontier package, though they still carry the
  independent Proposition 1.1 / Theorem 1.2 / Theorem 1.3 frontiers where
  applicable.  The `χ₀ = 0` Proposition 1.1 route now also has thin wrappers
  `IntervalDomainPaper2Proposition11ChiZeroFrontierData`,
  `IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData`, and
  `IntervalDomainPaper2StatementChiZeroThinFrontierData`: these discharge the
  local-existence field from `intervalDomain_localExistence_chiZero_unconditional`,
  so Proposition 1.1 only carries the independent finite-horizon alternative in
  that regime.  The Theorem 1.2/1.3 part of the `χ₀ = 0` route also has a
  thinner interpolation-positive statement route:
  `IntervalDomainPaper2Theorem12And13InterpolationFrontierData`,
  `IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData`,
  `IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData`, and
  `IntervalDomainPaper2StatementChiZeroInterpolationFrontierData`.  These
  wrappers remove the old carried `SemigroupEstimateData` / Lemma 2.1 / Lemma
  2.6 / Lemma 4.1 / Corollary 2.1 theorem fields from the main Theorem 1.2/1.3
  route, replacing them by explicit interpolation, energy, gradient-chain,
  mass-control, power-integrability, branch-bootstrap, and eventual sup-norm
  frontiers.  That interpolation route is not a valid discharge target as it
  stands: the current `IntervalDomainInterpolation` statement is known false
  as literally stated
  (`IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`),
  so any package containing it is a vacuous conditional until the statement is
  repaired.  The current preferred χ₀=0 headline and full-statement route
  avoids that false global premise by using
  `IntervalDomainClassicalSolutionPositiveInterpolation`, a solution-slice
  mass-gradient interpolation residual with the positive constant needed by
  Lemma 4.1.  It proves Lemma 4.1 via
  `Lemma_4_1_intervalDomain_of_solution_interpolation_frontier`, drops the
  positive-constant field for Corollary 2.1 via
  `IntervalDomainClassicalSolutionInterpolation_of_positive`, and is exposed
  by
  `IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData`,
  `IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationFrontierData`,
  `IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData`,
  and
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationFrontierData`.
  The same positive solution-slice route now also has H2-source and
  logistic-source main/local+main/full-statement wrappers:
  `IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationFrontierData`
  and
  `IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationFrontierData`
  are the full-statement entry points.  The full-statement routes now also
  have thinner bootstrap variants,
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationBootstrapFrontierData`,
  `IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationBootstrapFrontierData`,
  and
  `IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationBootstrapFrontierData`.
  These replace the carried `IntervalDomainPaper2Corollary21FrontierData`
  field by the smaller `Paper2BootstrapEstimateBranchData`; Corollary 2.1 is
  produced from the nested positive solution-slice common data.  There is now a
  further section-2-thin variant for each of these routes,
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinFrontierData`,
  `IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationSection2ThinFrontierData`,
  and
  `IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationSection2ThinFrontierData`.
  These replace the full `Paper2BootstrapEstimateBranchData` by
  `IntervalDomainPaper2BootstrapEstimateThinFrontierData`, keeping only the
  Lemma 2.6 / Lemma 2.7 / Proposition 2.2 / Proposition 2.3 branch frontiers;
  Proposition 2.4 comes from the proved interval-domain mass estimate
  `intervalDomain_Proposition_2_4`, and Proposition 2.5 comes from the nested
  Theorem 1.2/1.3 data.  This is still conditional, but no longer rests on the
  step-function counterexample premise, including in the full statement-target
  wrappers.  The preferred `χ₀ = 0` positive solution-slice route now also has
  a local-existence-free version,
  `IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData`,
  with main/local/full-statement wrappers ending at
  `IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.
  These remove the Theorem 1.2/1.3 `localExistence` field in the `χ₀ = 0`
  route by inserting `intervalDomain_localExistence_chiZero_unconditional`;
  the remaining full-statement residuals are the finite-horizon alternative,
  positive solution-slice interpolation/energy/global-extension/bootstrap and
  eventual sup-bound frontiers, plus the section-2 thin fields.
  The preferred headline-only route for Theorems 1.1--1.3 is now named by the
  common-free actual-atom route
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData`.
  It excludes Proposition 1.1 and section-2 target fields from headline
  accounting, produces both `Corollary_2_1` and `Proposition_2_5` from the
  same actual Moser atom package, and carries no `cGrad` parameter.  The older
  `IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData` and
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomFrontierData`
  remain as compatibility routes through the positive solution-slice common
  data.  Proposition 2.5 itself is split two ways:
  `IntervalDomainPaper2Prop25StructuredMoserFrontierData` exposes the existing
  structured-Moser producer with explicit `pSeq`/`rootBound`, energy,
  dissipation, relative interpolation, power-integrability, and endpoint
  fields; `IntervalDomainPaper2Prop25ActualAtomFrontierData` is the smaller
  preferred route through
  `intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`, carrying only
  nonnegative-B Moser dissipation, relative Moser interpolation, and the
  quantitative endpoint/root-tower producer.  The further
  `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData` route proves
  the relative-Moser atom from
  `intervalDomain_relativeMoserInterpolationBefore_of_massGradient`; its
  inputs are an `LpMassGradientInterpolationEstimate`, the gradient-chain
  comparison, a positive `cGrad`, and
  `MoserMassPowerToCurrentLpLowerOrder`.  It still honestly carries
  nonnegative-B Moser dissipation and the quantitative endpoint.  The
  corresponding thin section-2 wrappers are
  `intervalDomainPaper2_bootstrapEstimateTargets_of_thinStructuredMoserFrontierData`
  and
  `intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData`,
  with
  `intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomMassGradientFrontierData`
  for the mass-gradient relative-Moser route;
  the preferred full-statement wrappers are
  `intervalDomainPaper2_preferredChiZeroStatementTargets_of_structuredMoserFrontierData`
  and
  `intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierData`.
  The matching full-statement actual-atom routes are
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomCor21FrontierData`
  and
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientCor21FrontierData`.
  These use the common-free actual-atom path for section 2 and local+main
  theorem accounting, while keeping `IntervalDomainPaper2AprioriTargets` as an
  explicit independent field.  This is intentional: the current actual-atom
  Moser package does not prove Lemma 4.1.  The solution-interpolation variants
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomCor21SolutionInterpolationFrontierData`
  and
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientCor21SolutionInterpolationFrontierData`
  replace that explicit a-priori field by the existing positive solution-slice
  interpolation producer.  The terminal-endpoint mass-gradient route
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData`
  additionally replaces the endpoint `pSeq` / `rootBound` tower atom by one
  terminal `IntervalDomainMoserPointwisePowerControlBefore` estimate and
  rebuilds the old endpoint shape with constant sequences.  The raw-drop
  terminal route
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData`
  and its full-statement counterpart
  `IntervalDomainPaper2PreferredChiZeroStatementActualAtomRawDropMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData`
  additionally replace the black-box `MoserDissipationDropBeforeNonnegB`
  field by raw physical pointwise drop data, using the proved bridge
  `moserDissipationDropBeforeNonnegB_of_raw_drop`.  New headline work
  should not use
  `OldUnitIntervalPowerGNYoungForMoser` or the refuted global
  `IntervalDomainInterpolation` premise; the current code also records that
  abstract `MoserDissipationDropBeforeNonnegB` is false on a unit-linear-drop
  counterexample.  The new `P3MoserIntegratedClosure` module now proves the
  routine Moser chain, all-exponent, and quantitative-endpoint consequences
  from a supplied `IntegratedMoserFirstCrossingStep`.  It also packages the
  fixed-interval algebra needed on the faithful integrated route:
  `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`,
  `intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound`,
  `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound`,
  `intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on`,
  `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound`, and
  `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`.
  It also adds the honest precrossing/window layer:
  `IntegratedMoserPrecrossingIntervalData`,
  `integratedMoserPrecrossingIntervalData_of_regular_window`,
  `IntegratedMoserWindowUpperBoundData`, and
  `integratedMoser_windowUpperBoundData_of_precrossing` package regularity,
  energy nonnegativity, a current-exponent Icc bound, integrated dissipation,
  and relative interpolation into a fixed-window upper bound.  The auxiliary
  `IntegratedMoserWindowUpperBoundWitness` exposes the actual `Gbound`/`Ceps`
  witnesses so that a later strict lower-average gap is tied to the same
  fixed-window estimate, not to arbitrary larger witnesses.  The new
  `IntegratedMoserHighExcursionContradictionWindowFrontier` and
  `integratedMoserFirstCrossingStep_of_windowFrontier` then isolate the pure
  contradiction step from a high pointwise excursion to the supplied one-step
  Moser predicate.  The next producer split is now named as well:
  `IntegratedMoserHighExcursionLowerAverageWindowFrontier` is the
  thickness/modulus lower-average frontier, while
  `IntegratedMoserWindowUpperGapWitnessFrontier` is the quantitative
  `eps`/`Ceps` upper-gap frontier.  The preferred strict-gap interface is now
  `IntegratedMoserWindowUpperDataGapFrontier`: it receives the proved
  fixed-window upper-bound data producer and only has to close the gap for one
  selected actual witness, avoiding the older over-strong requirement that the
  same strict gap hold for every possible larger upper-bound witness.
  `integratedMoser_windowUpperBoundData_of_lowerAverageWindow` supplies that
  fixed-window data from regularity, nonnegativity, dissipation, and relative
  interpolation, and
  `integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap` converts the
  new gap chooser to the existing witness frontier.  The older
  `IntegratedMoserWindowUpperGapEpsilonFrontier` remains as a compatibility
  stronger interface via
  `integratedMoserWindowUpperDataGapFrontier_of_epsilonGap`.  Their pure
  assembler is
  `integratedMoserContradictionWindowFrontier_of_lowerAverage_upperGap`.
  These are still fixed-window or conditional frontier interfaces; they do not
  extract a pointwise next-exponent bound from a bare time-integral estimate.
  The remaining faithful hard theorem is the production of those
  high-excursion lower-average and upper-gap frontiers from integrated
  dissipation, relative interpolation, and all-exponent regularity, including
  high-excursion thickness, lower-average estimates, and the remaining
  quantitative epsilon-gap closure.
  The raw pointwise drop and terminal pointwise endpoint are still analytic
  inputs, not derived from the current abstract APIs.
  General
  χ₀ ≤ 0 is not a no-frontier headline yet:
  `paper2_theorem_1_1_general_chi_bform` still explicitly requires `hlocal`
  and `IntervalDomainUniformLocalExistence`.  The B-form
  branch now has `paper2_theorem_1_1_general_chi_bform_from_quant`, which
  replaces the uniform-local-existence input by the quantitative local factory
  `hQuant` via the existing restart/glue/sup-norm continuation machinery; the
  negative-part frontier branch has the analogous
  `paper2_theorem_1_1_general_chi_bform_negpart_from_quant`.  The
  squared-barrier branch now also has
  `paper2_theorem_1_1_general_chi_bformSq_from_quant`, replacing its
  `IntervalDomainUniformLocalExistence` input by the same quantitative factory;
  the banked squared-barrier wrapper
  `paper2_theorem_1_1_general_chi_bformSq_of_banked_from_quant` does the same
  after `positiveDatumBFormLocalHypSq_of_banked`.  The deeper squared-barrier
  branches are also wired to the quantitative factory:
  `paper2_theorem_1_1_general_chi_bformSq_regular_from_quant` and
  `paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_quant`, and the
  concrete-banked variant
  `paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_quant`.  The
  `SqRegular`/`SqDeepest` plumbing uses the banked PDE identity
  `BFormBankedInputs.hpde_u` directly instead of the stale spectral-agreement
  shim `hpde_of_BFormBankedInputs`.  These B-form branches are also wired one
  layer deeper through the threshold/Picard route:
  `*_from_picardFrontier_persistence` wrappers replace `hQuant` by
  `PicardRestartFrontier`, `ClassicalMinPersistence`, and the per-datum
  `hlocal` seed, using the already-proved
  `ThresholdQuantBridge.quantitativeLocalExistence_of_picardFrontier_persistence`.
  These B-form branches additionally have `*_from_picardFrontier_boundary`
  wrappers, which replace `ClassicalMinPersistence` by the named boundary
  min-point derivative residual `BoundaryMinPersistenceBound`, consumed via
  `MinPersistenceAtoms.classicalMinPersistence_of_boundary`.  For the base and
  negative-part full-PID branches, the `*_of_BForm` variants also discharge the
  explicit per-datum `hlocal` seed from the B-form local package itself.  The
  `*_picardLimitFrontier_*_of_BForm` variants for those same two branches also
  replace `PicardRestartFrontier` by the unified Picard-limit residual
  `ConeQuantBridge.PicardLimitRestartFrontier`.  The squared-barrier branches
  have analogous `*_picardLimitFrontier_*` variants for the restart residual,
  but still keep `hlocal`, because their B-form packages currently cover
  `PaperPositiveInitialDatum`, not the full `PositiveInitialDatum` class needed
  by F1.
- **Paper 3:** the generic `Paper3MainlineTargets` and interval-domain
  sectorial endpoints are still assembled from explicit frontier/existence
  packages such as `Paper3MainlineData` and
  `IntervalDomainSectorialMainlineExistence`; these are not yet no-assumption
  PDE constructions.  Newer interval-domain Theorem 2.1 entry points
  `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall`,
  `intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall`, and
  `intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall` consume
  the proved actual-linear-small persistence producer directly, removing the
  explicit `IntervalDomainSectorialTheorem21Persistence` input in the
  `m = 1`, `1 ≤ β`, `0 < χ₀ < a/(μ*Theta_beta (β-1))` subregime.  This does
  not discharge the Theorem 2.2 local-stability package or the general
  sectorial mainline existence package.  The interval-domain mainline and
  statement assembly also now have reduced-analytic entry points
  `IntervalDomainPaper3MainlineReducedAnalyticFrontierData` /
  `IntervalDomainPaper3StatementReducedAnalyticFrontierData`, with wrappers
  `intervalDomain_paper3_mainlineTargets_of_reducedAnalyticFrontierData` and
  `intervalDomain_paper3_statementTargets_of_reducedAnalyticFrontierData`.
  These replace the monolithic
  `IntervalDomainSectorialMainlineCoreExistence` field by
  `IntervalDomainSectorialMainlineReducedAnalyticFacts`, using the existing
  `.to_coreExistence` bridge; small-data Cauchy fields remain explicit, while
  the four persistence fields are reduced to pointwise lower-barrier facts.
  A deeper a-priori route,
  `IntervalDomainPaper3MainlineAprioriFrontierData` /
  `IntervalDomainPaper3StatementAprioriFrontierData`, uses
  `IntervalDomainSectorialMainlineAprioriFacts.to_coreExistence` to replace the
  small-data Cauchy fields by continuation plus mass/Lp/smoothing residuals,
  while keeping the same pointwise lower-barrier persistence facts.  The
  actual-linear-small route is now wired one layer deeper through
  `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts`,
  `IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData`, and
  `IntervalDomainPaper3StatementAprioriActualLinearSmallFrontierData` in
  `IntervalDomainActualLinearStatementAssembly`: in the `m = 1`, `1 ≤ β`,
  `0 < χ₀ < a/(μ*Theta_beta (β-1))` subregime it removes the pointwise
  persistence package from the a-priori mainline by inserting
  `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`.  The
  remaining actual-linear-small statement residuals are the spectral orbit
  bound, continuation/gluing, mass/Lp/smoothing route, compactness,
  stability, and Proposition 1.x packages.  The Proposition 1.x package now
  has a Paper2-theorem route,
  `IntervalDomainPaper3Proposition1FromPaper2TheoremsData`, which replaces the
  Paper3 Proposition 1.3 and Proposition 1.4 existence-branch fields by Paper2
  `Theorem_1_3` and `Theorem_1_2`; the remaining proposition inputs on that
  route are the negative-sensitivity bound plus those two Paper2 headline
  theorem inputs.  There is now also a Paper2-main-target route,
  `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData`, backed by the
  generic `Paper3Proposition1FromPaper2MainTargetsData`: it extracts Paper2
  Theorems 1.2/1.3 from `IntervalDomainPaper2MainTheoremTargets`, so Paper3
  Proposition 1.x can depend on the Paper2 headline theorem bundle rather than
  duplicate theorem fields.  A still thinner
  Moser-ladder actual-linear-small route is exposed by
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallFrontierData`, and
  `IntervalDomainPaper3StatementMoserActualLinearSmallFrontierData`.  This
  route replaces the old mass/Lp/smoothing package by the Moser-ladder atoms
  and derives the old `a_pos` / `chi_nonneg` fields from the actual-linear
  parameter hypotheses; remaining Moser-route inputs are boundedness,
  L²-seed regularity, Moser dissipation, relative Moser interpolation, and the
  quantitative endpoint tower.  A still thinner closed-energy variant is now
  exposed by
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallClosedEnergyFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallClosedEnergyFrontierData`:
  it replaces the naked `l2SeedRegularity` field by the existential closed
  integrated-energy trace package
  `P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData`, using the proved
  `l2SeedRegularity_of_closedEnergyIdentityTraceData` bridge.  The energy
  identity itself remains a residual; the seed regularity conversion is no
  longer a residual.  The closed-energy Moser route now has a still thinner
  CEGrad variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallCEGradFrontierData`, and
  `IntervalDomainPaper3StatementMoserActualLinearSmallCEGradFrontierData`.
  This replaces the black-box `relativeMoserInterpolation` field by a
  mass-gradient/lower-order interface (`cGrad` positivity,
  `LpMassGradientInterpolationEstimate`, the gradient-comparison inequality,
  and `MoserMassPowerToCurrentLpLowerOrder`), then uses the proved
  `P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient`
  bridge to recover `RelativeMoserInterpolationBefore`.  Those four CEGrad
  subfields are still analytic residuals; only the conversion from them to
  relative Moser interpolation is discharged.  The route also has a
  CERawGrad variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallCERawGradFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallCERawGradFrontierData`.
  This further replaces the black-box `moserDissipation` field by the raw
  pointwise nonnegative-`B` drop condition and uses the proved
  `moserDissipationDropBeforeNonnegB_of_raw_drop` bridge to recover
  `MoserDissipationDropBeforeNonnegB`.  The raw drop is still a residual; the
  packaging bridge is proved.  The route now has a CETerminal variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalFrontierData`.
  This replaces the abstract `quantitativeEndpoint` tower field by direct
  existence of one terminal pointwise power-control estimate
  `IntervalDomainMoserPointwisePowerControlBefore`; the proved conversion uses
  constant `pSeq` / `rootBound` sequences to recover
  `IntervalDomainMoserQuantitativeEndpoint`.  The terminal pointwise estimate
  remains a residual; the tower-packaging bridge is proved.  The CETerminal
  residual no longer carries the full `IntervalDomainBoundednessHyp` bundle:
  it carries the two-field `IntervalDomainMoserActualLinearSmallBoundednessCore`
  (`2 * γ < α` and `γ * N < 2`), and the conversion rebuilds
  `IntervalDomainBoundednessHyp` from that core, the wrapper hypothesis
  `0 < b`, and `CM2Params.hγ`.  Thus `0 < b`, `0 < γ`, and the sharp
  threshold branch are no longer duplicate residual fields at this level; the
  two absorption/dimension inequalities remain genuine parameter assumptions.
  The latest CETerminal statement route also has a Paper2-proposition-input wrapper,
  `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2FrontierData`,
  with theorem
  `intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2FrontierData`;
  this leaves the mainline residuals unchanged and removes the duplicate
  Paper3-side Proposition 1.3/1.4 existence branches by consuming Paper2
  Theorems 1.3/1.2 instead.  The CETerminal statement route also has a
  stronger Paper2-main-target wrapper,
  `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData`,
  whose proposition side consumes `IntervalDomainPaper2MainTheoremTargets`;
  this is the preferred bridge once Paper2's interval-domain headline bundle
  is available.  The actual-linear-small route now also has a direct
  integrated-step variant,
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepFrontierData`,
  plus the Paper2-main-target wrapper
  `IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainData`.
  This route consumes a supplied `IntegratedMoserFirstCrossingStep` and the
  existing quantitative endpoint.  The same surface is now refined by the
  lower-average / upper-gap split route
  `IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals`,
  `IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts`,
  `IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData`,
  `IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperFrontierData`,
  and
  `IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainData`;
  this consumes `IntegratedMoserFirstCrossingLowerUpperFrontiers` and then
  collapses to the existing integrated-step route.  Its reusable core is now
  `IntervalDomainMassLpSmoothingIntegratedStepResiduals`, which fills
  `IntervalDomainMassLpSmoothingRouteResiduals` directly via
  `intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms` and
  `intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms`; the
  Paper3 local adapter only supplies `l2SeedRegularity` from closed-energy
  trace data.  It
  deliberately does not derive `MoserDissipationDropBeforeNonnegB` or
  `RelativeMoserInterpolationBefore` from `Corollary_2_1`; those would be
  backwards analytic dependencies.  The hard residual is now exposed more
  precisely as production of the high-excursion contradiction-window frontier
  sufficient to obtain the integrated first-crossing step.  That frontier now
  also has a reusable Type-level split surface:
  `IntegratedMoserFirstCrossingLowerUpperFrontiers` and
  `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals` carry the
  cross-exponent lower-average and upper-gap suppliers separately before
  converting to the existing window-frontier and integrated-step routes.

**New threshold-plan route (2026-06-30):**
`P3MoserThresholdPlanProducer.lean` provides a complete alternative pipeline:
`integratedMoserFirstCrossingStep_of_abstract_data` takes regularity + energy
nonnegativity + dissipation drop + relative interpolation + gradient nonneg +
p0≥0 and produces `IntegratedMoserFirstCrossingStep` via the threshold-plan
contradiction argument.  Handles Cq=0 (non-increasing energy) separately.
`intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data` specializes
to `intervalDomain` by supplying gradient nonneg from `sq_nonneg`.
`P3MoserHighExcursionProducer.lean` is now axiom-clean (fixed 2 linarith
failures from integral-notation greedy parsing).  The remaining frontier for
this route is producing `IntegratedMoserFirstCrossingRegularity` from
`IsPaper2ClassicalSolution` (energy continuity via dominated convergence on
the compact interval domain).

Next real work is residual-assumption discharge, not proof-hole removal.  Good
small targets are the remaining Paper1 construction floors
(`hprodAll`/`hstep`/`htail`/stationary/flat/SMP packages), Paper2 general-χ
local/uniform existence inputs, production of
the high-excursion contradiction-window frontier sufficient for
`IntegratedMoserFirstCrossingStep` from integrated dissipation/relative
interpolation/regularity, and Paper3 interval-domain sectorial mainline
existence/persistence packages.

Input-package audit:
- `structure` and `def ... : Prop` packages here are explicit residual
  interfaces, not axioms and not proof holes.  A theorem consuming one of these
  packages is conditional until a producer constructs that package.
- For the integrated Moser route, `IntegratedMoserPrecrossingIntervalData` and
  `IntegratedMoserWindowUpperBoundData` now have proved producers from the
  named regularity/interior-energy-nonnegativity/current-bound/dissipation/
  relative inputs.  The energy-nonnegativity input is no longer a closed-time
  requirement: it is only required at interior times and, for `intervalDomain`,
  is produced from pointwise nonnegativity, `IsPaper2ClassicalSolution`, or
  `IsPaper2GlobalClassicalSolution`.  `IntegratedMoserHighExcursionContradictionWindowFrontier`
  is still the real analytic frontier.  Its lower-average and upper-gap
  subfrontiers are now explicitly split, both at a single exponent and in the
  cross-exponent `IntegratedMoserFirstCrossingLowerUpperFrontiers` package.
  The base-exponent nonnegativity field is now pure arithmetic via
  `p0_nonneg_of_abstractLpBootstrapHypothesis`, and
  `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` is now the
  preferred package collapsing lower-average data plus the upper-data-aware
  strict-gap chooser to the split first-crossing package.  The older
  `IntegratedMoserFirstCrossingLowerAverageEpsilonData` still collapses through
  a compatibility conversion, but is intentionally stronger.  The current code
  still does not derive high-excursion thickness or the quantitative selected
  upper-witness gap closure.
- Some fields are already produced or reduced further by code.  Examples:
  Paper2 χ₀=0 has `intervalDomain_theorem_1_1_chiZero_unconditional`, now
  exposed in the interval-domain statement assembly; the Paper2
  `IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData`
  wrapper produces `Corollary_2_1` and `Proposition_2_5` from the actual
  Moser atom package, and the mass-gradient variant lowers only the
  relative-Moser atom; Paper3 actual-linear-small persistence is produced by
  `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` and now wired
  to statement-level Theorem 2.1 wrappers.
- Other packages are genuine remaining analytic frontiers.  Examples:
  Paper1 `Paper1MainResultsData` / `Paper1MainlineExistence`, Paper2 general-χ
  `PicardLimitRestartFrontier` and `BoundaryMinPersistenceBound`, and Paper3
  reduced sectorial mainline facts / stability packages still require
  construction from PDE analysis before their corresponding headline endpoints
  become no-assumption theorems.

## SUPERSEDED HISTORICAL SNAPSHOT (2026-06-28)

1001+ files, ~393K LOC. Papers 1, 3: 0 sorry. Paper 2 χ₀=0: 0 sorry (UNCONDITIONAL).
Paper 2 χ₀<0: **42 sorry** across 8 files (was 43; hresolver_series filled).

### Architecture decision: DIRECT CUTOFF PATH is critical
Direct cutoff (IntervalHeatResolverJointC2, 5 sorry) bypasses
ResolverLevel0SpectralC2Coeff (DuhamelSourceTimeC2Coeff is 16+ fields, no producer)
and HeatSemigroupHighRegularity (FlooredSourceTimeData hyps are on separate path).

### 2026-06-28 progress:
- **hresolver_series FILLED** (310bc27): cosine reconstruction via coupledChemical_lift_eq_series
- **heatSemigroup_pos_of_pos ADDED** (571ab1d): S(t)u₀ > 0 from u₀ > 0 via lower bound
- Codex grinding heatLevel0_srcTimeCoeff_contDiffAt_two (adding hfloor chain)

### 2026-06-27 night session progress:
- **hfloor hypothesis added** to heatSemigroup_flooredSourceTimeData (heat positivity at t > 0)
- **heatDu_eq_secondValue bridge** — LaplacianValue = SecondValue by ring (definitional bridge)
- **d0 FILLED** (extracted as heatSemigroup_d0, pending build verify):
  - d0(a): heat profile joint continuity → rpow → srcSlice ContinuousOn
  - d0(b): HasDerivWithinAt → HasDerivAt via Icc_mem_nhds + hasDerivAt_srcSlice under floor
  - d0(c): rpow^(γ-1) × heatDu joint continuity from profile + secondValue
- **srcTimeCoeff_iteratedDeriv2 FILLED** (build-verified):
  iteratedDeriv_succ + EventuallyEq.deriv_eq on Ioi 0 + cosS1_hasDerivAt.deriv
- ChatGPT Q1224-Q1231: bridge verification, srcTimeCoeff proof, API discovery

### Learned: where-syntax ⟨⟩ elaboration pitfall
The `where` syntax for structure fields prevents `refine ⟨...⟩` from determining
the expected type when `have`-bindings are present. Fix: extract the proof into a
separate private theorem and call it from the `where` block.

### 2026-06-27 session progress:
- **3E-bdd filled** (b661bcd): intervalDomainLift u₀ bounded from Continuous u₀ on compact
- **3E-nonneg filled** (388ca89): added hu₀_nonneg hypothesis, propagated to callers
- **cutoffResolverTerm_contDiff_two decomposed** (7bb2f45): 4-layer structure —
  srcTimeCoeff ContDiffAt → resolverTimeCoeff ContDiffAt → cutoff global C² → (t,x) C²
  Single remaining sorry: heatLevel0_srcTimeCoeff_contDiffAt_two
- Level0: 7 → 5 sorry (3E-bdd and 3E-nonneg eliminated)
- ChatGPT Q1116-Q1122: resolver C² strategy, eigenvalue summability route, hu₀_nonneg design
- IntervalHeatResolverJointC2.lean: build-verified on uisai2 (axioms: propext/sorryAx/choice/sound)

### Per-sorry status (Level0, 5 remaining):
| Sorry | Line | Route | Status |
|-------|------|-------|--------|
| 1A (secondDeriv uniform bound) | 755 | joint C² on closed slab + compactness | BLOCKED on resolver C² |
| 2A-sup (uniform sup bound) | 893 | smooth representative + compactness | BLOCKED on resolver C² |
| eigenvalue summability | 1086 | depth-2 NeumannTower for ν·(S(r)u₀)^γ | ChatGPT route ready (Q1119) |
| resolver nonneg | 1101 | need S(r)u₀ ≥ 0 → source nonneg → resolver nonneg | needs hu₀_nonneg (same as 3E) |
| 3C+3D+3F (chain rule) | 1253 | direct resolver C² + inner commute | BLOCKED on resolver C² |
| 3G (time-deriv continuity) | 1262 | Level0HeatMixedRepr scaffold | separate path |

### MILESTONE: srcTimeCoeff_contDiffAt FILLED (127dcce, build-verified)
The assembly theorem connecting HasDerivAt×2 + ContinuousAt → ContDiffAt ℝ 2.
Key API: contDiffOn_succ_of_fderivWithin + ContDiffOn.smulRight (with StrongDual) +
smulRight_one_eq_toSpanSingleton + toSpanSingleton_deriv bridge.
IntervalPhysicalSourceTimeC2Concrete: 4 → 3 sorry.
Sub-lemmas (srcTimeCoeff_hasDerivAt, cosS1_hasDerivAt, cosS2_continuousAt) all sorry-free.
Also fixed: pass ContinuousOn (not IntervalIntegrable) to cosineCoeffs_hasDerivAt_of_smooth_param.

### What this session did (8 commits):
1. **F1 upstream weakening** (c2dfd86, e766768): ContinuousOn → IntervalIntegrable
   in 6 structures + consumer + 6 downstream callers. Boundary obstruction resolved.
2. **Architectural fix** (9dd3a4b): eliminated by_cases hτ : 0 < τ (τ ≤ 0 branch
   was mathematically impossible — heat semigroup discontinuous at t=0).
   15 sorry → 5 sorry.
3. **New infrastructure** (cfcb6de, 365db15, be5bf6b, 4a6740e):
   - variation-of-constants identity for localRestartCoeff
   - direct resolver inner commute WITHOUT PhysicalResolverJointC2Data
   - ResolverHasSpectralAgreementC2Coeff assembly (4 sorry)
   - Level0 ChemDivMixedTimeDerivClosedRepr skeleton (for 3G)

### Remaining 5 Level0 sorry:
- **1A** (line ~755): uniform ptwise bound of secondDeriv via joint continuity + compactness
- **2A-sup** (line ~893): uniform sup bound for coupledChemDivSourceLift
- **3A**: IntervalIntegrable from interior smoothness + sup bound (provable, no obstruction)
- **3C+3D+3F** (combined): chain rule HasDerivAt — blocked on resolver joint C² + bridge
- **3G**: time-derivative joint continuity on slab — blocked on mixed repr witnesses

### Root cause resolution status:
1. ~~Resolver C² scope mismatch~~: RESOLVED via Option B — direct cutoff resolver C²
   (IntervalHeatResolverJointC2.lean, 5 sorry, build-verified on uisai2).
   Option A (floor-weakening) also landed (4000f01) as backup.
   Option B infrastructure: variation-of-constants (0 sorry), direct inner commute (0 sorry),
   ResolverLevel0SpectralC2Coeff (assembly skeleton), Level0HeatMixedRepr (3G scaffold).
2. ~~F1 boundary obstruction~~: RESOLVED (ContinuousOn → IntervalIntegrable, 12+ files).
3. ~~τ ≤ 0 impossible branch~~: ELIMINATED (9dd3a4b, 15→5 sorry).

### Current state (end of 2026-06-26 night session):
Level0: **8 sorry** (from 15). Full project build-verified on uisai2 (3640 jobs).
34 commits, 25+ ChatGPT rounds, 10 subagents.

### Per-sorry closure map (Q1090 + Q1102):
- **3C+3D+3F** (chain rule HasDerivAt): CLOSES from direct resolver C² + inner commute
- **3E/positivity**: CLOSES with existing coupledChemical_floor_pos wiring
- **3A** (IntervalIntegrable): FILLED (9566859), 2 sub-sorry remain
- **3G** (time-deriv continuity): via Level0HeatMixedRepr scaffold (Q1102 confirmed no IteratePicardJointC2Data needed)
- **1A** (secondDeriv uniform bound): NEEDS WORK — joint continuity of cosine representative on closed slab
- **2A-sup** (source sup bound): NEEDS WORK — closed-slab source representative

### Next session priorities:
1. Fill 5 analytic sorry in IntervalHeatResolverJointC2.lean (per-term ContDiff + majorant)
2. Wire 3C+3D+3F from direct resolver C² (Q1066 has exact proof body)
3. Wire 3G from Level0HeatMixedRepr (fill 12 sorry for 10 smooth representatives)
4. Close 1A + 2A-sup from joint continuity + compactness

### Remaining 3 Level0 sorry (all blocked on resolver joint C²):
- 1A (line 755): joint pointwise bound of secondDeriv via compactness
- 2A-sup (line 804): uniform sup bound for coupledChemDivSourceLift
- 3A-sub (line 989): per-slab source continuity (upstream ContinuousOn weakening needed)

ALL THREE share the same blocker: resolver joint C² is proved INSIDE
FluxJointC2Hyp (sub-sorry 3C was filled via coupledChemical_jointContDiffAt_two +
PhysicalResolverJointC2Data), but NOT available as a standalone theorem for the
envelope construction.

### ROOT CAUSE: ∀ τ : ℝ scope mismatch (STRUCTURAL)
IterateSourceTimeData.floor requires positivity ∀ t : ℝ, but S(0)=0 (Lean
convention). The PhysicalResolverJointC2Data chain through FlooredSourceTimeData
is UNFILLABLE for the raw heat semigroup.

### NEXT SESSION OPTIONS (pick one):
(A) Weaken IterateSourceTimeData.floor to ∀ t, 0 < t → positivity
    (cross-cutting change across ~11 files, each ~1 line)
(B) Bypass the chain entirely: prove heatResolverJointContDiffAt_two
    DIRECTLY using cutoff approach (same as heatSemigroup_jointContDiffAt_two)
    — needs ContDiff of cutoff resolver term, which needs srcTimeCoeff C²
    for t > 0 (via cosineCoeffs_hasDerivAt_of_smooth_param)
(C) Build a positive-window-only IterateSourceTimeDataOn structure

Option (B) is the most self-contained. The existing cutoff heat semigroup
proof is the template — adapt it for the resolver series.

### 0-sorry infrastructure landed this session:
- IntervalSourceDecayQuantitative: quartic decay + eigenvalue L¹ summability
- IntervalResolverHighRegularity: global resolver positivity (period/even/reflect)
- Level0: slab inclusion (ContinuousWithinAt.mono_of_mem_nhdsWithin)
- Level0: resolver positivity (nonneg source → global nonneg → 1+V > 0)
- Level0: source eigenvalue summability (7-step chain: H2 certs + quartic decay)
- HeatRegularity: cutoff heat series global C² (contDiff_tsum via smoothRightCutoff)
- HeatRegularity: Leibniz main theorem (norm_iteratedFDeriv_mul_le applied + wired)

### Single key blocker: cutoffHeatTerm_iteratedFDeriv_bound (1 sorry)
In IntervalHeatSemigroupHighRegularity.lean. The cutoff approach is LANDED:
smoothRightCutoff kills t < 0, contDiff_tsum gives global C² of cutoff series,
eventual equality gives ContDiffAt at positive times. Only the Leibniz product
rule bound for ‖iteratedFDeriv k (φ·exp·â·cos)‖ remains.
Pattern: cutoffValueTerm_leibniz_bound (IntervalResolverSpectralJointC2CutoffBounds.lean:52)
uses norm_iteratedFDeriv_mul_le (Mathlib Leibniz rule).
Once proved → heatSemigroup_jointContDiffAt_two fully sorry-free →
unlocks sub-sorry 3B → 3C/3D → 2A-core → 1A.

### Sub-sorry with existing producers (found by cron analysis):
- 3F: coupledChemDivFlux_timeBridge_of_physicalJointC2 EXISTS (IntervalChemDivFACCommuteDischarge)
- 3G: chemDivMixedTimeDeriv_jointContinuousOn_closed EXISTS (IntervalChemDivTimeDerivClosed)
  Both need upstream PhysicalResolverJointC2Data → needs PhysicalSourceTimeC2 → needs heat wiring.

### Sub-sorry independent of joint C²:
- 2A-agree: definitional unfolding (coupledChemDivSourceLift_eq_deriv_fluxLift_interior exists)
- 3E: resolver positivity floor (τ > 0: nonneg source → nonneg resolver; τ ≤ 0: degenerate/sorry)

### Paper 2 χ₀<0 sorry breakdown

**IntervalConjugateLevel0BFormSourceOn.lean (4 sorry):**
1. Line 278: Source eigenvalue summability — `Summable (λ_k |sourceCoeff_k|)`.
   Route: depth-2 IBP via `intervalWeakH4Neumann_eigenvalue_L1_summable` (sorry'd
   in IntervalSourceDecayQuantitative.lean, reduces to cosineCoeffs-Laplacian identity).
2. Line 468: L1 uniform bound — joint continuity of deriv²(chemDiv) on [c,T]×[0,1] + compactness.
3. Line 514: Sup bound + per-slice continuity — same joint continuity difficulty.
4. Line 615: CoupledChemDivFluxJointC2Hyp — 5 fields of regularity for heat semigroup trajectory.

**IntervalConjugateBFormSourceTower.lean (5 sorry):** All downstream of Level0.

### Infrastructure built this session (sorry-free, axiom-clean)
- `IntervalResolverHighRegularity.lean`: global resolver nonneg from [0,1] via
  period-2 + even + reflect-one (intervalResolverLiftR_nonneg_of_nonneg_on_Icc),
  plus `0 < 1 + V(x)` wrapper.
- `IntervalConjugateLevel0BFormSourceOn.lean`: slab inclusion fix via
  ContinuousWithinAt.mono_of_mem_nhdsWithin; resolver positivity via nonneg source
  → nonneg resolver on [0,1] → global nonneg by symmetry.
- `IntervalSourceDecayQuantitative.lean`: depth-2 quartic decay + eigenvalue L¹
  summability — FULLY PROVED (0 sorry, axiom-clean, build verified on uisai2).
  `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound`: |c_k| ≤ 2B/(kπ)⁴
  `intervalWeakH4Neumann_eigenvalue_L1_summable`: Summable (λ_k |c_k|)
  Both proved via depth-2 IBP identity cosineCoeffs(f'') = -(kπ)² cosineCoeffs(f).

### FluxJointC2Hyp route (from ChatGPT analysis Q684/Q688)
The shortest path to CoupledChemDivFluxJointC2Hyp for the heat semigroup is:
  Physical source-time-C² data + summability
  → IntervalPhysicalResolverDataConcrete → CoupledChemDivFluxFactorJointC2Inputs
  → coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs → FluxJointC2Hyp
Hardest field: (b) joint C² of uncurried flux (resolver joint C² burden).
Second: (e) time-derivative ContinuousOn (spectral representative on closed slab).

### NeumannTower for source eigenvalue summability (line 278)
Existing tool: IntervalIBPCoeffExtraction.lean has NeumannTower + cosineCoeffs_decay.
Need: build NeumannTower at depth j=2 for ν·u^γ where u = heat semigroup.
Requires: C⁴ of ν·u^γ (chain rule) + depth-2 Neumann BCs (u' and u''' vanish at endpoints).

### Paper 1 (traveling waves): SORRY-FREE, unconditional infrastructure landed.
### Paper 2 χ₀=0: `intervalDomain_theorem_1_1_chiZero_unconditional` — UNCONDITIONAL, axiom-clean.
### Paper 3 (long-time dynamics): SORRY-FREE, linear dichotomy unconditional.

### χ₀ < 0 PRODUCTION FRONTIER
`BFormBankedInputs` fields — all satisfiable, all but 2 have sorry-free producers:
- `huPaper`, `Hinf`, `hsmall`, `MInit`, `haInit`: from existence data + ball estimates
- `hB_global`: from `conjugatePicardLimit_cosineSeries` (sorry-free)
- `hlogCont`, `hlogFourier`: Fields 9/10 from `IntervalBankSourceSliceLeaves` (sorry-free)
- `hchemIoo`: from `IntervalBankChemSliceFix` (sorry-free, replaces false `hchemCont`)
- **`hlogSrc`**: NEEDS PRODUCTION — `DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs ...)`
- **`hchemSrc`**: NEEDS PRODUCTION — `DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs ...)`

Production route for `hlogSrc`/`hchemSrc`:
1. `sourceTimeC1On_succ_of_sourceTimeC1On` (IntervalPicardSourceTimeC1OnRecursion) — GENERIC
2. `duhamelSourceTimeC1On_of_uniform_limit` (IntervalMildPicardLimitRegularityOn) — limit passage
3. Need: K1/K2 properties (representation, G1/G2 bounds, positivity) for `conjugatePicardIter`

---

## HISTORICAL (2026-06-10/11 — kept for reference, superseded by above)

## ⛔ FIDELITY CORRECTION (2026-06-11 ~04:00 — READ FIRST, supersedes all "done"/"unconditional"/"sorry-free" language below)
An independent adversarial audit (HANDOFF/FIDELITY-AUDIT.md) found this campaign
OVERSTATED its results. The honest status:
- What is in Lean is a **FRAGMENT** of the paper's Theorem 1.1: only χ₀=0 (the
  degenerate decoupled slice — NOT a chemotaxis system), N=1 (intervalDomain),
  a,b>0, 1≤α, 1≤γ. Untouched: χ₀<0 (the real case), a=b=0, N≥2, Thms 1.2/1.3.
- It is **CONDITIONAL** on `hsrc0` (TowerConeAnalyticResidual), which is the
  paper's hard analytic content relocated into a hypothesis AND plausibly
  unsatisfiable as typed (the s=0 ℓ¹-envelope t→0 disease). So there is NO
  unconditional result yet, even for the χ₀=0 fragment.
- The "#print axioms = clean" claims below were run on a DIVERGENT remote olean
  tree (/dev/shm/shen_work @ 6d2f95a, dirty), never on a clean f93cbda checkout.
  Clean-tree certification is in progress.
- Genuine positive: the STATEMENT layer is FAITHFUL (non-hollow) — the PDE, both
  equations, Neumann BC, real C² regularity, exact (1.21) bound.
The strong-language sections below describe real engineering progress on the
fragment, but their "done"/"prize"/"unconditional" framing is corrected here.

## ⭐⭐⭐ K1 ENDGAME STATE (2026-06-11 00:4x — engineering log, see FIDELITY CORRECTION above)
The hsrc0 endgame (waves W1a/W1b/W2/W3/W4, commits 085a3ad…7b424e2) built the
COMPLETE satisfiable replacement stack for the per-level source K1 package:
iterate initial approach (hand-written, χ₀=0), patched-coefficient continuity
+ per-level DuhamelSourceBddOn (no t→0 disease), the σ/2-shifted clamped
DuhamelSourceTimeC1 from winAdot data, consumer variants (hbsum/G2/hagree
_of_window/_of_sourceBdd), and assembled tower replacement legs — all
axiom-clean, all σ < T.

W4 verdict (rigorous): **σ = T is genuinely consumed** by three FROZEN
limit-side capstone feeders (IterateWindowC2Data closed-T quantifiers,
henv_iter at s ≤ D.T, hiter_cont at [D.T/2, D.T]), and every hsrc0-free route
is structurally σ < T strict (clamp pad headroom; WindowAdotLegs hi < T).
**TowerConeAnalyticResidual = { hsrc0 } is the honest irreducible minimum**
under the current frozen capstone surface.  Emptying it needs ONE of:
(i) a T-endpoint one-sided DuhamelSourceTimeC1 construction (the soft clamp
structurally cannot reach the endpoint), or (ii) a BddOn→λ-weighted upgrade
lemma, or (iii) unfreezing the capstone feeders to σ < T quantifiers.
Recorded in HANDOFF/k1-wall-plan.md W4 STATUS.

Also this campaign: the hL_cont VACUITY BUG (false zero-extension global
continuity field — residual was unsatisfiable as published) found and fixed
(c09aaca); hG2base + hG1all fake walls demolished by hand (7083684, 8f7987f).

## ⭐⭐ RESIDUAL SHRINK UPDATE (2026-06-10 19:30 — newest)
After the sorry-free capstone (32c8fee), two more residual legs fell — both
previously reported as BLOCKED by agents, both blockers shown ILLUSORY,
both proofs hand-written:
* **hG2base** (7083684, IntervalHomogeneousG2Base.lean): the gate at t := σ
  already forces homWeightBound = 32M/(eπ²σ²) ≤ A₂/σ², and the homogeneous
  slice's true spectral bound M·eigExpWeight σ ≤ 4M/(eπ²σ²) is 8× smaller —
  the gate's A₂ ≥ 64M/(eπ²) head-room was designed for this. No calibration
  hypothesis needed.
* **hG1all** (8f7987f, IntervalPicardG1All.lean): the split machinery's
  ∀ s : ℝ source sup is over-quantified — the Duhamel integrand reads
  s ∈ Ioc 0 t only. The windowed family wSrc satisfies the global sup by
  construction and the same value EqOn by integral congruence; the existing
  interior split + g1_kernel_bound apply verbatim. Bonus infrastructure:
  picardIter_hasJointMeasurability_all, u₀_lift_abs_le. HCone gained the
  cone-returned hlim_ball conjunct (precedent: hub's hball).
**TowerConeAnalyticResidual is now 7 fields: hsrc0, hL_cont, adot,
hadot_deriv, hadot_cont, adotBound, hadot_bound — ALL rooted in per-iterate
source K1 regularity (the project's one genuine remaining analytic wall;
see UNPROVED_TARGETS.md for the documented producer circularity).**
Axioms unchanged: both capstone theorems = [propext, Classical.choice,
Quot.sound].

## ⭐ FINAL STATE (2026-06-10 18:15 — supersedes everything below)
**THE CAPSTONE IS SORRY-FREE.** Commit 32c8fee:
`#print axioms` on BOTH `paper2_theorem_1_1_chiZero_unconditional` and
`paper2_theorem_1_1_chiZero_from_coneSupply` = `[propext, Classical.choice,
Quot.sound]` — NO sorryAx (independently re-verified on uisai2; full build
8547 jobs EXIT 0; md5 local=remote). The `hinterior` circularity (hcontP →
hsliceTC → restart-rep → BddOn → hcontP) was broken on the iterate side:
s-uniform geometric convergence (PicardConvFacts.hgeom) transfers per-iterate
coefficient time-continuity to the limit (IntervalPicardLimitCoeffTimeCont);
hinterior itself proved via the spectral restart series subtraction with the
λ-cancelling Duhamel bound + heat-damped homogeneous sum
(IntervalRestartSeriesLipschitz / IntervalRestartSliceLipschitz). The capstone
gained ONE hypothesis (`IterCoeffTimeContProvider`), discharged inside
`from_coneSupply` from the tower (`hiter_cont_of_tower`) — the acceptance
surface `from_coneSupply` is UNCHANGED. Tower residual
(`TowerConeAnalyticResidual`, the from_coneSupply hypothesis surface) is now
9 fields: hsrc0, hL_cont, hG1all, hG2base, adot(+4 legs). Honest blockers
recorded: hG1all needs a global all-s iterate source sup (truncated-source
rebuild = new analytic content); hG2base needs a homogeneous heat ∂²ₓ estimate
calibrated to the gate budget A₂. Design verdicts in
HANDOFF/chatgpt-hinterior-break-verdict.md.

## START HERE
Read `HANDOFF/CODEX-HANDOFF.md` — the complete execution handoff for the
Tower campaign (environment rules, current state, stage 1/2 plans, verdict
index). Build is REMOTE ONLY (uisai2:/dev/shm/shen_work; local builds are
blocked and would kernel-panic the mini). Acceptance = #print axioms.

## THE CURRENT STATE (one paragraph)
Paper 2 Theorem 1.1 (χ₀ = 0) capstone
`paper2_theorem_1_1_chiZero_unconditional`:
regime constants (χ₀=0, a>0, b>0, α≥1, γ≥1) + HWdata ⟹ Theorem_1_1,
axioms [propext, sorryAx, Classical.choice, Quot.sound]; the single sorryAx
is `hinterior` (IntervalPicardLimitSliceTimeContinuity). HWdata (per-datum
window iterate-C² provider) and hinterior share ONE root: the per-iterate
source-package production tower. The tower is fully designed and externally
audited (HANDOFF/chatgpt-tower-verdict.md); stage 1 (lemma layer, 4 files)
may already be landed by an in-flight agent — CHECK git log/status first.
Tower lands ⟹ both close ⟹ capstone carries regime constants only.

## What the 2026-06-09/10 campaign did (~40h, ~70 commits, all pushed)
Started at 21 sorries, 14 UNSATISFIABLE AS TYPED (global time quantifiers
vs (0,T]-only data; uniform gradient bounds false at t→0 by parabolic
smoothing; no ℓ¹ envelope at s=0 for continuous data; the s=T jump; two
genuine circularities). Dissolved via: C¹ soft clamp + existential clamped
witnesses; weak-chain horizon retype (DuhamelSourceL1ContOn) then the final
DuhamelSourceBddOn patched-family interface; ledger V2 (per-compact K2,
(0,T) K1, shifted fields deleted); K1 proved WITHOUT new analysis (weak
restart identity + per-mode FTC + fixed-split series differentiation);
iterate-side bootstrap breaking the hsrc0 circularity; hybrid weighted C²
(kernel G1 + t²-weighted spectral G2, gate SOLVED explicitly in
IntervalPicardGateSolve); cone _with_gate_data (returns exact hDu,
discharged GateCondition, hcont_iterates, PicardConvFacts, strict iterate
positivity); Hvsrc per-t₀ retype + clamped ν·u^γ witness; hpde_u via the
continuous-surrogate retype; Hvpos proved; capstone narrowed to
HWdata-only via fact-carrying bridges (the hPLF ∀-D route superseded).
Six external design audits (HANDOFF/chatgpt-*-verdict.md); three caught
real errors (the G1 spectral recursion non-closure, a circular k1_quadruple,
the hDu EqOn trap).

## Historical notes below (pre-campaign architecture, mostly still accurate
## for layers 1-2; the Paper2 layer-3 description is superseded by the above)

## Build invariant

```bash
lake build  # 8409 jobs, 0 sorry, 0 admit, 0 custom axiom
```

## Architecture: three layers

### Layer 1: PDE infrastructure (COMPLETE, 0 sorry)
All spectral, semigroup, kernel, Duhamel, resolver, energy, IBP, and
measurability infrastructure is proved. Key files:
- IntervalNeumannFullKernel, IntervalFullKernel*, IntervalDuhamel*
- IntervalResolverPositivity (O1: heat-Laplace nonneg, unconditional)
- IntervalChemFluxLipschitz (glue1+glue2: contraction estimates)
- IntervalGradDuhamelBound (Atom D: gradient sqrt-T estimates)
- IntervalLogisticLipschitz (Atom C: logistic Lipschitz, one-sided α>0)
- IntervalSourceCoefficientTimeC1 (G3: DuhamelSourceTimeC1 algebra)
- IntervalResolverSpatialC2 (G4q: resolver C² + Neumann + weight summability)

### Layer 2: Mild solution + regularity bootstrap (COMPLETE, 0 sorry)
- IntervalMildPicard: Picard iteration → GradientMildSolutionData (mild FP)
- IntervalMildSourceDecay: SourceCoeffQuadraticDecay (unconditional)
- IntervalMildToClassical: all 9 regularity conjuncts (unconditional)
- IntervalMildRegularityBootstrap: half-step restart C² + Neumann
- IntervalSemigroupNeumann: semigroup conjuncts 3/6/7/8/9 + composition
- IntervalMildPicardRegularity: Picard iterate induction (base + step)
- IntervalMildPicardLimitRegularity (G2.5): DuhamelSourceTimeC1 limit passage
- IntervalMildTimeRegularity (G4j): time DifferentiableAt from spectral
- IntervalMildTimeDerivContinuity (G4 fields): HasDerivAt + joint continuity
- IntervalMildFrontierFromSpectral (G4r): closed-slab joint continuity
- IntervalMildRegularityFrontierAssembly: u-side frontier field wiring
- IntervalResolverTimeRegularity: v-side frontier field wiring
- IntervalResolverDirectTimeRegularity (F2): resolver direct time regularity
- IntervalMildSourceDecayHelper: Sobolev chain rule / weak H² Neumann
- IntervalWeakCosineIBP: cosine coefficient decay infrastructure
- IntervalMildToLocalExistence: bridge to localExistence

### Layer 3: Paper-level theorem assembly (NEAR COMPLETE)
- IntervalDomainTheorem11Umbrella: γ≥1 umbrella (hposWit eliminated, G6)
- IntervalDomainThm11Assembly: final wiring, 15/15 frontier fields proved
- IntervalDomainStatementAssembly: Paper2 Thm 1.1/1.2/1.3 targets
- Paper1/Statements, Paper2/Statements, Paper3/Statements

## G0–G7 + G2.5 status (all committed, 0 sorry)

| Gap | Description | Status | Commits |
|-----|-------------|--------|---------|
| G0 | Continuous u₀ in initialAdmissible | ✓ DONE | 5343c18 |
| G1a | One-sided logistic Lipschitz α>0 | ✓ DONE | 5f94ba0 |
| G2a+G2b | Spatial IBP for Duhamel source | ✓ DONE | 5bf3fb5 |
| G2.5 | DuhamelSourceTimeC1 limit passage | ✓ DONE | e5da4dc |
| G3 | Total-source DuhamelSourceTimeC1 | ✓ DONE | b2b4b66+ |
| G4a–G4i | Spectral time derivatives (ODE→series) | ✓ DONE | 355f14d–356dd4e |
| G4j | Time DifferentiableAt of mild solution | ✓ DONE | e138bfa |
| G4k–G4m | Joint continuity (Duhamel+hom+restart) | ✓ DONE | cfa96ab–665367d |
| G4n–G4p | Spectral PDE identity + Laplacian | ✓ DONE | a1ce482–c7db735 |
| G4q | Resolver spatial C² + weight summability | ✓ DONE | 7c0dd7b |
| G4r | Closed-slab joint continuity | ✓ DONE | 8e8b1ae |
| G5 | Uniform S(t)u₀→u₀ for continuous u₀ | ✓ DONE | 809f1ac |
| G6 | PID-gate L² chain + eliminate hposWit | ✓ DONE | 25da5b3+2d8cdcf |
| G7 | ReachableArbitrarilyLong from hlocal+hUniform | ✓ DONE | 625fa56 |
| F2 | Resolver direct time regularity | ✓ DONE | a32f923 |

## Remaining frontier for unconditional Paper 2 Theorem 1.1

### Proved chain (axiom-clean)
```
Picard FP → iterate C² induction → DuhamelSourceTimeC1 limit (G2.5)
→ regularity bootstrap → localExistence
→ γ≥1 umbrella (no hposWit, G6) → L² uniqueness (PID-gated)
→ δ-iteration (G7) → Theorem_1_1
```

### Assembly theorem
```lean
paper2_theorem_1_1_of_frontier:
  hUniform + hMildLocal → Theorem_1_1 intervalDomain p
```

### Regularity frontier data: 15/15 fields proved
- 12 unconditional (u-side time + spatial, v-side spatial, sup-norm)
- 3 from ResolverHasSpectralAgreement (v-side time, constructible from F2)

### Two genuine remaining hypotheses

**F1: IntervalDomainUniformLocalExistence** (textbook continuation δ(M))
- For every M>0, ∃ δ>0 such that any classical solution with |u₀|≤M extends by δ
- Standard PDE (Henry/Amann); requires restart-before-end + overlap glue
- Estimated ~200 lines

**F2 (partially resolved): DuhamelSourceTimeC1 for the Picard limit**
- G2.5 reduces to uniform convergence of iterate source coefficient derivatives
- F2 direct resolver regularity proved (IntervalResolverDirectTimeRegularity)
- Remaining: instantiate the uniform convergence hypothesis from Picard data
- Estimated ~150 lines

## Other paper theorems

### Gap 2: Paper1 Theorem 1.1 (traveling wave existence)
Requires Schauder fixed point on the whole line (not interval domain).
Mathematically hardest gap.

### Gap 3: Paper1 Thm 1.2/1.3 (stability/uniqueness)
Depends on Gap 2.

### Gap 4: Paper2/Paper3 semigroup estimates (Lemma 2.1-2.4)
Mechanical but large. Zero-data branches proved.

## Priority order
1. F1 + F2 instantiation → Paper2 Thm 1.1 unconditional (~350 lines)
2. Gap 4 (semigroup estimates): mechanical
3. Gap 2 (whole-line Schauder): mathematically hardest
4. Gap 3 (weighted stability): depends on Gap 2

## Build
On uisai1: `PATH=$HOME/.elan/bin:$PATH lake build`

## 2026-06-06 night update — hQuant driven to a single shared residual

The "Two genuine remaining hypotheses" section above is STALE. Current map:

### hQuant (uniform δ(M) local existence) — Session B campaign, all green/axiom-clean
- **χ₀ = 0 (cone route, COMPLETE modulo one hypothesis):**
  `ConeQuantBridge.quantitativeLocalExistence_chiZero` — Picard contraction
  AND positivity proved (exponential cone invariance, uniform δ(p,M),
  no inf-threshold). Residual: `PicardLimitRestartFrontier` only.
  End-to-end: `paper2_theorem_1_1_chiZero_of_frontier` (+ hlocal).
- **General χ₀ ≤ 0 (threshold route, conditional):**
  `QuantFromThreshold` + `ThresholdQuantBridge`: hQuant ⟸ proved-δ(M,c)
  threshold Picard + `ClassicalMinPersistence` (min principle, open) +
  `PicardLimitRestartFrontier` + hlocal.
- **Key new infrastructure** (axiom-clean): Chapman–Kolmogorov
  `IntervalSemigroupComposition` (S(s)S(t)=S(s+t) via S1 spectral identity),
  cone atoms (mono/Duhamel-eval/kernel strict positivity), generic
  `gradientMildSolutionData_initialApproach` (hInitialApproach is no longer
  part of any per-datum frontier for continuous data).

### Unified residual
`PicardLimitRestartFrontier p` (ConeQuantBridge): restart source data +
frontier core for every packaged D with `D.u = picardLimit p u₀ D.T`.
One S-construction discharge (Session A's M-line, in flight) closes
hQuant(χ₀=0), the threshold route's Picard half, and hlocal(χ₀=0).

## 2026-06-09 — Thm 1.1 chain compilation green

### Chain status (ContinuousExtension → … → Provider)
Full 7-file chain compiles end-to-end on uisai2 (lake build green):
```
IntervalDomainContinuousExtension (0 sorry)
→ IntervalPicardLimitRestartWeak (0 sorry, eigenvalue summability proved)
→ IntervalDomainConstExtendAdapter (1 sorry: adapter body)
→ IntervalDomainMildLocalChi0 (1 sorry: restartData_of_inputs)
→ IntervalDomainThm11ChiZeroFinal (0 sorry)
→ IntervalDomainLedgerSweep (2 sorry: time-quantified → global adapters)
→ IntervalDomainThm11ChiZeroCoreProvider (17 sorry: analytic estimates)
```

### Key fix: namespace opens for `intervalLogisticSource` / `cosineMode`
Six files needed `open ShenWork.IntervalDomainExistence (intervalLogisticSource)`
and `open ShenWork.CosineSpectrum (cosineMode)`. Without these, all definitions
using these names silently became autoImplicit variables, cascading "Function
expected" errors.

### RestartWeak eigenvalue summability (NEW, 0 sorry)
`summable_eigenvalue_mul_abs_limitCoeff_weak`: proved via FTC envelope
computation + triangle split + `Summable.of_nonneg_of_le`. The proof handles:
`abs_add` → `abs_add_le` rename, `gcongr` → explicit `add_le_add` /
`mul_le_mul_of_nonneg_left`, `continuous_const` domain inference in tactic mode,
`-(t-s)*λ_k` parse order, `neg_zero` in simp set.

### Provider sorry inventory (17 items)
- G1, G2 — gradient/Hessian bound VALUES
- hG1t, hG2t — gradient/Hessian bound PROOFS
- adott family (5) + adotS family (5) — K1 time-C¹ data
- hpde_u, Hvsrc, Hvpos — PDE/resolver residuals
- hsrc0 (×2 in final wiring) — DuhamelSourceL1Cont

### LedgerSweep interface gap — RESOLVED 2026-06-09 night (horizon localization)
See HANDOFF/horizon-localization-design.md + HANDOFF/horizon-retype-status.md.
Landed (all green, 8521 jobs): C¹ soft clamp (IntervalTimeSoftClamp) +
clamped-witness TimeC1 producer (IntervalDomainClampedSourceRepresentation) +
weak-chain horizon retype (DuhamelSourceL1ContOn) + Hu_of_restart_localized
(0 sorry) + ledger V2 (per-compact hG1t/hG2t/hMdott, (0,T) K1, 5 shifted-K1
fields deleted, hsrc0 field) + K2 gradient producers wired + Hvpos proved
(mildChemicalConcentration_pos) + hpde_u producer (IntervalDomainPdeUProducer).

Sorry inventory end of 2026-06-09 (8, all satisfiable types; see
HANDOFF/horizon-retype-status.md header for the live ledger):
- Provider: hsrc0F (BddOn patched-family migration pass; producer is DONE
  0-sorry in IntervalPicardLimitBddProducer), K1 quadruple ×4 (R2 weak spine
  — NOT uniform-convergence/F2 after all; ChatGPT-verified route: weak
  restart identity → c_k' = −λ_k c_k + A_k by FTC → term-wise diff; first
  attempt was circular, fix in flight), Hvsrc
- PdeUWiring: 1 K1 bundle (same data as the quadruple)
- restartData_of_inputs + hasRestartData_of_subtypeCont (restart packaging)
Discharged today beyond the 10-list: Hu_of_reduced (subtype variant),
hpde_u (surrogate retype killed the false lift-continuity field).

### Option A SETBACK (Q1076): floor-weakening alone insufficient
FlooredSourceTimeData's 6 sorry are NOT trivially fillable after weakening:
- d0-d1: need positivity floor (0 < u(t,x)) for rpow chain rule
- zerothBound/laplBound: need UNIFORM bounds ∀ t > 0, but source derivatives
  blow up as t → 0 for merely continuous initial data
NEXT: further weaken zerothBound/laplBound to per-compact-window (∀ t ∈ [c,T]),
or restructure the consumer chain to accept window-local data directly.
