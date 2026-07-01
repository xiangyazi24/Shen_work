# Q2820 (shen1) — headline/frontier audit after recent wrapper and direct-route commits

Repo: `xiangyazi24/Shen_work`  
Default branch/head audited via connector: `origin/main = e6d5f991` (`Fix Hölder interpolation type signature`)  
Delivery branch: `chatgpt-scratch`

I did not modify repository source. I did not inspect, rely on, or propose edits to the Zinan-owned producer files:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`

This is a source-level audit, not a fresh local Lean build run.

## 0. Proof-hole verification

I verified the two direct-route files named in the prompt contain live `sorry`s, not just comments.

### `ShenWork/PDE/IntervalDomain1DLinfRoute.lean`

Live sorries are exactly at the four theorem bodies visible in source:

- `intervalDomain_Lp_energy_and_dissipation_of_regularity`
- `intervalDomain_Linf_of_Lp_and_gradient`
- `intervalDomain_all_Lp_of_Linf`
- `intervalDomain_Proposition_2_5_1d`

These correspond to the prompt’s line regions 86/129/145/172.

### `ShenWork/PDE/P3MoserAgmonDirectRoute.lean`

Live sorries are exactly at the six theorem bodies visible in source:

- `intervalDomain_higher_Lp_le_Linf_rpow_mul_seed`
- `intervalDomain_supNorm_rpow_le_energy_plus_gradient`
- `intervalDomain_gn_absorbed_interpolation_of_agmon`
- `intervalDomain_all_Lp_of_agmon_bootstrap`
- `intervalDomain_Corollary_2_1_of_agmon`
- `intervalDomain_Proposition_2_5_of_agmon`

These correspond to the prompt’s line regions 60/83/118/136/147/167.

Do not advertise either direct-route file as proved. They are architecture/skeleton files with live proof holes.

## 1. Headline/frontier status by file family

### Paper1: `ShenWork/Paper1/StatementAssembly.lean`

Status: mostly conditional wiring.

Proved pure/wiring components include scalar/barrier conversions such as:

- `ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi`
- `strict_upperBarrier_MChi_of_contactContradictions`
- `paper1_positiveCriticalBranch_of_strictBarrier`
- `paper1_positiveStrictBarrierBranch_of_contactBranch`
- `paper1_positiveContactBranch_of_lowerPinnedContactData`
- `paper1_positiveContactBranch_of_lowerPinnedRawContactData`

Headline wrappers are conditional and should not be advertised as unconditional Paper1 theorem proofs:

- `paper1_mainStatementTargets_of_mainResultsData` consumes `Paper1MainResultsData`.
- `paper1_Theorem_1_1_of_mainResultsData` consumes `Paper1MainResultsData`.
- `paper1_Theorem_1_1_of_constructionNegSMPProvider` consumes `ConstructionNegSMPProvider` plus the positive branch.
- `paper1_mainlineStatementTargets_of_mainlineExistence` consumes `Paper1MainlineExistence`.

Open Paper1 frontiers remain the actual construction data: negative construction provider, positive critical branch/no-contact/tail/Schauder data, and mainline existence packages.

### Paper2 generic: `ShenWork/Paper2/StatementAssembly.lean`

Status: generic conditional statement assembly only.

Wrappers such as:

- `paper2_bootstrapEstimateTargets_of_branchData`
- `paper2_Proposition_1_1_of_existenceData`
- `paper2_mainTheoremTargets_of_solutionBranchData`
- `paper2_localAndMainTheoremTargets_of_data`

are aliases/packagers around frontier records (`Paper2BootstrapEstimateBranchData`, `Paper2Proposition11ExistenceData`, `Paper2MainSolutionBranchData`, etc.). They are useful wiring, but not proved headline theorems by themselves.

### Paper2 interval: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`

Status: mixed; several interval-specific pieces are proved, but headline Theorems 1.2/1.3 remain conditional on significant frontiers.

Proved/unconditional interval pieces visible now:

- `intervalDomainPaper2_Lemma_3_1` proves `Lemma_3_1 intervalDomain p`.
- `intervalDomainPaper2_Lemma_4_1_of_provedAgmon` proves `Lemma_4_1 intervalDomain p` from the already-proved positive Agmon interpolation route.
- `intervalDomainPaper2_aprioriTargets_of_provedAgmon` proves `Lemma_3_1 ∧ Lemma_4_1` for `intervalDomain`.
- `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional` proves Theorem 1.1 only in the `χ₀ = 0` regime under its parameter hypotheses.
- `intervalDomainPaper2_Theorems_1_2_and_1_3_of_provedPositiveSolutionInterpolationFrontierData` discharges the interpolation field using proved Agmon, but still consumes the rest of the Theorem 1.2/1.3 frontier data.

Important conditional/alias surfaces:

- `intervalDomainPaper2_Theorems_1_2_and_1_3_of_provedPositiveSolutionInterpolationFrontierData` is **not** a proved Theorem 1.2/1.3 headline theorem. It removes only the interpolation assumption from the positive-solution route.
- `IntervalDomainPaper2ProvedPositiveSolutionInterpolationEnergyFrontierData` still carries dissipation, gradient-chain, mass-control, power-integrability, and cross-diffusion energy frontiers.
- `IntervalDomainPaper2Theorem12And13ProvedPositiveSolutionInterpolationFrontierData` still carries `prop25`, local/global existence, bootstrap outputs, and eventual sup-bound fields.
- `intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData` and `intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData` are conditional on `IntegratedMoserFirstCrossingStep` plus endpoint data. They do not prove the step.
- The GN-frontier route `intervalDomainPaper2_Lemma_4_1_of_GN_frontier` is explicitly deprecated because the old global `IntervalDomainInterpolation` premise is refuted. Do not use it for headline accounting.

Open Paper2 frontiers after proved Agmon:

- Proposition 2.5 / Corollary 2.1 still need actual atoms, integrated-step data, lower/upper frontiers, or a direct 1D L∞ route.
- Theorem 1.2/1.3 routes still need local/global extension, slow/critical/strong bootstrap outputs, eventual sup-bound fields, and Proposition 2.5.
- `χ₀ = 0` local-free routes are real but regime-specific.

### PDE Agmon core: `ShenWork/PDE/IntervalAgmonInterpolation.lean`

Status: proved core.

Key proved declarations:

- `unitIntervalPositiveAgmonInterpolation : UnitIntervalPositiveAgmonInterpolation`
- `intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon`
- `intervalDomain_classicalSolutionPositiveInterpolation`
- helper bridge facts around `intervalDomainLift_rpow_agmon_bound`, `intervalDomainLift_rpow_agmon_bound_qsqrt`, and integral/derivative rewrites.

This is genuine proved data and should be advertised as such. It proves the positive solution-slice interpolation field, not Moser/Prop 2.5 by itself.

### PDE integrated closure: `ShenWork/PDE/P3MoserIntegratedClosure.lean`

Status: proved closure/wiring, not a producer.

Proved closure utilities include:

- `integratedMoserFirstCrossingStep_of_windowFrontier`
- `integratedMoserFirstCrossingStep_of_lowerUpperFrontiers`
- `integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData`
- `moser_iteration_chain_of_integrated_first_crossing_step`
- `intervalDomain_integratedMoserGradientEnergy_nonneg`
- `intervalDomain_integratedMoserGradientEnergyNonnegativity`
- `integratedMoserGradientEnergy_intervalIntegral_nonneg_of_package`

These are genuine proved wrappers/utilities, but they consume regularity/dissipation/relative interpolation/lower-average/upper-data-gap/frontier data. They are not high-excursion or threshold producers.

### Paper3 generic: `ShenWork/Paper3/StatementAssembly.lean`

Status: conditional statement assembly.

Important wrappers:

- `paper3_proposition1Targets_of_frontierData`
- `paper3_proposition1Targets_of_paper2TheoremsData`
- `paper3_proposition1Targets_of_paper2MainTargetsData`

These are correct wiring. They are not unconditional Paper3 propositions because `negativeBound` remains an explicit field in the generic data.

### Paper3 interval + actual-linear: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

Status: strong wiring reductions are proved, but headline routes remain conditional on Moser/mainline/Paper2 inputs.

Proved/wiring reductions:

- actual-linear persistence is produced internally by `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` in relevant routes;
- `intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos` discharges Paper3 Proposition 1.2’s negative-sensitivity residual from `0 < p.χ₀`;
- NoNeg wrappers such as `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData` and `IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainNoNegData` remove the `negativeBound` field from the Paper3 actual-linear headline surfaces;
- integrated-step and lower-average/upper-data-gap wrappers reduce the exposed Moser surface, but remain conditional.

Still open in actual-linear Paper3 headline routes:

- `paper2Main : IntervalDomainPaper2MainTheoremTargets p C` or theorem12/theorem13 equivalents;
- `mainline` packages such as `IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData` or thin variants;
- core fields inside mainline: sectorial semigroup orbit bound, continuation/gluing, mass/Lp/smoothing residuals, compactness/regularization, and Stability24/full stability branches;
- the integrated first-crossing step if using the integrated-step route.

### Compatibility warning: `χ₀ = 0` versus actual-linear `0 < χ₀`

The Paper2 `χ₀ = 0`/local-free routes cannot feed the Paper3 actual-linear NoNeg route that requires `hχ0 : 0 < p.χ₀`. The hypotheses are inconsistent. I did not find a compatibility wrapper that makes a `χ₀ = 0` theorem usable in the actual-linear `0 < χ₀` route.

The proved-positive Agmon interpolation route is parameter-neutral and can be used for positive `χ₀`, but only after the rest of the non-`χ₀=0` Paper2/Paper3 frontiers are supplied. Do not conflate the `χ₀ = 0` local-free wrappers with the actual-linear `0 < χ₀` wrappers.

## 2. Direct Moser / GN-absorbed route sorries ranked

### A. `IntervalDomain1DLinfRoute.lean`

1. **Easiest independent close:** `intervalDomain_all_Lp_of_Linf`.
   - Prove `LpPowerBoundedBefore` from a pointwise upper bound and positivity of classical slices.
   - Likely needs only integral monotonicity on `[0,1]` and `Real.rpow_le_rpow`.
   - This is a good Codex target because it does not depend on the hard energy/Gronwall step.

2. **Medium, important bridge:** `intervalDomain_Linf_of_Lp_and_gradient`.
   - Depends on Agmon and the missing bridge between the gradient of `u^(p/2)` and the weighted gradient integral used in Agmon.
   - The current source calls a name `intervalDomain_moser_gradient_integral_eq_weighted_of_regularity`; this is the right missing lemma shape.

3. **Hard analytic core:** `intervalDomain_Lp_energy_and_dissipation_of_regularity`.
   - Requires logistic absorption, Gronwall, and a pointwise-in-time dissipation bound. This is the deepest real PDE/energy step in the 1D L∞ route.

4. **Assembly only after above:** `intervalDomain_Proposition_2_5_1d`.
   - Should be postponed until the three previous steps are closed and its hypotheses are checked for consistency.

### B. `P3MoserAgmonDirectRoute.lean`

1. **Low-level but signature-sensitive:** `intervalDomain_higher_Lp_le_Linf_rpow_mul_seed`.
   - Mathematically easy under boundedness/integrability/continuity hypotheses.
   - As currently stated, it has only pointwise nonnegativity and no `BddAbove`/integrability hypotheses, so it may be too weak or awkward. Prefer proving a stronger-hypothesis variant or reusing `integral_pow_le_sup_pow_mul` rather than fighting the current statement.

2. **Medium bridge:** `intervalDomain_supNorm_rpow_le_energy_plus_gradient`.
   - Similar to `intervalDomain_Linf_of_Lp_and_gradient`; needs compact/supNorm handling and the gradient-chain equality.

3. **Hard analytic/scalar step:** `intervalDomain_gn_absorbed_interpolation_of_agmon`.
   - This is the core GN-absorbed route: Hölder with seed norm plus Young absorption. It depends on the first two steps and careful exponent inequalities.

4. **Likely under-specified assembly:** `intervalDomain_all_Lp_of_agmon_bootstrap`.
   - It takes `hcross` and `hboot` but no explicit `LpBootstrapEnergyInequality` input. Verify whether imported chain code derives it from those; otherwise this statement is missing a hypothesis.

5. **Do not advertise / likely wrong as unconditional:** `intervalDomain_Corollary_2_1_of_agmon` and `intervalDomain_Proposition_2_5_of_agmon`.
   - `intervalDomain_Corollary_2_1_of_agmon (params)` has no frontier hypotheses, so it is almost certainly too strong as a theorem statement unless all needed bootstrapping is imported/proved elsewhere. Treat as aspirational until the earlier sorries are closed and its API is revisited.

## 3. Aliases/wrappers not to advertise as proved headline theorems

Do not advertise these as proved headline theorem closures:

- `paper1_mainStatementTargets_of_mainResultsData`, `paper1_Theorem_1_1_of_mainResultsData`, and `paper1_mainlineStatementTargets_of_mainlineExistence`: they consume Paper1 frontier packages.
- `paper2_mainTheoremTargets_of_solutionBranchData` and interval wrappers that say `of_frontierData`/`of_solutionBranchData`: they are statement assembly, not producers.
- `intervalDomainPaper2_Theorems_1_2_and_1_3_of_provedPositiveSolutionInterpolationFrontierData`: it discharges only the interpolation field; many Theorem 1.2/1.3 frontiers remain.
- `intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData`: it consumes an integrated first-crossing step; it does not produce it.
- `intervalDomainPaper2_Lemma_4_1_of_GN_frontier`: deprecated due the false global interpolation premise.
- `intervalDomain_paper3_*FrontierData` / `*P2MainData` / `*NoNegData` wrappers: these are valuable reductions but still consume Paper2/mainline/Moser/compactness/stability fields.
- all theorems in `IntervalDomain1DLinfRoute.lean` and `P3MoserAgmonDirectRoute.lean` with live `sorry` bodies.

## 4. Next concrete Lean attack routes

### Route 1: close the gradient-chain bridge used by both direct routes

Best target name/shape:

```lean
theorem intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm
        (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) =
      (pExp ^ 2 / 4) * intervalDomain.integral (fun x =>
        (u t x) ^ (pExp - 2) *
          (intervalDomain.gradNorm (u t) x) ^ 2)
```

Better generic version, if easier to reuse:

```lean
theorem intervalDomain_moser_gradient_integral_eq_weighted
    {pExp : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm
        (fun y => f y ^ (pExp / 2)) x) ^ 2) =
      (pExp ^ 2 / 4) * intervalDomain.integral (fun x =>
        f x ^ (pExp - 2) * (intervalDomain.gradNorm f x) ^ 2)
```

Use existing Agmon file infrastructure:

- `intervalDomainLift_rpow_deriv_sq_integral_eq`
- `intervalDomainLift_rpow_hasDerivWithinAt_Ioi`
- `deriv_eq_derivWithin_interior`
- endpoint-null `congr_ae` pattern already used in `IntervalAgmonInterpolation.lean`.

This bridge unlocks `intervalDomain_Linf_of_Lp_and_gradient` and `intervalDomain_supNorm_rpow_le_energy_plus_gradient`.

### Route 2: close `intervalDomain_all_Lp_of_Linf`

Target:

```lean
theorem intervalDomain_all_Lp_of_Linf
```

from `IntervalDomain1DLinfRoute.lean`.

Expected proof plan:

- For fixed `r > 1`, set a bound like `M := max 1 (M_inf ^ r)` or `M := M_inf ^ r` if nonnegativity is enough.
- Use positivity from `hsol.u_pos'` and pointwise `u t x ≤ M_inf`.
- Prove pointwise `(u t x)^r ≤ M_inf^r` by `Real.rpow_le_rpow`.
- Integrate over unit interval using `intervalDomain_integral_nonneg`/`intervalIntegral.integral_mono_on` or a local continuous/integrability helper if needed.

This is the easiest live sorry to close and produces a reusable endpoint after an L∞ bound.

### Route 3: close `intervalDomain_Linf_of_Lp_and_gradient`

Target:

```lean
theorem intervalDomain_Linf_of_Lp_and_gradient
```

from `IntervalDomain1DLinfRoute.lean`.

After Route 1, use:

- `intervalDomainLift_rpow_agmon_bound_qsqrt` or `intervalDomainLift_rpow_agmon_bound`;
- `hLp_bound t ht0 htT`;
- `hgrad_bound t ht0 htT`;
- monotonicity of `Real.sqrt` for nonnegative integrals;
- `nlinarith`/`ring_nf` for the final bound.

This is the best second target if the goal is to make the 1D L∞ direct route genuinely usable.

## 5. Strategic recommendation

Short term: do not patch more Paper2/Paper3 headline wrappers until the current direct-route sorries are reduced. The wrapper surface is now rich enough; the remaining high-signal work is proving the bridge and endpoint lemmas that make the new 1D route real.

Attack order:

1. `intervalDomain_moser_gradient_integral_eq_weighted` / `_of_regularity`.
2. `intervalDomain_all_Lp_of_Linf`.
3. `intervalDomain_Linf_of_Lp_and_gradient`.

Defer `intervalDomain_Lp_energy_and_dissipation_of_regularity` and `intervalDomain_gn_absorbed_interpolation_of_agmon` until the easy bridge/endpoint lemmas are closed; they are the genuine analytic heart of the direct route.
