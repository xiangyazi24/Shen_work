# Q2985 (shen1) — post-`5239f50d` integrated-Moser API audit

Repo: `xiangyazi24/Shen_work`  
Audited HEAD: `5239f50d30d7ec467d8bbd002090997fa6605625` (`Remove obsolete lower-average gap residual surface`)  
Scope: source-grounded Lean API/proof-frontier audit only; no source edits.  
Constraint: do not touch `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.

## Executive answer

The next lowest-risk **real wiring** step is in `ShenWork/PDE/P3MoserIntegratedClosure.lean`: add a fixed-coefficient wrapper that turns the already-proved coefficient-gap theorem

```lean
intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
```

into the public fixed predicate

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

by specializing `theta = 2` and applying

```lean
integratedMoserDissipationDropBefore_of_coeff_two
```

from `P3MoserDissipationShape`.

This is not a new analytic proof. It is pure wiring, but it reduces a real future handoff: downstream statement layers can ask for `LpBootstrapEnergyInequality + IntegratedMoserEnergyWindowFTC + regularity + nonnegativity + relative interpolation + scalar coefficient gap` instead of carrying `IntegratedMoserDissipationDropBefore` as a black-box residual.

The next lowest-risk **cleanup-only** step is in `ShenWork/PDE/P3MoserRegularityProducer.lean`: remove or deprecate four compatibility shortcut theorems whose lowerAverage / upperGap / upperDataGap parameters are now dead. Their proof bodies explicitly ignore those parameters and call the direct threshold-plan wrappers.

Do **not** delete the Type-valued high-excursion lower/upper frontier packages in `P3MoserIntegratedClosure.lean` yet. They are still forced by older split-route statement surfaces and are likely still externally useful to Zinan's producer file.

## 1. Remaining compatibility surfaces with dead or stronger assumptions

### A. Dead-argument shortcut theorems in `P3MoserRegularityProducer.lean`

File: `ShenWork/PDE/P3MoserRegularityProducer.lean`.

The following four theorems retain old lower-average / upper-gap parameters, but their current proof bodies only bind them to unused `_compat_*` locals and then call the direct threshold-plan route:

```lean
intervalDomain_firstCrossingStep_of_classical_and_frontiers
intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
```

Current shape, representative example:

```lean
theorem intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
    ...
    (hlower : ... IntegratedMoserHighExcursionLowerAverageWindowFrontier ...)
    (hupperDataGap : ... IntegratedMoserWindowUpperDataGapFrontier ...) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  have _compat_lower := hlower
  have _compat_upper := hupperDataGap
  exact intervalDomain_firstCrossingStep_of_classical_integratedData
    hreg hsol hdiss hrel hrho hp0_nonneg
```

These assumptions are genuinely dead in these four proof bodies. The clean replacement theorems already exist in the same file:

```lean
intervalDomain_firstCrossingStep_of_classical_integratedData
intervalDomain_firstCrossingStep_of_lite_classical_integratedData
intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
```

#### Recommended cleanup edit

Delete the four compatibility shortcut theorem blocks, or if external branch compatibility matters, mark them as deprecated and keep them for one cycle.

If deleting, also delete their four `#print axioms` lines in the `AxiomAudit` section:

```lean
#print axioms intervalDomain_firstCrossingStep_of_classical_and_frontiers
#print axioms intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
#print axioms intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
#print axioms intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
```

Expected build targets:

```bash
lake build ShenWork.PDE.P3MoserRegularityProducer
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
lake build ShenWork.Paper2.IntervalDomainStatementAssembly
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

Risk: low inside the current source tree; these are compatibility wrappers and the direct replacements already exist. External branches may still reference the old names, so deletion is an API break. If that matters, deprecate first rather than delete.

### B. Compatibility-named Paper3 route block: stale names, but no dead fields

File: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

The following route block remains compatibility-named with `LowerAverageUpperDataGap`, but the fields have already been cleaned up and every remaining field is used by the conversion to integrated-step data:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
```

Example: `IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.to_integratedStepResiduals` now consumes exactly the direct threshold-plan data:

```lean
classicalContinuityRegularity
integratedDissipation
relativeMoserInterpolation
quantitativeEndpoint
```

and no longer has lower-average / upper-data-gap fields.

#### Recommended cleanup edit

This is not the next best target if the goal is reducing assumptions: the assumptions are no longer dead. The remaining issue is naming/API hygiene.

If you want to clean it up, do a rename/deprecation pass only after downstream users have switched to the already cleaner integrated-step names:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainNoNegData
```

Risk: moderate API churn, low proof risk. This is cosmetic/stale-name cleanup, not a proof-frontier reduction.

## 2. Real wiring recommendation in `P3MoserIntegratedClosure.lean`

File: `ShenWork/PDE/P3MoserIntegratedClosure.lean`.

Current source already has:

```lean
intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap :
  ... → IntegratedMoserDissipationDropBeforeCoeff theta intervalDomain u T rho p0
```

and imported from `P3MoserDissipationShape`:

```lean
integratedMoserDissipationDropBefore_of_coeff_two :
  IntegratedMoserDissipationDropBeforeCoeff 2 D u T rho p0 →
  IntegratedMoserDissipationDropBefore D u T rho p0
```

The missing small wrapper is the fixed public predicate version.

### Recommended theorem to add

Add this immediately after `intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap`:

```lean
/-- Fixed-coefficient integrated Moser drop from the regular-energy coefficient-gap
route.

This specializes `intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap` to
`theta = 2`, then converts the coefficient-parametric predicate to the public
`IntegratedMoserDissipationDropBefore` predicate. -/
theorem intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
    {params : CM2Params} {T rho p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hgap :
      ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < p * A) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
  integratedMoserDissipationDropBefore_of_coeff_two
    (intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
      (params := params) (T := T) (rho := rho) (p0 := p0)
      (theta := (2 : ℝ)) (u := u)
      hboot henergy hFTC hreg hnonneg hrel hgap)
```

Add a `#print axioms` line for it in the audit section:

```lean
#print axioms
  intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
```

Expected build target:

```bash
lake build ShenWork.PDE.P3MoserIntegratedClosure
```

Optional downstream smoke tests:

```bash
lake build ShenWork.PDE.P3MoserRegularityProducer
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

Risk: very low. It uses existing imports and existing theorems. It does not touch `P3MoserHighExcursionProducer.lean`.

Limit: this wrapper still carries real analytic inputs: `hFTC`, `henergy`, `hreg`, `hnonneg`, `hrel`, and `hgap`. It does not prove those. It only exposes the already-proved route to the public fixed predicate consumed by threshold-plan wiring.

### Why not call the threshold-plan producer from `P3MoserIntegratedClosure.lean`?

Do not add a direct first-crossing theorem in `P3MoserIntegratedClosure.lean` that calls

```lean
P3MoserThresholdPlanProducer.integratedMoserFirstCrossingStep_of_abstract_data
```

because `P3MoserThresholdPlanProducer.lean` imports through the integrated-closure/high-excursion layer. Calling it from `P3MoserIntegratedClosure.lean` risks an import cycle. The right place for a first-crossing wrapper is an adjacent consumer file such as `P3MoserRegularityProducer.lean`, which already imports `P3MoserThresholdPlanProducer.lean`.

## 3. What should not be removed yet

### Type-valued high-excursion lower/upper packages remain live

Do **not** delete the Type-valued high-excursion split packages in `P3MoserIntegratedClosure.lean` as a low-risk cleanup. They are still forced by source-visible lower/upper split routes.

Important declarations in `P3MoserIntegratedClosure.lean` include:

```lean
IntegratedMoserFirstCrossingFromWindowFrontier
IntegratedMoserFirstCrossingLowerUpperFrontiers
IntegratedMoserFirstCrossingLowerAverageEpsilonData
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

They remain used/forced by older route surfaces, including:

* `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`
  ```lean
  IntervalDomainPaper2Prop25LowerUpperFrontierData
  IntervalDomainPaper2Prop25LowerUpperFrontierData.toIntegratedStepFrontierData
  ```
  This record only has `lowerUpperFrontiers` and `quantitativeEndpoint`; it does **not** carry regularity/integrated-dissipation/relative-interpolation, so it cannot be rerouted to the threshold-plan producer without changing the record's meaning.

* `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`
  ```lean
  IntervalDomainMassLpSmoothingWindowFrontierResiduals
  IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals
  ```
  These are explicitly window/lower-upper split residual surfaces. They are alternate producer-facing routes, not dead assumptions inside a direct-threshold proof.

* `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`
  ```lean
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals
  IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts
  IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
  ```
  These still carry `lowerUpperFrontiers` and convert through
  `integratedMoserFirstCrossingStep_of_lowerUpperFrontiers`.

Therefore, deleting the high-excursion Type-valued packages would require deleting the remaining lower/upper split route surfaces. That is not a low-risk proof-frontier cleanup; it is an API removal decision. It also risks interfering with Zinan's producer target surface.

### Lower-average data constructors still use their assumptions

In `P3MoserRegularityProducer.lean`, the data constructors

```lean
intervalDomain_lowerAverageEpsilonData_of_classical
intervalDomain_lowerAverageEpsilonData_of_lite_classical
intervalDomain_lowerAverageUpperDataGapData_of_classical
intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
```

still genuinely construct the corresponding legacy data packages, so their lower-average / upper-gap inputs are not dead. Keep them if the legacy data packages remain.

## 4. Recommended order of work

### Patch A — real wiring, very low risk

File: `ShenWork/PDE/P3MoserIntegratedClosure.lean`.

Add:

```lean
intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
```

as shown above.

Build:

```bash
lake build ShenWork.PDE.P3MoserIntegratedClosure
```

Impact: real wiring improvement. It exposes the current coefficient-gap route as the exact fixed integrated-dissipation predicate consumed downstream.

### Patch B — dead-argument API cleanup, low source risk / external API break

File: `ShenWork/PDE/P3MoserRegularityProducer.lean`.

Delete or deprecate:

```lean
intervalDomain_firstCrossingStep_of_classical_and_frontiers
intervalDomain_firstCrossingStep_of_lite_classical_and_frontiers
intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
```

and their `#print axioms` lines.

Build:

```bash
lake build ShenWork.PDE.P3MoserRegularityProducer
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
lake build ShenWork.Paper2.IntervalDomainStatementAssembly
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

Impact: removes stale assumptions from public theorem surfaces. This is API cleanup, not new analysis.

### Patch C — stale-name cleanup, moderate churn

File: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

Either leave the compatibility-named lowerAverage/upperDataGap route block in place, or remove it after all callers are on the integrated-step/Stability24 route names. This block no longer carries dead lowerAverage/upperDataGap assumptions, so removing it is naming cleanup only.

Build:

```bash
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

Impact: cosmetic API simplification; moderate external-name churn.

## Bottom line

The best next Codex task is **not** to delete high-excursion packages. The best low-risk wiring task is to add the fixed integrated-dissipation wrapper in `P3MoserIntegratedClosure.lean`. The best low-risk stale-surface cleanup is to remove/deprecate the four `P3MoserRegularityProducer` shortcut theorems whose old lowerAverage/upperGap arguments are now intentionally unused.
