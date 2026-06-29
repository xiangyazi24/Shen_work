# Q2236 Paper3 actual-linear terminal route audit

Audited current `main` around `e3aa461e`, after the named bridge `intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl` was added in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

## 1. Pieces now closed or wired by named bridges

### Terminal pointwise endpoint

`terminalPointwise` is now explicitly wired into the older `quantitativeEndpoint` interface by:

`intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl`

The exact bridge is curried over one solution/initial-datum instance. It takes the terminal field shape

```lean
∀ {u₀ : intervalDomain.Point → ℝ},
  PositiveInitialDatum intervalDomain u₀ →
∀ {T : ℝ}, 0 < T →
∀ {u v : ℝ → intervalDomain.Point → ℝ},
  IsPaper2ClassicalSolution intervalDomain p T u v →
  InitialTrace intervalDomain u₀ u →
∀ pExp,
  max (p.N : ℝ)
      (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
  LpPowerBoundedBefore intervalDomain pExp T u →
    ∃ q R, 0 < q ∧ 0 ≤ R ∧
      IntervalDomainMoserPointwisePowerControlBefore u T q R
```

and returns the old endpoint witness

```lean
∃ pSeq rootBound : ℕ → ℝ,
  (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
    IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

by choosing constant sequences `pSeq := fun _ => q` and `rootBound := fun _ => R`, with witness index `0`. The conversion `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.to_CERawGradResiduals` now calls this named theorem instead of carrying the proof inline.

### Boundedness core

`boundednessCore` is already wired by:

`IntervalDomainMoserActualLinearSmallBoundednessCore.to_boundednessHyp hb`

This reconstructs `IntervalDomainBoundednessHyp p` from `alphaAbsorption`, `gammaDimension`, wrapper `hb : 0 < p.b`, and `p.hγ`. This is packaging for the old boundedness bundle, but the two core facts remain real assumptions: `2 * p.γ < p.α` and `p.γ * (p.N : ℝ) < 2`.

### Closed-energy seed

`closedEnergyTrace` is wired to the older L² seed field by:

`P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData`

used in `IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals.to_actualLinearSmallResiduals`.

### Raw Moser drop

`rawMoserDrop` is wired to the repaired physical-`B` Moser drop predicate by:

`moserDissipationDropBeforeNonnegB_of_raw_drop`

used in `IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals.to_CEGradResiduals`.

Downstream, `MoserDissipationDropBeforeNonnegB` participates in the Moser chain through `moser_step_of_energy_nonnegB_relative_interpolation`, `moser_iteration_chain_of_energy_nonnegB_relative_interpolation`, `intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB`, and `intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`.

### Relative mass-gradient package

`relativeMassGradient` is wired to `RelativeMoserInterpolationBefore` by:

`P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient`

used in `IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals.to_closedEnergyResiduals`.

### Actual-linear persistence

The mainline no longer carries the four persistence parts. They are produced by:

`intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`

inside `IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.to_coreExistence` / `IntervalDomainSectorialMainlineMoserActualLinearSmallFacts.to_coreExistence`, from `ha`, `hb`, `hχ0`, `hm`, `hβ`, and `hχ`.

### Paper2-main proposition routing

In the P2Main terminal route,

`intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData`

routes Paper3 Proposition 1.3 and Proposition 1.4 through the Paper2 main theorem target bundle. It deliberately does not discharge Paper3 Proposition 1.2.

## 2. Remaining fields: genuine analytic residuals vs packaging-only

### `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals p`

Packaging / already wired:

- `boundednessCore`, as above, packages into `IntervalDomainBoundednessHyp p` once `hb` is supplied.
- `closedEnergyTrace`, `rawMoserDrop`, `relativeMassGradient`, and `terminalPointwise` all have named packaging/conversion bridges.

Genuine remaining residuals:

- `boundednessCore.alphaAbsorption` and `boundednessCore.gammaDimension` are genuine parameter-side assumptions.
- `closedEnergyTrace` itself is a genuine closed energy identity/trace residual.
- `rawMoserDrop` is a genuine pointwise physical-drop residual. It should not be derived from the broad Lp energy inequality; `P3MoserDissipationShape.lean` contains no-go/counterexample material against such automatic pointwise-drop claims.
- `relativeMassGradient` is a genuine mass-gradient / lower-order interpolation package.
- `terminalPointwise` is a genuine terminal pointwise Moser endpoint estimate, though it now packages cleanly into `quantitativeEndpoint`.

### `IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts p`

Packaging / wired:

- `massLpSmoothing` converts through
  `to_CERawGradFacts hb` → `to_CEGradFacts` → `to_closedEnergyFacts` → `to_moserActualLinearSmallFacts` → `to_aprioriActualLinearSmallFacts` → `to_coreExistence`.

Genuine remaining residuals:

- `spectralSemigroupOrbitBound : IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p` is a nonlinear sectorial orbit/Duhamel comparison residual. The linear spectral decay part is already separated and wired through `intervalDomain_spectralSemigroupOrbitBoundRaw_of_sectorialConcrete`, `intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound`, and `intervalDomain_Lemma_A_1_of_spectralSemigroupOrbitBound`, but no producer for the nonlinear orbit bound itself is present.
- `continuation : IntervalDomainStandardContinuationGluingData p` is a genuine continuation/gluing residual. It is consumed by `intervalDomainGlobalSolutionExists_of_standardContinuation_gluing_and_massLpSmoothing`, then by `intervalDomain_smallDataGlobal_of_globalSolutionExists` and `intervalDomain_massConstrainedSmallDataGlobal_of_globalSolutionExists`.

### `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData`

Packaging / wired:

- `paper2Main` inside `propositions` is consumed by the Paper2-main proposition bridge to supply Paper3 Propositions 1.3 and 1.4.
- `mainline` is routed through `intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData`.

Genuine remaining residuals:

- `propositions.negativeBound` is still the independent Paper3 Proposition 1.2 residual. It must not be derived from Paper2 Theorem 1.1; the statement-layer comment explicitly points to `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`.
- `mainline.core.spectralSemigroupOrbitBound` and `mainline.core.continuation` are genuine residuals.
- terminal Moser atoms inside `mainline.core.massLpSmoothing` are genuine lower-level residuals as listed above.
- `mainline.compactness` and `mainline.stability` remain genuine frontiers except for small structural packaging fields noted below.

### Compactness / regularization

Record: `IntervalDomainPaper3ConcreteCompactnessRegularizationData p M0 uBar vLower K`.

Packaging-only / structural:

- `upperEq` is structural, not analytic. It is used to route Lemma 3.4 through `intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm` and then through `intervalDomain_compactness_regularization_support_of_frontiers`.

Genuine residuals:

- `compact` feeds `Lemma_3_2.of_timeTranslateCompactnessRaw`.
- `initialContinuity` feeds `Lemma_3_3.of_assumed_continuity_branch`; the concrete interval bridge is `intervalDomain_Lemma_3_3_for_concreteStabilityNorms_of_initialContinuityRaw`.
- `minimalUpper` feeds `Lemma_3_5.of_assumed_bound_branch`.
- `resolvent` feeds `Lemma_7_1.of_neumannResolventGradientBoundExistsRaw`.

I did not find an existing canonical `CompactnessData intervalDomain` object in the inspected files that would definitionally close `upperEq` without choosing a new `K`. So removing `upperEq` is possible only as a local wrapper around a newly chosen canonical `K`, not by wiring an already-existing producer.

### Stability Theorems 2.3--2.5

Record: `IntervalDomainPaper3Stability23To25FrontierData p C`.

All eight fields are genuine stability residuals:

- `globalNonminimal23`
- `globalMinimal23`
- `expNonminimal23`
- `expMinimal23`
- `global24`
- `exp24`
- `global25`
- `exp25`

They are packaged by:

`intervalDomain_paper3_stability23To25Targets_of_frontiers` → `intervalDomain_Theorem_2_3_to_2_5_for_concreteStabilityNorms_of_frontiers`.

No inspected producer discharges these global/exponential stability fields.

## 3. Existing producers that should be wired now

The only newly relevant producer was the terminal endpoint bridge, and it is already wired:

`intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl`

No further producer appears to be sitting unused for the remaining analytic fields. In particular:

- no producer for `IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p` was found;
- no producer for `IntervalDomainStandardContinuationGluingData p` was found;
- no producer for `closedEnergyTrace`, `rawMoserDrop`, `relativeMassGradient`, or `terminalPointwise` was found beyond their packaging bridges;
- no producer for `negativeBound` was found, and deriving it from Paper2 main would contradict the documented no-go;
- no producer for the compactness/stability residuals was found.

## 4. Smallest honest next Lean edit

No new theorem wrapper is needed for the terminal bridge; it already exists and is used. The smallest honest next edit is a doc/comment clarification on the preferred terminal P2Main route, not a theorem pretending to close more analysis.

Suggested placement: immediately above `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData` in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

Suggested replacement/extension of the existing doc comment:

```lean
/-- Full interval-domain Paper3 statement frontiers using the direct terminal
pointwise endpoint input, with Proposition 1.3/1.4 routed through the Paper2
main theorem target bundle.

This is the preferred current actual-linear terminal statement route.  The
terminal Moser endpoint is no longer inline: `terminalPointwise` is converted to
`quantitativeEndpoint` by
`intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl`.
The route is still intentionally conditional: it carries the independent
`negativeBound` residual for Paper3 Proposition 1.2, the sectorial nonlinear
orbit bound, continuation/gluing, the terminal Moser analytic atoms,
compactness/regularization frontiers, and Theorem 2.3--2.5 stability frontiers.
Paper2 main targets discharge only the Proposition 1.3/1.4 branches, not
`negativeBound`. -/
```

Risk classification: local documentation-only cleanup. A canonical-`K` wrapper to remove `upperEq` would be a larger local wrapper/refactor because it must choose or define a concrete `CompactnessData intervalDomain`; it should be handled separately and should not hide `compact`, `initialContinuity`, `minimalUpper`, or `resolvent`.
