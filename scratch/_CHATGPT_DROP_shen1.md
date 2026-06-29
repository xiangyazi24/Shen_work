# Q2222 R3 Paper3 terminal/mainline residual thinning audit

Audited current `main` at commit `09140eae`.

## 1. Terminal Moser residual record

Record: `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals p`.

### `boundednessCore`

Classification: already thinned parameter residual; pure packaging to the old bundle, but not removable.

Existing chain:

`IntervalDomainMoserActualLinearSmallBoundednessCore.to_boundednessHyp hb`

This reconstructs `IntervalDomainBoundednessHyp p` by using:

- `Or.inr h.alphaAbsorption` for `IntervalDomainSharpL2AbsorptionThreshold p`;
- wrapper `hb : 0 < p.b`;
- `h.alphaAbsorption : 2 * p.γ < p.α`;
- `p.hγ : 0 < p.γ`;
- `h.gammaDimension : p.γ * (p.N : ℝ) < 2`.

The field still contains two genuine parameter assumptions: `alphaAbsorption` and `gammaDimension`.

### `closedEnergyTrace`

Classification: pure packaging already reducible downstream, but the trace itself is a genuine analytic residual.

Existing chain:

`closedEnergyTrace` → `P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData` → old `l2SeedRegularity` field in `IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals`.

This is used in `IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals.to_actualLinearSmallResiduals`.

### `rawMoserDrop`

Classification: pure packaging already reducible to the repaired physical-`B` predicate; the pointwise drop is still a genuine residual and should not be derived from the generic energy interface.

Existing chain:

`rawMoserDrop` → `moserDissipationDropBeforeNonnegB_of_raw_drop` → `MoserDissipationDropBeforeNonnegB` → `moser_step_of_energy_nonnegB_relative_interpolation` → `moser_iteration_chain_of_energy_nonnegB_relative_interpolation` → `intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB` and `intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`.

No-go caveat: `P3MoserDissipationShape.lean` contains `unitLinearDrop_not_MoserDissipationDropBeforeNonnegB`, so this pointwise drop shape is not an automatic consequence of the broad Lp energy interface.

### `relativeMassGradient`

Classification: pure packaging already reducible downstream, but the mass-gradient package is a genuine analytic residual.

Existing chain:

`relativeMassGradient` → `P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient` → `RelativeMoserInterpolationBefore`.

This is used in `IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals.to_closedEnergyResiduals`.

### `terminalPointwise`

Classification: wireable by existing inline proof with small Lean glue.

Current code converts it inline inside `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.to_CERawGradResiduals`. The proof chooses constant endpoint sequences:

- `pSeq := fun _ => q`;
- `rootBound := fun _ => R`;
- witness index `0`;
- endpoint bound `⟨R, hR, 0, hq, hR, le_rfl, hpoint⟩`.

This should be named as a helper theorem. Exact suggested helper:

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper3

noncomputable section

/-- A direct terminal pointwise power-control witness supplies the older
quantitative Moser endpoint by choosing constant endpoint sequences. -/
theorem intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl
    {p : CM2Params}
    (hterminal :
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
            IntervalDomainMoserPointwisePowerControlBefore u T q R) :
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
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound := by
  intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
  rcases hterminal hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨q, R, hq, hR, hpoint⟩
  refine ⟨fun _ => q, fun _ => R, ?_⟩
  intro _hAll
  exact ⟨R, hR, 0, hq, hR, le_rfl, hpoint⟩

end

end ShenWork.Paper3
```

Then `to_CERawGradResiduals` can replace the inline block with:

```lean
quantitativeEndpoint :=
  intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl
    h.terminalPointwise
```

## 2. Sectorial terminal mainline facts

Record: `IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts p`.

### `spectralSemigroupOrbitBound`

Classification: genuine analytic residual.

Wireable chain after it is supplied:

`intervalDomain_spectralSemigroupOrbitBoundRaw_of_sectorialConcrete` → `intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound` → `intervalDomain_Lemma_A_1_of_spectralSemigroupOrbitBound` → Theorem 2.2 wrappers such as `intervalDomain_Theorem_2_2_xpSigma_local_exponential_branch_of_spectralSemigroupOrbitBound`.

The linear unit-interval spectral decay is already separated and proved; this field is the remaining nonlinear orbit-comparison/Duhamel estimate.

### `continuation`

Classification: genuine analytic residual.

Consumed by:

`intervalDomainGlobalSolutionExists_of_standardContinuation_gluing_and_massLpSmoothing` → `intervalDomain_smallDataGlobal_of_globalSolutionExists` and `intervalDomain_massConstrainedSmallDataGlobal_of_globalSolutionExists` → sectorial core existence.

No exact producer for `IntervalDomainStandardContinuationGluingData p` was found in the inspected route.

### `massLpSmoothing`

Classification: composite reduced Moser route. The field is terminal-residual data; its conversions are pure packaging, while its lower-level analytic atoms remain real residuals.

Conversion chain:

`IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts.to_CERawGradFacts hb` → `IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts.to_CEGradFacts` → `IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts.to_closedEnergyFacts` → `IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts.to_moserActualLinearSmallFacts` → `IntervalDomainSectorialMainlineMoserActualLinearSmallFacts.to_aprioriActualLinearSmallFacts` → `IntervalDomainSectorialMainlineMoserActualLinearSmallFacts.to_coreExistence`.

The actual-linear persistence fields are not carried here; they are produced by `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` from `ha`, `hb`, `hχ0`, `hm`, `hβ`, and `hχ`.

## 3. Full P2Main statement route

Record: `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData p C M0 uBar vLower K`.

### `propositions`

Type: `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C`.

Fields:

- `negativeBound`: genuine residual / no-go to derive from Paper2 main. The generic wrapper `paper3_proposition1Targets_of_paper2MainTargetsData` explicitly consumes `negativeBound` separately and uses only `main.2.1` and `main.2.2` for Paper3 Propositions 1.4 and 1.3. The source comment says this is not derived from Paper2 Theorem 1.1 and points to `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`.
- `paper2Main`: wireable if supplied by the preferred Paper2 route. In Paper3 it is pure proposition packaging: `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData` → `paper3_proposition1Targets_of_paper2MainTargetsData` extracts Paper2 Theorem 1.2 and Theorem 1.3.

### `mainline`

Type: `IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData p M0 uBar vLower K`.

Fields:

- `core`: same three-field sectorial terminal facts above; contains genuine `spectralSemigroupOrbitBound`, genuine `continuation`, and the reduced terminal Moser residuals.
- `compactness`: see compactness map below.
- `stability`: see stability map below.

Wrapper chain:

`intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainData` → `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData` plus `intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData`.

## 4. Compactness/regularization input structure

Record: `IntervalDomainPaper3ConcreteCompactnessRegularizationData p M0 uBar vLower K`.

- `upperEq`: wireable with a canonical concrete `K` whose `upperEnvelope` is `intervalDomain.supNorm`; for arbitrary `K`, it remains a structural field. It feeds `intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm` through `intervalDomain_compactness_regularization_support_of_frontiers`.
- `compact`: genuine analytic residual, consumed by `Lemma_3_2.of_timeTranslateCompactnessRaw`.
- `initialContinuity`: genuine analytic/topological residual, consumed by `Lemma_3_3.of_assumed_continuity_branch`; the concrete bridge is `intervalDomain_Lemma_3_3_for_concreteStabilityNorms_of_initialContinuityRaw`.
- `minimalUpper`: genuine analytic residual, consumed by `Lemma_3_5.of_assumed_bound_branch`.
- `resolvent`: genuine analytic residual, consumed by `Lemma_7_1.of_neumannResolventGradientBoundExistsRaw`.

Assembly chain:

`IntervalDomainPaper3ConcreteCompactnessRegularizationData` → `intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers` → `intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers` → `intervalDomain_compactness_regularization_support_of_frontiers`.

## 5. Stability 2.3--2.5 input structure

Record: `IntervalDomainPaper3Stability23To25FrontierData p C`.

All eight fields are genuine stability frontiers:

- `globalNonminimal23`
- `globalMinimal23`
- `expNonminimal23`
- `expMinimal23`
- `global24`
- `exp24`
- `global25`
- `exp25`

Existing chain:

`IntervalDomainPaper3Stability23To25FrontierData` → `intervalDomain_paper3_stability23To25Targets_of_frontiers` → `intervalDomain_Theorem_2_3_to_2_5_for_concreteStabilityNorms_of_frontiers`.

No inspected file produces these eight universal global/exponential stability inputs. The wrappers only package them into Theorems 2.3, 2.4, and 2.5.

## 6. Smallest next Lean edit

The smallest faithful edit after `09140eae` is to name the inline terminal endpoint bridge:

1. Add `intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl` near `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals`.
2. Replace the inline `quantitativeEndpoint := by ...` block in `to_CERawGradResiduals` with a call to that helper.

This edit reduces misleading headline surface by making explicit that `terminalPointwise` is not the same as `quantitativeEndpoint`; it is a stronger terminal atom that purely packages into the older endpoint shape. It does not remove or fake any analytic residual.

The next larger cleanup would be a canonical-`K` compactness wrapper that discharges `upperEq` by construction, but that is more invasive because it chooses a concrete `CompactnessData intervalDomain`. The terminal helper is strictly smaller and mechanically local.
