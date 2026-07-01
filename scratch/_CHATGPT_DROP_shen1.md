# Q2993 (shen1) — Paper2 Prop. 2.5 regular-energy coefficient-gap surface

Repo: `xiangyazi24/Shen_work`  
Audited committed HEAD: `e559581bb93e0036af36f7e6f12f5e719e6c065e` (`Expose fixed Moser dissipation coefficient-gap route`)  
Pending local theorem assumed present and already producer-target built:

```lean
intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
```

Scope: source-grounded Lean audit/design for the next additive **Paper2 surface only**.  
Constraint respected: do **not** touch `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.  
Additive only: no replacement of existing integrated-step, integrated-Moser, lower/upper, or actual-atom packages.

## Executive answer

The canonical file is:

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
```

not the generic `ShenWork/Paper2/StatementAssembly.lean`.  The interval-domain statement file already imports and opens the needed PDE Moser modules:

```lean
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.PDE.P3MoserLemmas
import ShenWork.PDE.P3MoserRegularityProducer

open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
```

The existing Prop. 2.5 integrated-step package is already the right target:

```lean
IntervalDomainPaper2Prop25IntegratedStepFrontierData
```

It carries exactly:

```lean
integratedStep :
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u
      (p.N : ℝ) T rho p0 →
      IntegratedMoserFirstCrossingStep intervalDomain u T rho p0

quantitativeEndpoint : ...
```

So the new surface should be an additive refinement that produces that `integratedStep` field using the pending PDE theorem, while forwarding the already-existing quantitative endpoint field unchanged.

## Placement

Add the following block in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` immediately after:

```lean
end IntervalDomainPaper2Prop25IntegratedMoserFrontierData
```

and before:

```lean
/-- Lower-average / upper-gap split frontier for interval-domain Proposition
2.5 and Corollary 2.1. -/
structure IntervalDomainPaper2Prop25LowerUpperFrontierData
```

This keeps the new route adjacent to the existing integrated-Moser and integrated-step Prop. 2.5 surfaces, and it does not disturb the lower/upper frontier package.

## Exact Lean code

No new import or open is needed in `IntervalDomainStatementAssembly.lean` once the pending local theorem is present in `P3MoserRegularityProducer.lean`, because that file already imports `ShenWork.PDE.P3MoserRegularityProducer` and opens `ShenWork.IntervalDomainExistence.P3MoserRegularityProducer`.

```lean
/-- Regular-energy coefficient-gap frontier for interval-domain Proposition 2.5
and Corollary 2.1.

Compared with `IntervalDomainPaper2Prop25IntegratedMoserFrontierData`, this
surface does not carry a pre-built integrated dissipation field.  Instead it
carries the regular-energy sources used by the fixed coefficient-gap route:
classical regularity data, the energy-window FTC, relative Moser interpolation,
and the coefficient gap. -/
structure IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData
    (p : CM2Params) : Prop where
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  windowFTC :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyWindowFTC intervalDomain u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coefficientGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ pExp, p0 ≤ pExp → ∀ A K : ℝ,
          0 < A → 0 < K → (2 : ℝ) < pExp * A
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData

/-- Collapse the regular-energy coefficient-gap frontier to the existing
integrated-step statement route. -/
def toIntegratedStepFrontierData
    {p : CM2Params}
    (h : IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData p) :
    IntervalDomainPaper2Prop25IntegratedStepFrontierData p where
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
      hsol
      hcross
      hboot
      (h.classicalRegularity hsol hcross hboot)
      (h.windowFTC hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (h.coefficientGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

end IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData
```

Then add the Prop. 2.5 wrapper near the existing integrated-step and integrated-Moser Prop. 2.5 wrappers, for example immediately after:

```lean
theorem intervalDomainPaper2_Proposition_2_5_of_integratedMoserFrontierData
```

```lean
/-- Regular-energy coefficient-gap frontier produces interval-domain
Proposition 2.5 through the existing integrated-step statement route. -/
theorem intervalDomainPaper2_Proposition_2_5_of_regularEnergyCoeffGapFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
    p hData.toIntegratedStepFrontierData

/-- Instance-facing regular-energy coefficient-gap Proposition 2.5 wrapper. -/
theorem
    intervalDomainPaper2_Proposition_2_5_of_regularEnergyCoeffGapFrontierDataFact
    (p : CM2Params)
    [hData :
      Fact (IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_regularEnergyCoeffGapFrontierData
    p hData.out
```

This is the smallest viable Prop. 2.5-only surface.  It does not replace the existing `IntervalDomainPaper2Prop25IntegratedMoserFrontierData`; it adds a more upstream regular-energy coefficient-gap route into the same already-canonical integrated-step endpoint.

## Optional sibling wrappers

If you want the new surface to mirror the existing integrated-step and integrated-Moser routes completely, add these adjacent to the existing Corollary 2.1 and combined wrappers:

```lean
/-- Regular-energy coefficient-gap frontier produces interval-domain
Corollary 2.1 through the existing integrated-step statement route. -/
theorem intervalDomainPaper2_Corollary_2_1_of_regularEnergyCoeffGapFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
    p hData.toIntegratedStepFrontierData

/-- Regular-energy coefficient-gap frontier produces both Tier-1 Moser outputs. -/
theorem
    intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_regularEnergyCoeffGapFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData p) :
    Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
    p hData.toIntegratedStepFrontierData
```

The Prop. 2.5-only structure and theorem above are sufficient for the requested next additive Paper2 surface; these siblings are convenience surfaces.

## `#print axioms` lines

Add these near the existing axiom-audit lines in `IntervalDomainStatementAssembly.lean`:

```lean
#print axioms IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData.toIntegratedStepFrontierData
#print axioms intervalDomainPaper2_Proposition_2_5_of_regularEnergyCoeffGapFrontierData
#print axioms intervalDomainPaper2_Proposition_2_5_of_regularEnergyCoeffGapFrontierDataFact
```

If the optional Corollary 2.1 wrappers are added, also add:

```lean
#print axioms intervalDomainPaper2_Corollary_2_1_of_regularEnergyCoeffGapFrontierData
#print axioms intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_regularEnergyCoeffGapFrontierData
```

## Build target

For the additive Paper2 surface:

```bash
lake build ShenWork.Paper2.IntervalDomainStatementAssembly
```

For root-closure confirmation:

```bash
lake build ShenWork
```

## Type-check and mismatch notes

1. **Against committed `e559581b` alone, the exact code is expected to fail only because the pending theorem is not yet in the committed GitHub HEAD.**  The identifier

   ```lean
   intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
   ```

   must first be present in `ShenWork/PDE/P3MoserRegularityProducer.lean`.  The user reports that theorem is already pending locally and has built through the producer target, so the Paper2 code above is intended for that local tree.

2. **The correct target is `IntervalDomainPaper2Prop25IntegratedStepFrontierData`, not `IntervalDomainMassLpSmoothingIntegratedStepResiduals`.**  The latter is a larger route-level package from `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean` and additionally requires:

   ```lean
   a_pos
   chi_nonneg
   boundednessHyp
   l2SeedRegularity
   quantitativeEndpoint
   ```

   That would be too strong for a Prop. 2.5-only Paper2 surface.  The existing Paper2 statement assembly package is exactly the minimal surface: `integratedStep + quantitativeEndpoint`.

3. **No direct mismatch with `intervalDomain_LpBootstrapEnergyInequality_of_regularity` appears in the Paper2 surface.**  This surface delegates the energy construction to the pending PDE theorem.  The pending theorem receives the same `hsol`, `hcross`, and `hboot` arguments carried by the Paper2 package and internally produces the strict-time `LpBootstrapEnergyInequality`.

4. **The coefficient-gap field is intentionally parameterized by the active bootstrap triple.**  In Prop. 2.5 the integrated-step consumer will instantiate the bootstrap with `rho = 2 * p.γ` via `intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms`, but Corollary 2.1 uses the bootstrap supplied by its hypothesis.  Therefore the field should stay fully polymorphic in `{T rho p0 u v}` rather than hard-coding `2 * p.γ`.

5. **The endpoint field must remain.**  `intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms` consumes both an integrated first-crossing step supplier and the quantitative endpoint/root tower.  The new coefficient-gap route only produces the first-crossing step; it does not replace endpoint extraction.
