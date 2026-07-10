# CODEX_SPEC: Assembly filler — wire all frontiers into IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals

## Goal

Create `ShenWork/PDE/P3MoserAssemblyFiller.lean` that fills all 5 fields of
`IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals` from the now-proved
frontier theorems. This is PURE WIRING — every sub-result is already proved.

## The target structure (in IntervalDomainIntegratedMoserAssembly.lean:33)

```lean
structure IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace : ∀ u₀, PositiveInitialDatum ... → ... → Nonempty (ClosedEnergyIdentityTraceData ...)
  integratedMoserDissipation : ∀ {T rho p0} {u v}, hsol → hcross → hboot → IntegratedMoserDissipationDropBefore ...
  relativeMassGradient : ∀ {T rho p0} {u v}, hsol → hcross → hboot → ∃ cGrad, ...
  quantitativeEndpoint : ∀ {u₀}, PositiveInitialDatum ... → 0 < T → hsol → htrace → ∀ pExp, ... → LpPowerBoundedBefore ... → ∃ pSeq rootBound, ...
```

## How to fill each field

### Field 1: boundednessHyp
This is a parameter condition (`IntervalDomainBoundednessHyp p`). Take it as a hypothesis.

### Field 2: closedEnergyTrace
Already proved:
- `P3MoserClosedEnergyProducer.lean`: `ClosedEnergyIdentityTracePartialData` from classical solution
- `P3MoserFTCInfrastructure.lean`: remaining data from `IntegratedMoserEnergyWindowFTC` at exponent 2
- The FTC at exponent 2 comes from the `closedEnergyTrace` providers in `P3MoserEnergyContinuity.lean`

For this field, you need to derive `ClosedEnergyIdentityTraceData` from classical solution + initial trace.
Chain: classical → partial data (task 6) → FTC remaining (task 8) → full data.

The FTC at exponent 2 needs endpoint continuity (proved in task 2/4) + derivative integrability near t=0.
Take `closedEnergyTrace` as a hypothesis if wiring is complex.

### Field 3: integratedMoserDissipation
Signature: `hsol → hcross → hboot → IntegratedMoserDissipationDropBefore`

Use `intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE` (P3MoserIntegratedDissipationPDE.lean:46).
This needs extra inputs: hftc, hrel, hdata, hgap.
- hftc: IntegratedMoserEnergyWindowFTC — take as hypothesis or derive
- hrel: RelativeMoserInterpolationBefore — derive from relativeMassGradient field
- hdata: IntervalDomainIntegratedMoserClassicalRegularityData — derive from task 15's producer
- hgap: coefficient gap — take as hypothesis

**Simplest approach:** Create the filler with minimal extra hypotheses beyond `p : CM2Params`.
The fields that need "extra" inputs (hftc, classicalRegularity, hgap) should be taken as
explicit hypotheses of the filler function, similar to how `to_integratedStepResiduals`
takes `classicalRegularity` as an argument.

### Field 4: relativeMassGradient
Signature: `hsol → hcross → hboot → ∃ cGrad, ...`

Use task 9's producers:
- `intervalDomain_relativeMassGradient_of_classical_boundedBefore` (P3MoserRelativeMassGradientProducer.lean:428)
  needs `IsPaper2BoundedBefore` — but this is the OUTPUT of the Moser iteration, not available here.
- `intervalDomain_relativeMassGradient_components_BD_of_classical` (line 486) gives B+D unconditionally

For the full 4-tuple, the A,C components need BoundedBefore. Since BoundedBefore is the ITERATION OUTPUT
(not available when filling the field), consider:
- Option A: Fill the field with components B+D + carry A,C as hypotheses
- Option B: Use unconditional A,C producers if they exist
- Option C: Take BoundedBefore as a hypothesis of the filler

**Check existing unconditional producers** by grepping for the 4-tuple components.

### Field 5: quantitativeEndpoint
Signature: `PositiveInitialDatum → 0 < T → hsol → htrace → pExp → condition → LpPowerBoundedBefore → ∃ pSeq rootBound, ...`

Use task 14's `intervalDomain_moserQuantitativeEndpoint_of_integrated_dissipation`
(P3MoserQuantitativeEndpointDischarge.lean:75).

## File structure

```lean
import ShenWork.PDE.P3MoserIntegratedDissipationPDE
import ShenWork.PDE.P3MoserQuantitativeEndpointDischarge
import ShenWork.PDE.P3MoserGradientIntegrabilityFromDissipation
import ShenWork.PDE.P3MoserRelativeMassGradientProducer
import ShenWork.PDE.P3MoserClosedEnergyProducer
import ShenWork.PDE.P3MoserFTCInfrastructure
import ShenWork.Paper3.IntervalDomainIntegratedMoserAssembly

namespace ShenWork.IntervalDomainExistence.P3MoserAssemblyFiller

-- Main theorem: fill the assembly
theorem intervalDomain_integratedDropResiduals_of_classical
    {p : CM2Params}
    (hbdns : IntervalDomainBoundednessHyp p)
    -- Extra hypotheses for irreducible inputs:
    (hClosedTrace : ∀ u₀ ..., Nonempty (ClosedEnergyIdentityTraceData ...))
    (hFTC : ∀ ..., IntegratedMoserEnergyWindowFTC ...)
    (hGap : ∀ q ≥ p0, ∀ A K, 0 < A → 0 < K → 2 < q * A) :
    IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p := ...

end ShenWork.IntervalDomainExistence.P3MoserAssemblyFiller
```

## Rules
- 0 sorry, 0 custom axiom, 0 native_decide
- #print axioms must show ONLY [propext, Classical.choice, Quot.sound]
- Add the import to ShenWork.lean
- Verify with `lake env lean ShenWork/PDE/P3MoserAssemblyFiller.lean`
- If a field cannot be filled from existing infrastructure, REPORT what specific lemma is missing
  rather than using sorry
- Do NOT modify any existing files except adding import to ShenWork.lean

## Verification
```bash
lake env lean ShenWork/PDE/P3MoserAssemblyFiller.lean
# must show no errors
```
Then:
```lean
#print axioms intervalDomain_integratedDropResiduals_of_classical
-- must be [propext, Classical.choice, Quot.sound]
```
