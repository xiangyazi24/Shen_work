# Q2448 shen1 — Paper3-local integrated-step route scope audit

Repo: `xiangyazi24/Shen_work`

Audited upstream ref: `main` at `830352766089c95945fc741ccc208762862c54c6`

Question: whether the current local Paper3-specific direct `to_routeResiduals` layer should be committed now, or whether a generic `IntegratedStepResiduals` surface should first be moved into `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`.

## Verdict

The Paper3-local direct `to_routeResiduals` layer is acceptable to commit now, provided it really does what you describe:

```lean
allLpBoundFromBootstrap :=
  intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    h.integratedStep
endpointBoundFromLp :=
  intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    h.integratedStep h.quantitativeEndpoint
```

and `driftBoundFromMass` uses the resulting `Corollary_2_1` and `Proposition_2_5` only as **outputs** for the usual finite-horizon boundedness/drift argument.

This is logically honest.  It does not derive old Moser inputs from Corollary 2.1, and it does not claim the hard theorem producing `IntegratedMoserFirstCrossingStep` has been proved.

For a clean zero-sorry commit, I recommend the minimal local scope:

1. Keep the integrated-step consumers in `P3MoserActualWiring.lean`.
2. Commit the Paper3-local direct integrated-step residual route in `IntervalDomainActualLinearStatementAssembly.lean`.
3. Do **not** first move a generic `IntegratedStepResiduals` structure into `IntervalDomainMoserLadderAtoms.lean`, unless you already have that refactor building.

The generic extraction is a reasonable later cleanup, but it is not required for logical honesty.  Doing it now increases blast radius and import churn without reducing the current analytic frontier.

## Why the Paper3-local route is honest

The current upstream generic Moser-ladder route is:

```lean
IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals
```

It produces:

```lean
Corollary_2_1 intervalDomain p
Proposition_2_5 intervalDomain p
```

from the old actual atoms, then uses those two theorem outputs inside `driftBoundFromMass` to obtain finite-horizon boundedness and the chemotactic drift bound.  That use of `Corollary_2_1` and `Proposition_2_5` is legitimate: they are exactly what `IntervalDomainMassLpSmoothingRouteResiduals` needs.

Your local Paper3 route has the same outer shape but changes the producer of the two theorem outputs:

```text
integratedStep + quantitativeEndpoint
  -> Corollary_2_1 / Proposition_2_5
  -> IntervalDomainMassLpSmoothingRouteResiduals
  -> Paper3 mainline
```

That is fine.

The bad route from Q2445 was different:

```text
integratedStep
  -> Corollary_2_1
  -> moserDissipationDropBeforeNonnegB / RelativeMoserInterpolationBefore
  -> old Moser route
```

The new local route does not do this, so it avoids the circular/misleading dependency.

## Minimal commit contents

### 1. `P3MoserActualWiring.lean`

Keep/add:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

and:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Then keep the two consumers:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

Optional but useful:

```lean
#print axioms intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
#print axioms intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

Expected axioms should be no worse than the surrounding file's standard proof stack.  In particular, the theorems should not add `sorryAx`, new axioms, or a hidden theorem producing the first-crossing step.

### 2. `IntervalDomainActualLinearStatementAssembly.lean`

It is acceptable for the new route to live here first because it is genuinely Paper3-specific: it combines actual-linear-small boundedness, closed-energy L2 seed conversion, the integrated-step Moser atom, and the Paper3 mainline wrappers.

A clean local shape is:

```lean
/-- Closed-energy actual-linear-small residuals using a supplied integrated
first-crossing step.  This route bypasses the old pointwise drop and relative
Moser residual fields. -/
structure IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        Nonempty
          (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u)
  integratedStep :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
  quantitativeEndpoint :
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
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

Then the local direct conversion is acceptable:

```lean
namespace IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals

/-- Direct route to the old mass/Lp/smoothing route residual surface.

This does not derive old Moser atoms.  It only supplies the route-level outputs
`Corollary_2_1` and `Proposition_2_5` using the integrated-step consumers. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  driftBoundFromMass := by
    intro u₀ hu₀ T hT u v hsol htrace hmass
    have hCor21 : Corollary_2_1 intervalDomain p :=
      intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
        h.integratedStep
    have hProp25 : Proposition_2_5 intervalDomain p :=
      intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
        h.integratedStep h.quantitativeEndpoint
    -- reuse the same L2 seed / boundedness / drift argument as
    -- `IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals`.
    -- This is acceptable duplication for the first Paper3-local commit.
    ...
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  allLpBoundFromBootstrap :=
    intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
      h.integratedStep
  endpointBoundFromLp :=
    intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
      h.integratedStep h.quantitativeEndpoint

end IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals
```

The `...` in this display should be the same already-building body used in your local patch: closed-energy trace gives the L2 seed via `P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData`; the L2 seed gives `hbootstrap`; then `intervalDomainBoundedBefore_of_corollary21_and_proposition25` gives `IsPaper2BoundedBefore`; then `IntervalDomainChemotacticDriftBound_of_LinfBound` gives the drift bound.

### 3. Paper3 wrapper names

For the wrapper layer, these names are good and consistent with the existing file:

```lean
IntervalDomainSectorialMainlineMoserActualLinearSmallCEIntegratedStepFacts
IntervalDomainPaper3MainlineMoserActualLinearSmallCEIntegratedStepFrontierData
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEIntegratedStepFrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallCEIntegratedStepFrontierData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCEIntegratedStepFrontierData
```

If your local patch also has a P2-main proposition route variant, use:

```lean
IntervalDomainPaper3StatementMoserActualLinearSmallCEIntegratedStepP2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCEIntegratedStepP2MainData
```

but keep it as an optional wrapper.  The core logical patch is the residual-to-route conversion plus the mainline route.

## Import caveats

`IntervalDomainActualLinearStatementAssembly.lean` currently imports:

```lean
import ShenWork.Paper3.IntervalDomainStatementAssembly
import ShenWork.Paper3.IntervalDomainMoserLadderHeadline
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearSectorial
import ShenWork.PDE.P3MoserLemmaDischarge
```

Do not rely only on a transitive import for the new type.  Add an explicit import:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

If the two consumer theorems live in `P3MoserActualWiring.lean` and are not already visible through existing transitive imports in your local tree, also add:

```lean
import ShenWork.PDE.P3MoserActualWiring
```

In practice `IntervalDomainMoserLadderHeadline` imports `IntervalDomainMoserLadderAtoms`, and that imports `P3MoserActualWiring`, but explicit imports are safer for this patch because the new route names directly mention the integrated closure API.

Also add:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

near the existing `open` block.

## Why not move generic first?

Moving a generic structure into

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

is a good later refactor if a non-Paper3 route also needs the same integrated-step residual surface.  But it is not necessary for this commit.

Reasons to keep the first commit local:

1. The current residual is Paper3 actual-linear specific: it carries `closedEnergyTrace`, actual-linear boundedness data, and Paper3 sectorial wrappers.
2. The generic extraction would still need a separate Paper3 conversion from `closedEnergyTrace` to `l2SeedRegularity`, so it does not eliminate all local code.
3. It changes a shared low-level module and can force more imports or rebuild churn.
4. The logical risk you are avoiding is not duplication; it is deriving old Moser atoms from `Corollary_2_1`.  Your current direct local route already avoids that.

Therefore the best zero-sorry commit is the narrower Paper3-local route.

## What should be left out

Do not commit any theorem or def named like:

```lean
moserDissipationDropBeforeNonnegB_of_corollary21
relativeMoserInterpolationBefore_of_corollary21
```

Do not fill old fields:

```lean
moserDissipation
relativeMoserInterpolation
relativeMassGradient
rawMoserDrop
```

from `Corollary_2_1` or from the integrated-step output.

Do not add the hard theorem:

```lean
IntegratedMoserDissipationDropBefore
  + RelativeMoserInterpolationBefore
  + IntegratedMoserFirstCrossingRegularity
  -> IntegratedMoserFirstCrossingStep
```

in this commit.

## Recommended commit checklist

Before committing, verify these grep checks after stripping comments/strings if possible:

```text
0 occurrences: sorry
0 occurrences: admit
0 occurrences: native_decide
0 new axiom declarations
0 occurrences of: _of_corollary21
0 occurrences of: moserDissipationDropBeforeNonnegB_of_corollary21
0 occurrences of: relativeMoserInterpolationBefore_of_corollary21
```

Also run or keep the local successful checks for:

```text
lake env lean ShenWork/PDE/P3MoserActualWiring.lean
lake env lean ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
lake build ShenWork.PDE.P3MoserActualWiring
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

The current local Paper3-specific direct `to_routeResiduals` layer is acceptable to commit now if these pass.
