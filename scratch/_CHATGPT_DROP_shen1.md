# Q2973 (shen1) — lowerAverage/upperDataGap API cleanup audit

Repo: `xiangyazi24/Shen_work`  
Scope: source-grounded API audit; no project source edits.  
Assumed local patch state: the two reroutes described in the prompt are already present and verified.

## Short answer

Yes, the fields can be removed with small source-visible edits, but the safest cleanup is staged.

1. **Lowest-risk patch:** remove `lowerAverage` and `upperDataGap` from the reusable PDE package
   ```lean
   IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals
   ```
   in `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`, and remove the two corresponding assignments in the Paper3 constructor
   ```lean
   IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.to_lowerAverageUpperDataGapResiduals
   ```
   This leaves the Paper3 compatibility structure unchanged, so external constructors of the Paper3 route do not immediately break.

2. **Next patch, still small but more API-breaking:** remove `lowerAverage` and `upperDataGap` from the Paper3 structure
   ```lean
   IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
   ```
   in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.
   In the local patched state its `to_integratedStepResiduals` no longer uses those fields, so only the structure definition and stale constructor assignments/comments need edits.

3. **Avoid renaming route structures in the same patch.** Names containing `LowerAverageUpperDataGap` become stale after field deletion, but renaming all theorem/structure names would create broad downstream churn. Treat that as a later deprecation/alias cleanup.

## Source hits / constructor inventory

Connector code search for the exact names found only the defining files and the Paper3 bridge:

* `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`
  appears in:
  * `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`
  * `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

* `IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals`
  appears only in:
  * `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

So within the source indexed by GitHub, this is not a wide-use API.

## 1. PDE package cleanup

File: `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`.

Current structure:

```lean
structure IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity : ...
  classicalRegularity : ...
  integratedDissipation : ...
  relativeMoserInterpolation : ...
  lowerAverage : ...
  upperDataGap : ...
  quantitativeEndpoint : ...
```

The conversion already ignores the two obsolete fields:

```lean
namespace IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals

def to_integratedMoserResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedMoserResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  classicalRegularity := h.classicalRegularity
  integratedDissipation := h.integratedDissipation
  relativeMoserInterpolation := h.relativeMoserInterpolation
  quantitativeEndpoint := h.quantitativeEndpoint
```

Therefore deleting the fields from this PDE structure is semantically safe.

### Minimal PDE patch

Delete the two fields:

```lean
  lowerAverage :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ q, p0 ≤ q →
        0 ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 q Cnext)
  upperDataGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ q, p0 ≤ q →
        0 ≤ q →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain u T rho p0 q)
```

No changes are needed in:

```lean
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_integratedMoserResiduals
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_integratedStepResiduals
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.aprioriBound
```

except docstring wording.

### Required Paper3 constructor edit for the PDE patch

File: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

Update:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.to_lowerAverageUpperDataGapResiduals
```

by deleting these assignments:

```lean
  lowerAverage := h.lowerAverage
  upperDataGap := h.upperDataGap
```

The rest of the constructor stays the same.

## 2. Paper3 package cleanup

File: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

Current Paper3 structure:

```lean
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace : ...
  classicalContinuityRegularity : ...
  integratedDissipation : ...
  relativeMoserInterpolation : ...
  lowerAverage : ...
  upperDataGap : ...
  quantitativeEndpoint : ...
```

After the local Q2968-style reroute, its

```lean
to_integratedStepResiduals
```

uses the direct threshold-plan producer and does not consume `lowerAverage` or `upperDataGap`. Therefore the fields are dead for the integrated-step path.

### Minimal Paper3 field deletion patch

Delete the fields from the structure:

```lean
  lowerAverage :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ q, p0 ≤ q →
        0 ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain u T rho p0 q Cnext)
  upperDataGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ q, p0 ≤ q →
        0 ≤ q →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain u T rho p0 q)
```

In the already-rerouted local version, `to_integratedStepResiduals` should need no proof-body change. In current unpatched main it would still need the Q2968 reroute first.

If the PDE package cleanup above is also applied, then `to_lowerAverageUpperDataGapResiduals` must also delete the same two assignments:

```lean
  lowerAverage := h.lowerAverage
  upperDataGap := h.upperDataGap
```

If only the Paper3 fields are deleted but the PDE structure still carries those fields, `to_lowerAverageUpperDataGapResiduals` can no longer be implemented. So do not delete Paper3 fields alone unless you either:

1. delete the PDE fields too, or
2. remove/deprecate `to_lowerAverageUpperDataGapResiduals` and any use of it.

## Risk ranking

### Low risk: PDE package field deletion only

Edits:

1. Remove `lowerAverage` / `upperDataGap` from `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`.
2. Remove the two assignments in Paper3 `to_lowerAverageUpperDataGapResiduals`.
3. Adjust docstrings.

Why low risk: the PDE conversion already ignores those fields, and GitHub search shows only the Paper3 bridge constructs the PDE package.

### Low-to-moderate risk: coordinated deletion in both PDE and Paper3 structures

Edits:

1. All edits from the low-risk patch.
2. Remove `lowerAverage` / `upperDataGap` from `IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals`.
3. Confirm local `to_integratedStepResiduals` is already the direct threshold-plan version.
4. Adjust docstrings.

Why higher risk: any local/unindexed code constructing the Paper3 compatibility structure with the old fields will break. Within the visible source, this is small.

### Moderate/high churn: rename all `LowerAverageUpperDataGap` route names

The names that become stale include:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
```

Renaming them would be semantically cleaner but is not the lowest-risk residual reduction. Prefer later aliases/deprecation wrappers.

## Recommended minimal patch plan

### Patch 1: safe source cleanup

Do this first:

```text
PDE/IntervalDomainMoserLadderAtoms.lean:
  - Remove lowerAverage and upperDataGap fields from
    IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.
  - Leave conversions unchanged.

Paper3/IntervalDomainActualLinearStatementAssembly.lean:
  - In to_lowerAverageUpperDataGapResiduals, remove:
      lowerAverage := h.lowerAverage
      upperDataGap := h.upperDataGap
  - Leave the Paper3 structure fields in place for compatibility.
```

This validates that the reusable PDE route no longer advertises dead high-excursion fields while preserving the Paper3 surface for downstream callers.

### Patch 2: Paper3 compatibility surface cleanup

After Patch 1 builds:

```text
Paper3/IntervalDomainActualLinearStatementAssembly.lean:
  - Remove lowerAverage and upperDataGap fields from
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.
  - Keep the old structure/theorem names for now, but update comments to say the route is retained as a compatibility name and now uses direct threshold-plan data.
```

### Patch 3: optional deprecation/rename

Only after downstream branches are updated, introduce clearer names such as:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallContinuityIntegratedResiduals
IntervalDomainSectorialMainlineMoserActualLinearSmallContinuityIntegratedFacts
```

and keep old names as abbrevs or compatibility wrappers if practical. This is cleanup, not the next lowest-risk residual reduction.

## Remaining real residuals after cleanup

Removing these fields does not prove new analysis. The remaining genuine inputs are still:

* `closedEnergyTrace` / L² seed regularity;
* `classicalContinuityRegularity` or `classicalRegularity` for closed-time Moser regularity;
* `integratedDissipation : IntegratedMoserDissipationDropBefore ...`;
* `relativeMoserInterpolation : RelativeMoserInterpolationBefore ...`;
* `quantitativeEndpoint` or terminal pointwise endpoint routes;
* plus Paper3 sectorial/compactness/stability residuals outside the Moser ladder.

So the field deletion is an API hygiene reduction, not a new analytic theorem.
