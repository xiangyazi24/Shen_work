# Q2968 (shen1) — Moser ladder lowerAverage/upperDataGap residual audit

Repo: `xiangyazi24/Shen_work`  
Scope: source-grounded API audit; no project source edits.  
Context assumed: local patch has already refactored
`ShenWork/PDE/P3MoserRegularityProducer.lean` theorem
`intervalDomain_firstCrossingStep_raw_of_globalClassicalTraceAnchored_upperDataGapFrontiers`
to call the direct threshold-plan producer and no longer take lowerAverage / upperDataGap fields.

## Short answer

Yes. There are still residual surfaces carrying lowerAverage / upperDataGap / window-frontier fields even though the direct threshold-plan route can use regularity + energy nonnegativity + integrated dissipation + relative interpolation.

The lowest-risk concrete target is in:

* `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`
* structure:
  ```lean
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
  ```
* conversion theorem/def:
  ```lean
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.to_integratedStepResiduals
  ```

This structure carries both:

```lean
lowerAverage : ... IntegratedMoserHighExcursionLowerAverageWindowFrontier ...
upperDataGap : ... IntegratedMoserWindowUpperDataGapFrontier ...
```

but it also already carries enough data to run the threshold-plan producer directly:

```lean
classicalContinuityRegularity : ...
integratedDissipation : ...
relativeMoserInterpolation : ...
```

The current conversion still calls the old upper-data-gap route:

```lean
intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
  ...
  (h.lowerAverage hsol hcross hboot)
  (h.upperDataGap hsol hcross hboot)
```

That is now unnecessary.

## Safest Lean wiring patch

The safest first patch is proof-body-only: keep the structure fields for API compatibility, but make `to_integratedStepResiduals` ignore `lowerAverage` and `upperDataGap` and call the direct threshold-plan producer. This removes the actual proof dependency immediately without breaking existing constructors.

Patch the `integratedStep` field in
`IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.to_integratedStepResiduals` as follows:

```lean
namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals

/-- Convert the actual-linear-small component lowerAverage/upperDataGap
residual surface to the existing integrated-step actual-linear residual
surface.

The lower-average and upper-data-gap fields are no longer needed for the
conversion: the direct threshold-plan producer only needs regularity, energy
nonnegativity, integrated dissipation, relative interpolation, `rho_pos`, and
`p0_nonneg`. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
      p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
      (intervalDomain_classicalRegularityData_of_continuityRegularityData
        (IsPaper2ClassicalSolution.T_pos hsol).le
        (h.classicalContinuityRegularity hsol hcross hboot))
      hsol
      (h.integratedDissipation hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
```

This is a strictly weaker dependency path than the current one: it uses an existing theorem already imported through `P3MoserRegularityProducer`, and it does not need the window frontiers.

After that proof-body patch builds, the next API cleanup is to delete the two fields from the structure:

```lean
  lowerAverage : ...
  upperDataGap : ...
```

But I would do that as a second patch because downstream constructors may still fill those fields. The proof-body change is the lowest-risk compile test.

## Closely related PDE-level package

There is also a reusable PDE-level residual package in:

```lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

namely:

```lean
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals
```

It carries:

```lean
classicalRegularity
integratedDissipation
relativeMoserInterpolation
lowerAverage
upperDataGap
quantitativeEndpoint
```

but its conversion

```lean
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_integratedMoserResiduals
```

already drops `lowerAverage` and `upperDataGap` entirely:

```lean
classicalRegularity := h.classicalRegularity
integratedDissipation := h.integratedDissipation
relativeMoserInterpolation := h.relativeMoserInterpolation
quantitativeEndpoint := h.quantitativeEndpoint
```

So this package is already internally routed through the direct integrated-Moser residual surface:

```lean
IntervalDomainMassLpSmoothingIntegratedMoserResiduals
```

For this file, the safe API cleanup is even more direct: remove the `lowerAverage` and `upperDataGap` fields from
`IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`, and remove the corresponding assignments from any constructors. The conversion itself needs no semantic change because it does not use those fields.

However, because `Paper3/IntervalDomainActualLinearStatementAssembly.lean` still has a `to_lowerAverageUpperDataGapResiduals` constructor that populates those fields, I would first land the Paper3 proof-body reroute above, then remove fields from both structures in a coordinated API-cleanup patch.

## What should not be refactored this way

These packages still carry window/lower-upper frontiers, but they do **not** have enough data to feed the direct threshold-plan producer as-is:

* `IntervalDomainPaper2Prop25LowerUpperFrontierData` in
  `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`.
  It only carries `lowerUpperFrontiers` plus `quantitativeEndpoint`; it does not carry regularity, integrated dissipation, or relative interpolation. So it is an alternate/historical lower-upper statement route, not a direct threshold-plan candidate.

* `IntervalDomainMassLpSmoothingWindowFrontierResiduals` in
  `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`.
  It carries an opaque `windowFrontier : IntegratedMoserFirstCrossingFromWindowFrontier ...`, not regularity/dissipation/relative-interpolation inputs.

* `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals` in
  `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`.
  It carries `lowerUpperFrontiers`, not the threshold-plan input tuple.

* `IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals` in
  `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.
  It carries `lowerUpperFrontiers`, not the direct regularity/dissipation/relative-interpolation package.

Those can remain as alternative WIP / historical routes unless you want to delete old APIs wholesale.

## Remaining genuine analytic inputs after the safe reroute

The direct threshold-plan route still genuinely needs the following residuals, depending on which surface is used:

* closed-time Moser regularity:
  ```lean
  IntervalDomainIntegratedMoserClassicalRegularityData
  ```
  or the continuity version
  ```lean
  IntervalDomainIntegratedMoserClassicalContinuityRegularityData
  ```
* integrated dissipation:
  ```lean
  IntegratedMoserDissipationDropBefore
  ```
* relative Moser interpolation:
  ```lean
  RelativeMoserInterpolationBefore
  ```
* endpoint / boundedness closure:
  ```lean
  IntervalDomainMoserQuantitativeEndpoint
  ```
  or the later terminal pointwise endpoint wrappers.
* L² seed / closed-energy trace fields in the Paper3 Moser ladder.
* unrelated Paper3 global/sectorial residuals: compactness, resolvent, stability24, continuation, and Paper2 main theorem input where applicable.

So the next residual reduction should **not** claim to prove any analytic estimate. It should only remove the now-obsolete lowerAverage / upperDataGap dependency from the conversion path that already has the threshold-plan data.
