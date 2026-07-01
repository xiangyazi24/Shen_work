# Q2996 (shen1) — PDE/Paper3 ladder surface for regular-energy coefficient-gap route

Repo: `xiangyazi24/Shen_work`  
Audited committed HEAD: `af19f8478ce16c590db64981f0dd0367d8560646` (`Add coefficient-gap first-crossing producer`)  
Assumed local pending patch: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` already adds
`IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData` plus its Prop. 2.5 / Cor. 2.1 / thin bootstrap target wrappers, and that patch has built on uisai2.

Scope: source-grounded Lean audit/design for the next additive **PDE/Paper3 ladder surface only**.  
Constraint respected: do **not** touch `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.  
Additive only: no replacement/deletion of existing integrated-step, integrated-Moser, window-frontier, lower/upper, or Paper3 actual-linear routes.

## Executive answer

The next PDE surface should live in:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

Add it immediately after:

```lean
end IntervalDomainMassLpSmoothingIntegratedMoserResiduals
```

and before:

```lean
/-- Lower-level inputs that refine `IntegratedStepResiduals` by replacing
the opaque `integratedStep` field with an explicit high-excursion
contradiction-window frontier supplier. -/
structure IntervalDomainMassLpSmoothingWindowFrontierResiduals
```

This makes the new route a sibling of the existing `IntervalDomainMassLpSmoothingIntegratedMoserResiduals` surface, and it converts to the canonical package:

```lean
IntervalDomainMassLpSmoothingIntegratedStepResiduals
```

That package is already the right junction because it supplies:

```lean
corollary21
proposition25
to_routeResiduals
aprioriBound
```

from one integrated first-crossing step plus the quantitative endpoint.

## Why not import the new Paper2 frontier into the PDE file?

Do **not** import `ShenWork.Paper2.IntervalDomainStatementAssembly` into `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`.  The PDE ladder file should remain below the Paper2 statement assembly layer.  The new Paper2 frontier and this new PDE residual should be parallel surfaces with the same data shape:

* Paper2 surface: statement-level Prop. 2.5 / Cor. 2.1 package.
* PDE surface: mass/Lp/smoothing ladder package that converts to `IntervalDomainMassLpSmoothingIntegratedStepResiduals`.

This avoids a layering/cycle risk while still routing through the same integrated-step atom produced by:

```lean
intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
```

## Exact PDE code

No new import is needed in `IntervalDomainMoserLadderAtoms.lean`.  At `af19f847`, it already imports:

```lean
import ShenWork.PDE.P3MoserRegularityProducer
```

and already opens:

```lean
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
```

Add this block at the placement above:

```lean
/-- Lower-level inputs that produce the integrated first-crossing step from the
regular-energy coefficient-gap route.

This is the mass/Lp/smoothing residual analogue of the Paper2
`IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData` surface.  It
keeps the route additive: the existing integrated-step, integrated-Moser,
window-frontier, and lower/upper frontier packages remain unchanged. -/
structure IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTC :
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
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
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

namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals

/-- Collapse the regular-energy coefficient-gap residuals to the canonical
integrated-step mass/Lp/smoothing residual package. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
      hsol
      hcross
      hboot
      (h.classicalRegularity hsol hcross hboot)
      (h.energyWindowFTC hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (h.coeffGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Corollary 2.1 from the regular-energy coefficient-gap residual package. -/
theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    Corollary_2_1 intervalDomain p :=
  h.to_integratedStepResiduals.corollary21

/-- Proposition 2.5 from the regular-energy coefficient-gap residual package. -/
theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    Proposition_2_5 intervalDomain p :=
  h.to_integratedStepResiduals.proposition25

/-- Build the old mass/Lp/smoothing residual package from the regular-energy
coefficient-gap route. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_integratedStepResiduals.to_routeResiduals

/-- A-priori bound from the regular-energy coefficient-gap residual package. -/
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_integratedStepResiduals.aprioriBound

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals
```

## `#print axioms` lines

Add these near the existing axiom audit block at the end of `IntervalDomainMoserLadderAtoms.lean`, immediately after the existing `IntervalDomainMassLpSmoothingIntegratedMoserResiduals` lines and before the `WindowFrontierResiduals` lines:

```lean
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.to_integratedStepResiduals
#print axioms IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.corollary21
#print axioms IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.proposition25
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.to_routeResiduals
#print axioms IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.aprioriBound
```

## Build target

For the additive PDE ladder surface:

```bash
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
```

A useful combined check, matching the current campaign targets, is:

```bash
lake build \
  ShenWork.PDE.IntervalDomainMoserLadderAtoms \
  ShenWork.Paper2.IntervalDomainStatementAssembly \
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

## Paper3 actual-linear wrapper: now or later?

I would **not** add a Paper3 actual-linear wrapper in the same patch unless an immediate Paper3 endpoint needs to consume this route.  The PDE surface above is the canonical next additive layer.  It already converts to `IntervalDomainMassLpSmoothingIntegratedStepResiduals`, and therefore to the existing route-level apriori package.  A Paper3 actual-linear wrapper would only be a parameter-side convenience wrapper that supplies:

```lean
a_pos := ha
chi_nonneg := le_of_lt hχ0
```

and forwards the same analytic fields.

If you do want that convenience wrapper now, put it in:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

inside the existing section:

```lean
/-! ### Moser-ladder route with actual-linear persistence -/
```

immediately after:

```lean
def IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals.to_moserLadder
```

and before:

```lean
/-! ### Closed-energy seed variant -/
```

Optional exact code:

```lean
/-- Regular-energy coefficient-gap mass/Lp/smoothing residuals for the
actual-linear-small regime.  The parameter-side fields `a_pos` and `chi_nonneg`
are supplied by the actual-linear-small wrapper hypotheses. -/
structure IntervalDomainMassLpSmoothingRegularEnergyCoeffGapActualLinearSmallResiduals
    (p : CM2Params) where
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTC :
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
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
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

/-- Build the generic regular-energy coefficient-gap residual package from the
actual-linear-small parameter hypotheses. -/
def IntervalDomainMassLpSmoothingRegularEnergyCoeffGapActualLinearSmallResiduals.to_regularEnergyCoeffGap
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapActualLinearSmallResiduals p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  classicalRegularity := h.classicalRegularity
  energyWindowFTC := h.energyWindowFTC
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint
```

Optional Paper3 `#print axioms` line if that wrapper is added:

```lean
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapActualLinearSmallResiduals.to_regularEnergyCoeffGap
```

But I recommend landing the PDE residual first.  The Paper3 actual-linear wrapper is mechanically harmless, but it is a convenience layer, not the next necessary proof frontier.

## Smallest viable alternative if the named surface is ill-typed

If Lean rejects the direct call to the producer theorem because namespace opening changes, qualify it explicitly:

```lean
ShenWork.IntervalDomainExistence.P3MoserRegularityProducer.
  intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
```

If the field name `energyWindowFTC` conflicts with local naming conventions, rename only the field to `windowFTC`; the type and converter remain identical.  To align with the already-pending Paper2 surface, I recommend keeping `energyWindowFTC`.

If someone insists that the PDE residual must literally convert through the new Paper2 `IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData`, that is the wrong layer for `IntervalDomainMoserLadderAtoms.lean`: it would require importing `ShenWork.Paper2.IntervalDomainStatementAssembly` into a PDE ladder file.  The smallest viable and layer-safe alternative is exactly the converter above to `IntervalDomainMassLpSmoothingIntegratedStepResiduals`, which is already the canonical residual package used to recover Corollary 2.1, Proposition 2.5, the route residuals, and the apriori bound.
