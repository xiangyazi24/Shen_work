# Q2999 (shen1) — Paper3 actual-linear wrapper for regular-energy coefficient-gap route

Repo: `xiangyazi24/Shen_work`  
Audited pushed HEAD: `c6694aa8c2a9d89aa7b2a2e30569602a7b7c934d` (`Add Paper2 coefficient-gap frontier surface`)  
Assumed local pending patch: `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean` adds
`IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals` and its converters to
`IntervalDomainMassLpSmoothingIntegratedStepResiduals`, route residuals, and apriori bound.

Scope: source-grounded Lean audit/design for whether to add a Paper3 actual-linear-small wrapper now.  
Constraint respected: do **not** touch `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.  
Additive only: no deletion/replacement of existing integrated-step, integrated-Moser, lower/upper, closed-energy, raw-gradient, or terminal routes.

## Executive answer

Yes, a **thin Paper3 actual-linear wrapper is worthwhile now**, but keep it small.  The best immediate addition is not a new statement theorem family; it is a pair of converters in:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

The wrapper should:

1. introduce an actual-linear-small residual surface that supplies the regular-energy coefficient-gap inputs without carrying `a_pos`/`chi_nonneg` as fields;
2. convert that surface to the new PDE residual `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals` using the actual-linear hypotheses `ha : 0 < p.a` and `hχ0 : 0 < p.χ₀`;
3. also convert it to the existing actual-linear integrated-step route:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
```

so all existing integrated-step Paper3 mainline/frontier/P2Main wrappers remain reusable unchanged.

I would **not** add full `...RegularEnergyCoeffGapFrontierData` / `...P2MainData` statement variants in this same patch.  That would duplicate the already-existing integrated-step mainline and statement wrappers.  The small residual/facts converters are enough: callers can feed the converted core into the existing integrated-step actual-linear route.

## Placement

In `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`, place the new residual wrapper in the section:

```lean
/-! ### Integrated first-crossing step route
```

immediately after the existing namespace block:

```lean
end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
```

and before:

```lean
/-- Sectorial mainline facts with the integrated first-crossing step input. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
```

Then place the sectorial facts wrapper immediately after:

```lean
end
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
```

and before:

```lean
/-- Concrete interval-domain Paper3 mainline frontiers using the integrated
first-crossing step route and the actual-linear-small persistence producer. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
```

No new imports or opens should be needed once the pending PDE residual is present.  The file already imports `ShenWork.PDE.IntervalDomainMoserLadderAtoms`, and already opens `ShenWork.IntervalDomainExistence` plus the Moser namespaces used by the existing integrated-step route.

## Exact Lean code

```lean
/-- Actual-linear-small mass/Lp/smoothing residuals for the regular-energy
coefficient-gap route.

This is a thin wrapper over the reusable PDE residual
`IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals`: the actual-linear
wrapper does not store the parameter-side `a_pos` and `chi_nonneg` fields,
because those are supplied by the actual-linear-small theorem hypotheses.  It
also keeps the L² seed in the closed-energy trace form already used by the
actual-linear integrated-step route. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals

/-- Convert the actual-linear-small regular-energy coefficient-gap residuals to
the reusable PDE residual package. -/
def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  classicalRegularity := h.classicalRegularity
  energyWindowFTC := h.energyWindowFTC
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Convert the regular-energy coefficient-gap residuals to the existing
actual-linear integrated-step residual surface.  This keeps all downstream
integrated-step Paper3 routes reusable without introducing new statement-target
variants. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  integratedStep := by
    intro T rho p0 u v hsol hcross hboot
    exact
      intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
        hsol hcross hboot
        (h.classicalRegularity hsol hcross hboot)
        (h.energyWindowFTC hsol hcross hboot)
        (h.relativeMoserInterpolation hsol hcross hboot)
        (h.coeffGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Direct route residuals from the regular-energy coefficient-gap actual-linear
surface. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_regularEnergyCoeffGapResiduals ha hχ0).to_routeResiduals

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
```

This already forwards to the existing integrated-step actual-linear route.  If you want a small sectorial core wrapper as well, add this immediately after the existing integrated-step facts namespace:

```lean
/-- Sectorial mainline facts for the regular-energy coefficient-gap Moser route. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
      p

namespace IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts

/-- Convert the regular-energy coefficient-gap sectorial facts to the existing
integrated-step sectorial facts. -/
def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_integratedStepResiduals

/-- Convert the regular-energy coefficient-gap sectorial facts to the existing
a-priori actual-linear-small facts. -/
def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p :=
  h.to_integratedStepFacts.to_aprioriActualLinearSmallFacts ha hχ0

end IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
```

## Theorem / statement wrappers

I do **not** recommend adding new `...RegularEnergyCoeffGapFrontierData`, `...P2MainData`, or `...P2MainNoNegData` statement wrappers in this patch.  They would be mechanically equivalent to the existing integrated-step wrappers after applying:

```lean
h.core.to_integratedStepFacts
```

The preserved existing theorem names should remain the statement entry points:

```lean
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepFrontierData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainNoNegData
```

A caller that has the new regular-energy sectorial facts can use the existing integrated-step wrapper by forming:

```lean
{ core := hCore.to_integratedStepFacts
  compactness := hCompactness
  stability := hStability }
```

as the `IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData` argument.

If a direct wrapper is later desired for ergonomics, the smallest one should be a `def` converter, not a new proof theorem:

```lean
def IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFrontierData.toIntegratedStep
    ... : IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K := ...
```

but I would defer this until there is an actual call site.

## `#print axioms` lines

Add these near the existing axiom-audit block in `IntervalDomainActualLinearStatementAssembly.lean`, close to the other actual-linear integrated-step route prints:

```lean
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals.to_regularEnergyCoeffGapResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals.to_routeResiduals
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts.to_aprioriActualLinearSmallFacts
```

Expected audit output should remain the same trusted foundation only:

```text
[propext, Classical.choice, Quot.sound]
```

The `Classical.choice` dependency is already present in the existing closed-energy and integrated-step actual-linear wrappers because `closedEnergyTrace` is stored as `Nonempty`.

## Build targets

The minimal build after adding this Paper3 wrapper is:

```bash
lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

Because this wrapper depends on the pending PDE residual, the practical campaign check should include both:

```bash
lake build \
  ShenWork.PDE.IntervalDomainMoserLadderAtoms \
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

For the full current campaign closure:

```bash
lake build \
  ShenWork.PDE.IntervalDomainMoserLadderAtoms \
  ShenWork.Paper2.IntervalDomainStatementAssembly \
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

## Smallest viable alternative if this is ill-typed

If Lean cannot see the pending PDE residual because `IntervalDomainActualLinearStatementAssembly.lean` is checked against pushed `c6694aa8` only, then this wrapper is expected to fail with an unknown identifier:

```lean
IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals
```

The smallest viable alternative is to land the pending PDE patch first, then add the Paper3 wrapper above.

If namespace inference fails for the producer theorem, qualify it explicitly:

```lean
ShenWork.IntervalDomainExistence.P3MoserRegularityProducer.
  intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
```

If you want zero dependency on the new PDE residual, keep only `to_integratedStepResiduals`.  That is layer-safe and will still reuse the existing integrated-step actual-linear route, but it no longer demonstrates the connection to `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals`.  Since Q2999 explicitly asks to use the new PDE residual, I recommend keeping both converters.
