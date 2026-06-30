# Q2684 (shen1) — Paper3 actual-linear Moser interface thinning audit

Repo: `xiangyazi24/Shen_work`, Lean 4.  
Scope: non-Zinan files only.  Do **not** edit or rely on
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

I inspected `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`
and the imported Moser/PDE packages on current `main` through `7539485a`.

## Verdict

There is **one worthwhile mechanical thinning still available** for the Paper3
actual-linear Moser statement surfaces:

> Add an actual-linear wrapper surface for the already-existing PDE-level
> `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`, preferably
> using the new continuity regularity package
> `IntervalDomainIntegratedMoserClassicalContinuityRegularityData`.

This removes the remaining opaque

```lean
lowerUpperFrontiers :
  ... → Nonempty
    (IntegratedMoserFirstCrossingLowerUpperFrontiers intervalDomain u T rho p0)
```

from the preferred Paper3 actual-linear LowerUpper surface, replacing it by the
mechanically assembled lower-average / upper-data-gap route:

```lean
classicalContinuityRegularity
integratedDissipation
relativeMoserInterpolation
lowerAverage
upperDataGap
```

The proof chain is already in the repo; the missing part is only a Paper3-facing
wrapper in `IntervalDomainActualLinearStatementAssembly.lean`.

A second possible thinning is the old, optional one: add an IntegratedStep
sup-norm compactness thin route analogous to the existing LowerUpper thin route.
That is mechanically valid but probably API bloat unless direct integrated-step
callers need it.  The preferred route should now be lowerAverage/upperDataGap,
not bare IntegratedStep.

## 1. Exact redundant / wireable fields

### A. Main worthwhile thinning: `lowerUpperFrontiers`

Current Paper3 actual-linear field:

```lean
structure IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals
    (p : CM2Params) : Prop where
  ...
  lowerUpperFrontiers :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        Nonempty
          (IntegratedMoserFirstCrossingLowerUpperFrontiers
            intervalDomain u T rho p0)
  ...
```

This field is mechanically derivable from the imported lower-average /
upper-data-gap components, because `P3MoserRegularityProducer.lean` already has:

```lean
intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
intervalDomain_regularityLite_of_classicalRegularityData
intervalDomain_classicalRegularityData_of_continuityRegularityData
```

and `P3MoserIntegratedClosure.lean` already has the generic conversion path:

```lean
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.toLowerUpperFrontiers
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

At the PDE package level this is already consumed by:

```lean
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_integratedStepResiduals
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.aprioriBound
```

The Paper3 actual-linear file simply has no matching statement-facing surface
for that package yet.

### B. Regularity field inside that thinning should use continuity data

The PDE-level residual currently expects:

```lean
classicalRegularity :
  ... → IntervalDomainIntegratedMoserClassicalRegularityData u T p0
```

That can be mechanically thinned in a Paper3-facing wrapper to:

```lean
classicalContinuityRegularity :
  ... → IntervalDomainIntegratedMoserClassicalContinuityRegularityData u T p0
```

using:

```lean
intervalDomain_classicalRegularityData_of_continuityRegularityData
  (IsPaper2ClassicalSolution.T_pos hsol).le
  (h.classicalContinuityRegularity hsol hcross hboot)
```

This replaces raw `gradientTimeIntegrable` by the named
`gradientEnergyContinuous` residual.  It does **not** remove endpoint continuity:
for these actual-linear finite-horizon Moser callbacks, the input is only
`IsPaper2ClassicalSolution intervalDomain p T u v`, not
`IsPaper2GlobalClassicalSolution`, so the new global-classical at-right reducer
cannot be used without adding a new global branch field.

### C. Optional / not recommended by default: IntegratedStep thin compactness

Current field in:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
```

is still generic-K compactness:

```lean
compactness :
  IntervalDomainPaper3ConcreteCompactnessRegularizationData
    p M0 uBar vLower K
```

It can be mechanically thinned exactly like the existing lower/upper thin route:

```lean
IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData
IntervalDomainPaper3SupNormCompactnessRegularizationData.toConcrete
```

The existing proof pattern is already in:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperThinFrontierData
```

I would not add this unless direct `IntegratedMoserFirstCrossingStep` callers
really need a public co-equal fallback.  The lowerAverage/upperDataGap route is
strictly closer to the intended producer split.

## 2. Exact theorem chain for the main thinning

The chain for the proposed actual-linear lowerAverage/upperDataGap surface is:

```text
IntervalDomainIntegratedMoserClassicalContinuityRegularityData
  -- intervalDomain_classicalRegularityData_of_continuityRegularityData
IntervalDomainIntegratedMoserClassicalRegularityData
  -- intervalDomain_regularityLite_of_classicalRegularityData
IntervalDomainIntegratedMoserRegularityFrontierDataLite
  -- intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
IntegratedMoserFirstCrossingStep
  -- IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
IntervalDomainMassLpSmoothingRouteResiduals
  -- IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.to_coreExistence
IntervalDomainSectorialMainlineCoreExistence
  -- existing Paper3 mainline/statement target wrappers
IntervalDomainPaper3StatementTargets
```

If you prefer to route through the reusable PDE package first, the middle of the
chain is:

```text
new actual-linear residual
  -- to_lowerAverageUpperDataGapResiduals ha hχ0
IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals
  -- .to_integratedStepResiduals
IntervalDomainMassLpSmoothingIntegratedStepResiduals
  -- .to_routeResiduals
IntervalDomainMassLpSmoothingRouteResiduals
```

The only caveat: `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`
currently expects full `IntervalDomainIntegratedMoserClassicalRegularityData`, so
the Paper3-facing wrapper is where the continuity-data-to-regularity-data
conversion should happen.

## 3. Small compile-likely patch sketch

Place this in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`,
after the existing lower/upper residual section or just before the existing
LowerUpper thin route.  Add the `open` line near the other opens if it is not
already present.

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Actual-linear-small Moser residuals with the preferred lower-average /
upper-data-gap split.  Compared with the existing `LowerUpperResiduals`, this
replaces the opaque `IntegratedMoserFirstCrossingLowerUpperFrontiers` supplier by
regularity, integrated dissipation, relative interpolation, lower-average, and
upper-data-gap inputs.  The regularity input is stated in the new continuity
form, so gradient time-integrability is derived by
`intervalDomain_classicalRegularityData_of_continuityRegularityData`. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
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
  classicalContinuityRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalContinuityRegularityData u T p0
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
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
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals

/-- Convert the actual-linear-small lowerAverage/upperDataGap residual surface to
the existing integrated-step actual-linear residual surface. -/
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
    intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
      (intervalDomain_regularityLite_of_classicalRegularityData hsol
        (intervalDomain_classicalRegularityData_of_continuityRegularityData
          (IsPaper2ClassicalSolution.T_pos hsol).le
          (h.classicalContinuityRegularity hsol hcross hboot)))
      hsol
      (h.integratedDissipation hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
      (h.lowerAverage hsol hcross hboot)
      (h.upperDataGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Convert to the reusable PDE-level lowerAverage/upperDataGap residual package.
This route is useful if downstream wants the new residual package directly. -/
def to_lowerAverageUpperDataGapResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  classicalRegularity := by
    intro T rho p0 u v hsol hcross hboot
    exact
      intervalDomain_classicalRegularityData_of_continuityRegularityData
        (IsPaper2ClassicalSolution.T_pos hsol).le
        (h.classicalContinuityRegularity hsol hcross hboot)
  integratedDissipation := h.integratedDissipation
  relativeMoserInterpolation := h.relativeMoserInterpolation
  lowerAverage := h.lowerAverage
  upperDataGap := h.upperDataGap
  quantitativeEndpoint := h.quantitativeEndpoint

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals

/-- Sectorial mainline facts with the preferred lowerAverage/upperDataGap Moser
residual surface. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts

def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_integratedStepResiduals

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts

end ShenWork.Paper3
```

Then either:

1. stop there and let callers convert to the existing integrated-step statement
   route via `.to_integratedStepFacts`, or
2. add a statement wrapper analogous to
   `IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData`.

The minimal statement wrapper would be:

```lean
-- Sketch only: place after the IntegratedStep/Stability24/P2Main route.
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K
```

But that exact sketch still uses the integrated-step mainline type.  If you want
the public type name itself to expose lowerAverage/upperDataGap, define the
matching mainline type:

```lean
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

def
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData.toIntegratedStepStability24
    {p : CM2Params} {M0 uBar vLower : ℝ} {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K where
  core := h.core.to_integratedStepFacts
  compactness := h.compactness
  stability24 := h.stability24
```

Then the theorem is a one-line call to the existing integrated-step Stability24
wrapper:

```lean
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    hData.toIntegratedStepStability24
```

## 4. No useful global-classical endpoint thinning in these surfaces

The new reducer

```lean
intervalDomain_classicalRegularityData_of_globalClassicalRegularityData
```

and the energy endpoint theorem

```lean
intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
```

are real and useful, but they need:

```lean
IsPaper2GlobalClassicalSolution intervalDomain params u v
```

The actual Moser callbacks in these Paper3 statement surfaces take only finite
horizon inputs:

```lean
IsPaper2ClassicalSolution intervalDomain p T u v
CrossDiffusionBootstrapEstimate intervalDomain p T rho u v
AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0
```

So there is no honest mechanical way to replace `endpointEnergy` by only
`IntervalDomainInitialPowerEnergyContinuityAtZero` at this layer.  Adding a field
that manufactures a global classical solution from each finite-horizon callback
would not be thinning; it would be a new analytic/global-extension input.

## 5. Optional IntegratedStep compactness-thin patch

If a direct integrated-step caller asks for the same sup-norm compactness surface
as the lower/upper headline route, add a copy of the existing lower/upper thin
wrapper with `core` replaced by
`IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts`.

The mechanical chain is:

```text
IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData
  -- with `ha : 0 < p.a` and shared `initialContinuity`
IntervalDomainPaper3SupNormCompactnessRegularizationData
  -- .toConcrete
IntervalDomainPaper3ConcreteCompactnessRegularizationData
```

This removes the generic `K` compactness field from direct IntegratedStep public
surfaces.  I still rank it below the lowerAverage/upperDataGap wrapper because it
adds another fallback API rather than moving the preferred route closer to the
actual analytic split.

## 6. Genuinely analytic residuals left after the thinning

After adding the lowerAverage/upperDataGap actual-linear wrapper, the remaining
non-mechanical residuals are:

```lean
-- L² seed / closed energy at the beginning of the route
closedEnergyTrace :
  ... → Nonempty (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u)

-- Moser regularity, now in honest continuity form
classicalContinuityRegularity :
  ... → IntervalDomainIntegratedMoserClassicalContinuityRegularityData u T p0

-- Its endpoint subfield remains finite-horizon endpoint continuity, not just atZero
endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0

-- Its gradient subfield is still analytic
IntervalDomainIntegratedMoserGradientEnergyContinuityData.gradientEnergyContinuous

-- Integrated Moser PDE inequality
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0

-- Relative interpolation / mass-gradient route unless separately reduced
RelativeMoserInterpolationBefore intervalDomain u T rho p0

-- Zinan-adjacent frontiers; consume only, do not edit producer files
IntegratedMoserHighExcursionLowerAverageWindowFrontier
IntegratedMoserWindowUpperDataGapFrontier

-- Endpoint route to Prop 2.5
IntervalDomainMoserQuantitativeEndpoint
-- or the existing terminalPointwise package if using the CETerminal route

-- Paper3 non-Moser residuals
IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw
IntervalDomainStandardContinuationGluingData
IntervalDomainPaper3SupNormCompactnessAPosData / concrete compactness
IntervalDomainPaper3Stability24ActualLinearFrontierData
IntervalDomainPaper3Proposition1FromPaper2MainTargetsData
```

No theorem in the current imports turns these into consequences of the actual-linear parameter hypotheses alone.  The only remaining work I would call mechanical is the wrapper layer above.
