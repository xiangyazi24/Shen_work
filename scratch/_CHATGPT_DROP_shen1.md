# Q2651 (shen1) — post-regularity wiring frontier audit

Repo: `xiangyazi24/Shen_work`

Scope: non-Zinan-owned files only.  I am **not** proposing edits to
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

I audited the repo state visible on `main` plus the local-change summary you gave.
The new local names `IntervalDomainIntegratedMoserClassicalRegularityData`,
`IntervalDomainPowerEnergyEndpointContinuity`, and
`intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity` are not
visible on `main` yet, so the ranking below treats your local verification as the
source of truth for those names.

## Bottom line

Best next Codex target: **consumer-side wire-up in `IntervalDomainMoserLadderAtoms.lean`, with a small theorem-level helper layer in `P3MoserActualWiring.lean` only if useful.**

Do **not** spend the next non-Zinan slot on another Paper3 statement wrapper.
The regularity work has made it possible to lower the reusable Moser residual
surface from an opaque `IntegratedMoserFirstCrossingStep` / `IntegratedMoserFirstCrossingLowerUpperFrontiers`
input to the new classical-regularity-data + dissipation + relative + lower-average + upper-data-gap package.
That is the useful wiring layer before any public statement-layer proliferation.

## 0. Grep/check set

```bash
grep -R "IntervalDomainIntegratedMoserClassicalRegularityData\|intervalDomain_regularityLite_of_classicalRegularityData\|intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData\|IntervalDomainPowerEnergyEndpointContinuity\|intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity\|upperDataGap" -n ShenWork/PDE

grep -R "IntegratedMoserFirstCrossingLowerAverageUpperDataGapData\|integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData\|IntegratedMoserWindowUpperDataGapFrontier\|IntegratedMoserHighExcursionLowerAverageWindowFrontier" -n ShenWork/PDE/P3MoserIntegratedClosure.lean

grep -R "IntervalDomainMassLpSmoothingIntegratedStepResiduals\|IntervalDomainMassLpSmoothingWindowFrontierResiduals\|IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals" -n ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean

grep -R "intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms\|intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms" -n ShenWork/PDE/P3MoserActualWiring.lean

grep -R "IntervalDomainPaper2Prop25IntegratedStepFrontierData\|IntervalDomainPaper2Prop25LowerUpperFrontierData\|toIntegratedStepFrontierData" -n ShenWork/Paper2/IntervalDomainStatementAssembly.lean
```

Candidate imports for any new non-Zinan consumer-side file, or for a new section added to `P3MoserActualWiring.lean` / `IntervalDomainMoserLadderAtoms.lean`:

```lean
import ShenWork.PDE.P3MoserRegularityProducer
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.IntervalDomainMoserLadderAtoms

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open scoped Interval
```

## 1. Pure wire-up now possible from existing code

### 1. Add a regularity-aware residual package in `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`

This is the best next target.

Existing reusable consumers already in that file:

- `IntervalDomainMassLpSmoothingIntegratedStepResiduals`
- `IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21`
- `IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25`
- `IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals`
- `IntervalDomainMassLpSmoothingWindowFrontierResiduals.to_integratedStepResiduals`
- `IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.to_integratedStepResiduals`

The missing layer after your regularity wiring is a package that consumes the
preferred analytic split directly, then converts to
`IntervalDomainMassLpSmoothingIntegratedStepResiduals`.

Suggested name to add:

```lean
import ShenWork.PDE.P3MoserRegularityProducer
import ShenWork.PDE.IntervalDomainMoserLadderAtoms

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Interval

-- Candidate names only; fill fields to match the new local regularity-data API.
-- structure IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals
-- def IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_integratedStepResiduals
-- def IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.to_routeResiduals
-- def IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals.aprioriBound
```

The conversion should build the `integratedStep` field by calling your new
`P3MoserRegularityProducer` shortcut, whose generic endpoint is already the
existing theorem
`integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData` through
`IntegratedMoserFirstCrossingLowerAverageUpperDataGapData`.

Why this is ranked first: it immediately feeds the Paper3 a-priori route without
touching statement wrappers.  Existing downstream users of
`IntervalDomainMassLpSmoothingIntegratedStepResiduals.aprioriBound` and
`.to_routeResiduals` then get the thinner Moser surface automatically.

### 2. Add theorem-level helpers in `ShenWork/PDE/P3MoserActualWiring.lean`

Add these only if you want Paper2/Paper3 theorem consumers to use the new data
without first building a residual record in `IntervalDomainMoserLadderAtoms.lean`.

Existing analogues:

- `intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms`
- `intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms`

Candidate names:

```lean
import ShenWork.PDE.P3MoserRegularityProducer
import ShenWork.PDE.P3MoserActualWiring

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open scoped Interval

-- Candidate names:
-- theorem intervalDomain_allLpBoundFromBootstrap_of_actual_lowerAverageUpperDataGap_atoms
-- theorem intervalDomain_endpointBoundFromLp_of_actual_lowerAverageUpperDataGap_atoms
-- theorem intervalDomain_cor21_and_prop25_of_actual_lowerAverageUpperDataGap_atoms
```

Implementation shape: define the local `hstep` expected by the existing
`..._actual_integrated_step_atoms` theorems, using the new classical-regularity
producer plus the preferred lower-average / upper-data-gap shortcut.

This is pure assembly if the local shortcut already returns
`IntegratedMoserFirstCrossingStep intervalDomain u T rho p0`.

### 3. In `ShenWork/PDE/P3MoserRegularityProducer.lean`, avoid duplicating your new shortcut

You said the current local change already added:

- `IntervalDomainIntegratedMoserClassicalRegularityData`
- `intervalDomain_regularityLite_of_classicalRegularityData`
- `intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData`
- preferred lowerAverage/upperDataGap first-crossing-step shortcuts

So Codex should only grep/check this file after the build lands.  Do not add a
parallel epsilon-gap version unless a caller still supplies the older
`IntegratedMoserWindowUpperGapEpsilonFrontier`.  The generic compatibility path
already exists:

- `IntegratedMoserFirstCrossingLowerAverageEpsilonData.toUpperDataGapData`
- `integratedMoserWindowUpperDataGapFrontier_of_epsilonGap`
- `integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap`

### 4. Paper2 statement wrappers are already sufficient

`ShenWork/Paper2/IntervalDomainStatementAssembly.lean` already has the statement
surface that matters:

- `IntervalDomainPaper2Prop25IntegratedStepFrontierData`
- `IntervalDomainPaper2Prop25LowerUpperFrontierData`
- `IntervalDomainPaper2Prop25LowerUpperFrontierData.toIntegratedStepFrontierData`
- `intervalDomainPaper2_Proposition_2_5_of_lowerUpperFrontierData`
- `intervalDomainPaper2_Corollary_2_1_of_lowerUpperFrontierData`
- `intervalDomainPaper2_bootstrapEstimateTargets_of_thinLowerUpperFrontierData`

A new Paper2 statement wrapper that mentions
`IntervalDomainIntegratedMoserClassicalRegularityData` directly would be API
bloat unless an actual caller is holding exactly that data and cannot conveniently
pass through the PDE-level residual package.

## 2. Honest analytic residuals still not derivable from `IsPaper2ClassicalSolution` alone

### 1. Endpoint / closed-time energy data

Your new `intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity`
correctly turns open-interior continuity plus endpoint information into
closed-time continuity.  The remaining analytic input is the endpoint piece,
represented in the local change by `IntervalDomainPowerEnergyEndpointContinuity`
and the `endpointEnergy` field of `IntervalDomainIntegratedMoserClassicalRegularityData`.

Do not claim this follows from the current `IsPaper2ClassicalSolution` interface alone: the existing classical regularity gives strong interior information, but the Moser regularity package needs every `p ≥ p0` on `[0,T]`, including endpoint behavior.

### 2. Gradient-energy time integrability

Still a real regularity/energy frontier:

- `IntegratedMoserFirstCrossingRegularity.gradientTimeIntegrable`
- local `IntervalDomainIntegratedMoserClassicalRegularityData.gradientTimeIntegrable`

This is not supplied by the existing classical solution record alone.  It needs
an actual gradient-energy estimate or an added regularity theorem strong enough
to prove the time-integrability of
`integratedMoserGradientEnergy intervalDomain u p` for every ladder exponent.

### 3. Integrated Moser dissipation

Still analytic, not a consequence of the old abstract route:

- `IntegratedMoserDissipationDropBefore`
- `integratedMoserDissipationDropBefore_of_integrated_energy`

The existing theorem is a packaging theorem from the exact integrated energy
inequality, not a derivation from `IsPaper2ClassicalSolution` alone.  Also do not
route this through the old pointwise/nonnegative-B shape unless that is the
chosen fallback atom; the integrated route is the faithful one for the current
first-crossing plan.

### 4. Relative Moser interpolation / mass-gradient comparison

`RelativeMoserInterpolationBefore` is still an atom unless supplied by the
mass-gradient route:

- `relativeMoserInterpolationBefore_of_massGradient`
- `moserClosure_relativeInterpolationBefore_of_mass_gradient_estimate`
- `LpMassGradientInterpolationEstimate`
- `MoserMassPowerToCurrentLpLowerOrder`

The bridge exists; the mass-gradient inputs are the analytic residuals.

### 5. Lower-average and upper-data-gap production

The preferred split is now named, but producing it is still the high-excursion
analytic step:

- `IntegratedMoserHighExcursionLowerAverageWindowFrontier`
- `IntegratedMoserWindowUpperDataGapFrontier`
- `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData`
- `integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData`

Because of the ownership constraint, non-Zinan Codex should **consume** these
frontiers but should not implement high-excursion / last-exit / threshold-plan
logic in `P3MoserHighExcursionProducer.lean` or
`P3MoserThresholdPlanProducer.lean`.

### 6. Quantitative endpoint / terminal endpoint

Unaffected by the regularity wiring.  Prop 2.5 routes still require one of:

- `IntervalDomainMoserQuantitativeEndpoint`
- terminal pointwise endpoint data in the existing terminal-endpoint wrappers

This is not the next best non-Zinan attack unless the caller is explicitly trying
to remove the endpoint atom from a statement package.

## 3. Statement-layer wrappers that should not be added unless callers demand them

### 1. Do not add Paper3 `...ClassicalRegularityLowerAverageUpperDataGap...` statement wrappers yet

Avoid new public wrappers in
`ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` that directly
mention `IntervalDomainIntegratedMoserClassicalRegularityData` unless there is a
real caller blocked at that exact surface.

The existing Paper3 layers already cover the important public surfaces:

- generic-K integrated-step route
- lower/upper split route
- thin actual-linear P2-main route
- Stability24 actual-linear thinning

Adding a regularity-data-named Paper3 statement wrapper now would mostly rename
the same frontier package one level higher.

### 2. Do not add another IntegratedStep sup-norm thin route by default

The previous generic-K IntegratedStep Stability24 route is enough as a fallback.
The preferred route remains the lower/upper or lowerAverage/upperDataGap split,
because it is closer to the real producer decomposition.

### 3. Do not add `Fact` wrappers automatically

Only add `...Fact` wrappers after a caller actually uses typeclass-style
frontier discovery.  The current files already have many instance-facing
compatibility wrappers; adding them speculatively creates noise.

### 4. Do not add more epsilon-gap public surfaces

The older all-witness epsilon-gap interface is stronger than the preferred
upper-data-aware interface.  Keep using:

- `IntegratedMoserWindowUpperDataGapFrontier`
- `integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap`

Use `integratedMoserWindowUpperDataGapFrontier_of_epsilonGap` only as a
compatibility adapter for existing epsilon-gap callers.

## Ranked next actions for Codex

1. **`ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`** — add a new
   `IntervalDomainMassLpSmoothingLowerAverageUpperDataGapResiduals`-style
   package and conversions to `IntervalDomainMassLpSmoothingIntegratedStepResiduals`.
   This gives Paper3/PDE consumers the new regularity-aware Moser route without
   statement bloat.

2. **`ShenWork/PDE/P3MoserActualWiring.lean`** — add theorem-level Corollary 2.1
   / Proposition 2.5 helpers that build `IntegratedMoserFirstCrossingStep` from
   the new classical-regularity data plus preferred lowerAverage/upperDataGap
   frontiers, then call the existing `...actual_integrated_step_atoms` theorems.

3. **`ShenWork/PDE/P3MoserRegularityProducer.lean`** — only grep/verify the new
   shortcut names and add missing `#print axioms`; do not add parallel old
   epsilon-gap surfaces if the upperDataGap route is already present.

4. **No statement-layer additions** in `Paper2/IntervalDomainStatementAssembly.lean`
   or `Paper3/IntervalDomainActualLinearStatementAssembly.lean` unless a direct
   caller demands them.  The current statement wrappers already consume
   integrated-step and lower/upper split data; the useful missing layer is below
   them.
