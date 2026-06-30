# Q2625 shen2: Paper3 Theorem 2.2 / mainline wiring audit

Repo target: `xiangyazi24/Shen_work`, default branch `main`.

This is an audit/design note for Paper3 statement/sectorial/stability wiring. It intentionally avoids high-excursion producer files and `IntervalDomainMoserLadderAtoms`.

## Short recommendation

The best next non-vacuous Lean wiring task is **not** another alias for `IntervalDomainSectorialTheorem22LocalFrontiers` or `IntervalDomainSectorialMainlineCoreExistence`. Those still expose the same sectorial-local inputs:

```lean
IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
∀ uStar, ∀ delta > 0, SmallDataGlobalExistence intervalDomain p uStar delta
∀ uStar, ∀ delta > 0, MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta
```

Instead, add a **linear-raw Theorem 2.2 sectorial endpoint** that consumes the already-existing raw branch interfaces:

```lean
LinearStabilityInstabilityNonminimalRaw
LinearStabilityInstabilityMinimalRaw
```

and produces the concrete sectorial Theorem 2.2 target. Then add a thin sectorial mainline package that combines this Theorem 2.2 raw-local-stability frontier with the existing Theorem 2.1 persistence package.

This genuinely reduces assumptions at the Paper3 headline / mainline layer because callers no longer need to carry the sectorial-orbit and small-data Cauchy fields when they already have the `LinearStabilityInstability*Raw` branch facts. It is **not** a proof of those branch facts; those remain real PDE frontiers.

## Current audited shape

### `IntervalDomainStabilityChain.lean`

This file already has a strong generic theorem:

```lean
intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw
```

which consumes:

```lean
LinearStabilityInstabilityNonminimalRaw intervalDomain p
  unitIntervalNeumannSpectrum N.c1Distance C.chiCritical

LinearStabilityInstabilityMinimalRaw intervalDomain p
  unitIntervalNeumannSpectrum N.c1Distance C.chiCritical
```

and assembles:

```lean
Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C
```

The unstable halves are discharged from the audited critical-spectrum identity. This is real wiring, not a restatement of small-data existence.

The same file also already has sectorial/spectral-semigroup routes such as:

```lean
intervalDomain_Theorem_2_2_for_concreteStabilityNorms_spectralSemigroup_frontiers
intervalDomain_Theorem_2_2_for_concrete_constants_branch_frontiers_via_linearRaw
```

Those are useful, but the main sectorial package still exports Theorem 2.2 through the `IntervalDomainSectorialTheorem22Existence` / `CoreExistence` route, whose fields include the raw orbit comparison and small-data global existence.

### `IntervalDomainSectorial.lean`

The concrete local-frontier type is:

```lean
def IntervalDomainSectorialTheorem22LocalFrontiers
    (p : CM2Params) : Prop :=
  ∃ sigma pNorm : ℝ,
    1 / 2 < sigma ∧ sigma < 1 ∧ 1 < pNorm ∧
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p ∧
    (∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta) ∧
    (∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta)
```

The Paper2-style theorem package is:

```lean
structure IntervalDomainSectorialTheorem22Existence
    (p : CM2Params) where
  sigma : ℝ
  pNorm : ℝ
  sigma_low : 1 / 2 < sigma
  sigma_high : sigma < 1
  pNorm_gt_one : 1 < pNorm
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  smallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta
  massConstrainedSmallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta
```

The canonical core package fixes `sigma = 3/4`, `pNorm = 2`, but keeps the same analytic content:

```lean
structure IntervalDomainSectorialMainlineCoreExistence
    (p : CM2Params) (uBar : ℝ) where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  smallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta
  massConstrainedSmallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta
  persistencePart1 : UniformPersistencePart1Raw intervalDomain p
  persistencePart2 : UniformPersistencePart2Raw intervalDomain p
  persistencePart3 : UniformPersistencePart3Raw intervalDomain p
  persistencePart4 :
    UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1
```

This is already an honest sectorial frontier, but it is not the thinnest Theorem 2.2 statement layer if the `LinearStabilityInstability*Raw` branches have already been proved elsewhere.

### `IntervalDomainStatementAssembly.lean`

The current mainline data are:

```lean
structure IntervalDomainPaper3MainlineFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainSectorialMainlineCoreExistence p uBar
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)
```

So even if a caller already has Theorem 2.2 raw branch data, the current mainline route still asks for `core`, hence for orbit comparison and both small-data existence branches.

### `Statements.lean` / `StatementAssembly.lean`

The raw branch interface is already present and meaningful:

```lean
def LinearStabilityInstabilityNonminimalRaw ... : Prop := ...
def LinearStabilityInstabilityMinimalRaw ... : Prop := ...
```

These are not cosmetic: each includes the linearly stable conclusion plus the actual sup-small local-exponential global solution statement. The generic `StatementAssembly.lean` wrapper:

```lean
paper3_Theorem_2_2_of_branchData
```

confirms that Theorem 2.2 is naturally branch-data driven. The interval files already exploit this in `IntervalDomainStabilityChain.lean`; the missing cleanup is to expose the same branch-data reduced route as a sectorial/mainline entry point.

## Proposed next task

### File target

Primary file:

```text
ShenWork/Paper3/IntervalDomainSectorial.lean
```

Optional follow-up file:

```text
ShenWork/Paper3/IntervalDomainStatementAssembly.lean
```

Do **not** touch:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

## Source patch shape: sectorial linear-raw endpoint

Add this near the existing `IntervalDomainSectorialTheorem22Existence` / `IntervalDomainSectorialMainlineExistence` block, after `IntervalDomainSectorialTheorem21Persistence` is defined and before the core-existence section.

Standalone test imports:

```lean
import ShenWork.Paper3.IntervalDomainSectorial

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section
```

Code shape:

```lean
/-- Theorem 2.2 local-stability data already reduced to the raw branch
interface, with concrete sectorial interval norms and constants.

This is intentionally *not* the same as
`IntervalDomainSectorialTheorem22Existence`: it does not carry the nonlinear
orbit comparison or small-data Cauchy fields.  Those are one possible way to
produce the raw branch facts, but they are not needed once the raw branch facts
are supplied directly. -/
structure IntervalDomainSectorialTheorem22LinearRawExistence
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  nonminimal :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  minimal :
    LinearStabilityInstabilityMinimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
```

Then add the theorem:

```lean
/-- Concrete sectorial interval-domain Theorem 2.2 from the already-reduced raw
linear-stability/instability branch package.

The stable/local-exponential halves are exactly the two raw fields.  The
unstable halves are discharged from the concrete unit-interval critical-spectrum
identity. -/
theorem intervalDomain_Theorem_2_2_sectorialMainline_of_linearRawExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hlin : IntervalDomainSectorialTheorem22LinearRawExistence
      p M0 uBar vLower) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) := by
  let C := intervalDomainSectorialPaper3Constants p M0 uBar vLower
  have hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C :=
    intervalDomainSectorialPaper3Constants_usesCriticalSpectrum p M0 uBar vLower
  refine Theorem_2_2.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    simpa [C] using hlin.nonminimal ha hb
  · intro ha hb
    dsimp
    intro hχcrit
    exact hC.positiveEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hχcrit
  · intro ha hb uStar huStar
    simpa [C] using hlin.minimal ha hb uStar huStar
  · intro _ha _hb uStar huStar
    dsimp
    intro hχcrit
    exact hC.minimalEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hχcrit
```

Why this should compile: it is the same proof skeleton already used in `IntervalDomainStabilityChain.intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw`, but specialized to `intervalDomainSectorialStabilityNorms` and `intervalDomainSectorialPaper3Constants`. `IntervalDomainSectorial.lean` already imports `Statements`, has the concrete constants theorem, and has the spectrum witness.

If Lean resists the `simpa [C]` lines because of the local `let C`, use the direct terms instead:

```lean
exact hlin.nonminimal ha hb
```

and

```lean
exact hlin.minimal ha hb uStar huStar
```

The raw fields are already stated with the exact same `chiCritical` function.

## Source patch shape: mainline package using raw Theorem 2.2

Add a mainline package that combines this reduced Theorem 2.2 frontier with the existing Theorem 2.1 persistence package:

```lean
/-- Sectorial mainline package whose Theorem 2.2 component is supplied at the
raw branch level, not via the sectorial-orbit/small-data local-frontier route.

This is useful when local exponential stability has already been proved in the
`LinearStabilityInstability*Raw` form.  It still requires the genuine Theorem
2.1 persistence package. -/
structure IntervalDomainSectorialMainlineLinearRawExistence
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  theorem22 :
    IntervalDomainSectorialTheorem22LinearRawExistence p M0 uBar vLower
  persistence : IntervalDomainSectorialTheorem21Persistence p uBar
```

Then:

```lean
/-- Concrete interval-domain Theorem 2.1/2.2 endpoint from the split raw-local
Theorem 2.2 package and the existing persistence package. -/
theorem intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_linearRawExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (h : IntervalDomainSectorialMainlineLinearRawExistence
      p M0 uBar vLower) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) ∧
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  ⟨intervalDomain_Theorem_2_2_sectorialMainline_of_linearRawExistence
      p M0 uBar vLower h.theorem22,
    intervalDomain_Theorem_2_1_sectorialMainline_of_persistence
      p M0 uBar vLower h.persistence⟩
```

And the literal target handoff:

```lean
/-- The literal sectorial Theorem 2.1/2.2 target from the raw-local Theorem 2.2
mainline package. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_linearRawExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (h : IntervalDomainSectorialMainlineLinearRawExistence
      p M0 uBar vLower) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_linearRawExistence
    p M0 uBar vLower h
```

Optional fact wrapper:

```lean
/-- Instance-facing raw-local sectorial mainline endpoint. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_linearRawExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [h : Fact (IntervalDomainSectorialMainlineLinearRawExistence
      p M0 uBar vLower)] :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_linearRawExistence
    p M0 uBar vLower h.out
```

This is the main non-vacuous task. It creates a branch-data based route that bypasses the sectorial-local existence fields when those have already been discharged into raw local-stability facts.

## Optional statement-assembly follow-up

Once the sectorial package above exists, add a statement-level data record in:

```text
ShenWork/Paper3/IntervalDomainStatementAssembly.lean
```

Do this only if the user-facing mainline umbrella should expose the split local-stability route directly.

```lean
import ShenWork.Paper3.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section
```

Suggested names:

```lean
/-- Concrete interval-domain Paper3 mainline frontiers in which Theorem 2.2 is
supplied through the raw linear-stability/instability branch package rather than
through `IntervalDomainSectorialMainlineCoreExistence`.

This does not remove compactness or Theorem 2.3--2.5 frontiers.  It only prevents
the Theorem 2.2 headline from forcing callers through the sectorial-orbit and
small-data-global fields when they already have raw local-stability branches. -/
structure IntervalDomainPaper3MainlineLinearRawFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  localMainline :
    IntervalDomainSectorialMainlineLinearRawExistence p M0 uBar vLower
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)
```

Do **not** try to force this into the existing `IntervalDomainPaper3MainlineTargets` without thought. That target currently contains `IntervalDomainPaper3CoreStatementTargets`, which is defined in terms of the canonical core existence package and includes the sectorial Theorem 2.1/2.2 target as a component. A split raw-local route may deserve a sibling target rather than shoehorning through `core`.

A safe sibling target would be:

```lean
/-- Sibling mainline target for the raw-local Theorem 2.2 route. -/
def IntervalDomainPaper3MainlineLinearRawTargets
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop :=
  Lemma_3_1 intervalDomain p ∧
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms ∧
    UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm ∧
    IntervalDomainStabilityChainTheorem21Target p M0 uBar vLower ∧
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower ∧
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower ∧
    IntervalDomainPaper3CompactnessRegularizationTargets p K
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) ∧
    IntervalDomainPaper3ConcreteStability23To25Targets p M0 uBar vLower
```

Then assemble it by using:

```lean
intervalDomain_sectorialMainline_unconditionalTarget_of_linearRawExistence
intervalDomain_paper3_Theorem_2_1_partTargets_of_persistence
intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
```

But I would do this only after adding the sectorial-level raw-local endpoint. The sectorial patch is the smaller, cleaner, compile-safer reduction.

## What this task reduces

Compared with `IntervalDomainSectorialMainlineCoreExistence`, the raw-local route removes these fields from the Theorem 2.2/mainline assumption surface:

```lean
IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
∀ uStar, ∀ delta > 0,
  SmallDataGlobalExistence intervalDomain p uStar delta
∀ uStar, ∀ delta > 0,
  MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta
```

It replaces them with:

```lean
LinearStabilityInstabilityNonminimalRaw intervalDomain p ...
LinearStabilityInstabilityMinimalRaw intervalDomain p ...
```

That is a real reduction when the caller has local exponential stability already proved in the raw branch form. It avoids re-demanding the sectorial proof ingredients.

## What remains real PDE frontier

For the raw-local sectorial route:

```lean
LinearStabilityInstabilityNonminimalRaw ...
LinearStabilityInstabilityMinimalRaw ...
```

remain genuine PDE/local-stability frontiers. They include global solution existence from small sup-neighborhood data, initial trace, and exponential `C¹` convergence. They are not proved by algebraic spectral formulas alone.

For the combined Theorem 2.1/2.2 mainline:

```lean
UniformPersistencePart1Raw intervalDomain p
UniformPersistencePart2Raw intervalDomain p
UniformPersistencePart3Raw intervalDomain p
UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1
```

remain genuine persistence frontiers.

For the full `IntervalDomainPaper3MainlineFrontierData` layer, the following remain outside this task:

```lean
IntervalDomainPaper3ConcreteCompactnessRegularizationData
IntervalDomainPaper3Stability23To25FrontierData
```

Those contain compactness, initial continuity, minimal upper-bound, resolvent, and Theorem 2.3--2.5 global/asymptotic/exponential frontiers. They are not reduced by a Theorem 2.2 wiring task.

## What not to do

Do not add a new structure that is just:

```lean
structure Something where
  local : IntervalDomainSectorialTheorem22LocalFrontiers p
```

or a version that fixes `sigma = 3/4` but still asks for:

```lean
spectralSemigroupOrbitBound
smallDataGlobal
massConstrainedSmallDataGlobal
```

That would be a name-only reshuffle of the existing `CoreExistence` assumptions.

Do not claim that `IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw` implies small-data global existence. The orbit comparison field already assumes global solutions in its conclusion; it does not construct them.

Do not push this task into Zinan-owned files:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

Do not conflate Theorem 2.2 local stability with Theorem 2.1 persistence. A reduced Theorem 2.2 route should not carry persistence fields unless the target is explicitly the combined Theorem 2.1/2.2 mainline.

## Bottom line

The best next Codex-sized wiring commit is:

```text
File: ShenWork/Paper3/IntervalDomainSectorial.lean
Add:
  IntervalDomainSectorialTheorem22LinearRawExistence
  intervalDomain_Theorem_2_2_sectorialMainline_of_linearRawExistence
  IntervalDomainSectorialMainlineLinearRawExistence
  intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_linearRawExistence
  intervalDomain_sectorialMainline_unconditionalTarget_of_linearRawExistence
```

This is the first non-vacuous assumption reduction because it lets the Paper3 Theorem 2.2 headline consume the already-existing `LinearStabilityInstability*Raw` branch facts directly, instead of re-carrying the sectorial-orbit plus ordinary/mass-constrained small-data global existence fields through `IntervalDomainSectorialMainlineCoreExistence`.
