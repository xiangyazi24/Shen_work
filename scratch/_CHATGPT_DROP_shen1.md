# Q2636 shen1 — Paper3 actual-linear statement-route audit and next reductions

Repo: `xiangyazi24/Shen_work`

Branch inspected: current `main` after the committed changes mentioned in the prompt.

Files inspected:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
ShenWork/Paper3/IntervalDomainStatementAssembly.lean
ShenWork/Paper3/IntervalDomainSectorial.lean
ShenWork/Paper3/IntervalDomainSectorialNonlinearBridges.lean
ShenWork/Paper3/IntervalDomainPersistenceActualLinearSectorial.lean
ShenWork/PDE/P3MoserRegularityProducer.lean
ShenWork/PDE/P3MoserActualWiring.lean
ShenWork/PDE/P3MoserLemmaDischarge.lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

I did **not** rely on editing `ShenWork/PDE/P3MoserHighExcursionProducer.lean` or `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

## Executive summary

The next best non-conflicting reductions are in the **actual-linear statement layer**, not in high-excursion/Moser producer files.

Top two reductions:

1. **Actual-linear stability 2.3/2.5 vacuity reduction.**  In the actual-linear-small route, the final theorem assumes `0 < p.χ₀` and `0 < p.a`.  Therefore the `χ₀ ≤ 0` Theorem 2.3 branches and the minimal `a = 0, b = 0` Theorem 2.5 branches inside `IntervalDomainPaper3Stability23To25FrontierData` are vacuous.  A new actual-linear stability data structure should carry only the genuinely relevant Theorem 2.4 fields `global24` and `exp24`, then fill the other six fields by contradiction.  This removes six explicit frontier fields without new math.

2. **Actual-linear compactness/core thinning.**  In the current actual-linear raw-linear route, `IntervalDomainInitialContinuityRaw p` is carried twice: once in `IntervalDomainPaper3CoreStatementActualLinear22Data.initialContinuity`, and once inside `IntervalDomainPaper3ConcreteCompactnessRegularizationData.initialContinuity`.  Also, if the compactness package is the already-defined `intervalDomainSupNormCompactnessData`, the `upperEq` field is definitional; and under `0 < p.a`, the compactness `minimalUpper` field is vacuous.  A thin actual-linear mainline data structure can carry one shared `initialContinuity`, only the real compactness/resolvent fields, and the two raw linear Theorem 2.2 branches.

The uncommitted `P3MoserRegularityProducer` lite change is also the right reduction: `powerTimeIntegrable` is derivable from `energyContinuous + 0 ≤ T`; keep `energyContinuous` and `gradientTimeIntegrable` explicit.  That is orthogonal to high-excursion ownership.

The uncommitted `IntervalDomainSectorial.lean` raw-linear sibling route is also the right direction: it bypasses `IntervalDomainSectorialMainlineCoreExistence` for the Theorem 2.1/2.2 target when raw linear-stability branches are supplied directly.  That is pure assembly plus already-produced actual-linear persistence; it should not carry the nonlinear orbit/small-data fields needed only for the sectorial H3.1 route.

## Route map: what the current actual-linear statement route is doing

The current preferred actual-linear statement endpoint in `IntervalDomainActualLinearStatementAssembly.lean` is:

```lean
IntervalDomainPaper3StatementActualLinear22P2MainData
intervalDomain_paper3_statementTargets_of_actualLinear22P2MainData
```

It has:

```lean
structure IntervalDomainPaper3StatementActualLinear22P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22FrontierData
      p M0 uBar vLower K
```

The `propositions` branch routes Paper3 Proposition 1.3/1.4 through Paper2 main theorem targets, but it deliberately still carries the independent Paper3 Proposition 1.2 residual:

```lean
structure IntervalDomainPaper3Proposition1FromPaper2MainTargetsData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
```

The `mainline` branch is:

```lean
structure IntervalDomainPaper3MainlineActualLinear22FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainPaper3CoreStatementActualLinear22Data
    p M0 uBar vLower
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)
```

and the actual-linear core is:

```lean
structure IntervalDomainPaper3CoreStatementActualLinear22Data
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  theorem22Nonminimal :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  theorem22Minimal :
    LinearStabilityInstabilityMinimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
```

`to_linear22Data` fills the Theorem 2.1 persistence field internally by calling:

```lean
intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
```

from `IntervalDomainPersistenceActualLinearSectorial.lean`.

## Classification by structure / field

### `IntervalDomainPaper3StatementActualLinear22P2MainData`

| Field | Classification | Notes |
|---|---|---|
| `propositions.negativeBound` | real analytic frontier / remains explicit | Paper2 main targets do not imply Paper3 Proposition 1.2 negative-sensitivity eventual bound. This is explicitly documented in `IntervalDomainStatementAssembly.lean`. |
| `propositions.paper2Main` | already external target / can be wired if caller has it | This is not produced by the actual-linear Paper3 route; it should be supplied from the Paper2 main theorem route. |
| `mainline` | mixed | See below. |

No honest reduction removes `negativeBound` from this route unless a separate negative-sensitivity global/eventual-bound theorem is supplied.

### `IntervalDomainPaper3CoreStatementActualLinear22Data`

| Field | Classification | Notes |
|---|---|---|
| `initialContinuity` | real analytic frontier, but duplicated | Needed for Lemma 3.3. No producer found in the repo. It is also carried in compactness data; share it once. |
| `theorem22Nonminimal` | real analytic frontier | No existing producer found for the raw nonminimal linear-stability/instability branch. |
| `theorem22Minimal` | real analytic frontier | No existing producer found for the raw minimal linear-stability/instability branch. |
| persistence | already produced internally | `IntervalDomainPaper3CoreStatementActualLinear22Data.to_linear22Data` fills it using `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`. |

### `IntervalDomainPaper3ConcreteCompactnessRegularizationData`

| Field | Classification | Notes |
|---|---|---|
| `upperEq` | pure redundant wrapper when using `intervalDomainSupNormCompactnessData` | `IntervalDomainPaper3SupNormCompactnessRegularizationData.toConcrete` already fills this definitionally. |
| `compact` | real analytic frontier | `TimeTranslateCompactnessRaw` remains a compactness theorem, not produced here. |
| `initialContinuity` | real analytic frontier, but duplicated | Same field as `core.initialContinuity`; share it once. |
| `minimalUpper` | vacuous in actual-linear-small route | Actual-linear theorem wrapper assumes `0 < p.a`, while this branch starts with `p.a = 0`. Fill by contradiction. |
| `resolvent` | real analytic frontier | `NeumannResolventGradientBoundExistsRaw` remains explicit. |

### `IntervalDomainPaper3Stability23To25FrontierData`

| Field | Classification under actual-linear-small hypotheses | Notes |
|---|---|---|
| `globalNonminimal23` | vacuous | Starts with `p.χ₀ ≤ 0`, contradicts wrapper hypothesis `0 < p.χ₀`. |
| `globalMinimal23` | vacuous | Same contradiction via `p.χ₀ ≤ 0`; also minimal branch. |
| `expNonminimal23` | vacuous | Same contradiction via `p.χ₀ ≤ 0`. |
| `expMinimal23` | vacuous | Same contradiction via `p.χ₀ ≤ 0`; also minimal branch. |
| `global24` | real analytic frontier | This is the positive-sensitivity nonminimal global-stability branch. |
| `exp24` | real analytic frontier | This is the positive-sensitivity nonminimal exponential upgrade branch. |
| `global25` | vacuous | Starts with `p.a = 0`, contradicts wrapper hypothesis `0 < p.a`. |
| `exp25` | vacuous | Same `p.a = 0` contradiction. |

This is the largest safe reduction currently available in the statement layer.

### Actual-linear persistence package

Already produced in repo:

```lean
intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
```

It fills:

```lean
IntervalDomainSectorialTheorem21Persistence p uBar
```

from:

```lean
0 < p.a, 0 < p.b, 0 < p.χ₀,
p.m = 1, 1 ≤ p.β,
p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))
```

The component reductions are also already in the repo:

```lean
intervalDomain_uniformPersistencePart1Raw_of_part2_smallLinear
intervalDomain_uniformPersistencePart2Raw_proven
intervalDomain_uniformPersistencePart3Raw_vacuous_of_m_eq_one
intervalDomain_uniformPersistencePart4Raw_vacuous_of_a_pos
```

### Sectorial core vs raw-linear sibling route

`IntervalDomainSectorialMainlineCoreExistence` is still the right package for the H3.1 sectorial path.  But for the actual-linear raw Theorem 2.2 route, it is overkill because raw linear-stability branches directly produce Theorem 2.2.

The uncommitted sibling route in `IntervalDomainSectorial.lean` is therefore a good non-conflicting reduction.  It should keep only:

```lean
persistence : IntervalDomainSectorialTheorem21Persistence p uBar

theorem22Nonminimal : LinearStabilityInstabilityNonminimalRaw ...
theorem22Minimal : LinearStabilityInstabilityMinimalRaw ...
```

and assemble:

```lean
IntervalDomainSectorialTheorem21And22UnconditionalTarget p M0 uBar vLower
```

without `spectralSemigroupOrbitBound`, `smallDataGlobal`, or `massConstrainedSmallDataGlobal`.

Classification:

* raw linear Theorem 2.2 branches: real analytic frontier;
* persistence: already produced by actual-linear small route;
* sectorial core existence fields: pure redundant for this raw-linear Theorem 2.2 path, but still relevant to the separate H3.1/local-exponential route.

### Moser / mass-Lp smoothing surfaces in `IntervalDomainActualLinearStatementAssembly.lean`

| Structure / field | Classification | Notes |
|---|---|---|
| `IntervalDomainMassLpSmoothingMoserActualLinearSmallBoundednessCore` | real parameter-side frontier | `alphaAbsorption` and `gammaDimension` remain real parameter inequalities; `to_boundednessHyp` fills the rest from `hb` and existing parameter positivity. |
| `closedEnergyTrace` | real analytic frontier | Converted by `P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData`. Good reduction from old L² seed field. |
| `rawMoserDrop` | real analytic frontier | Converted by `moserDissipationDropBeforeNonnegB_of_raw_drop`. |
| `relativeMassGradient` | real analytic frontier | Converted by `P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient`. |
| `terminalPointwise` | real analytic frontier | Converted by `intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl`. This is a good endpoint simplification. |
| `integratedStep` | real analytic frontier / atom | Good explicit atom if avoiding high-excursion/threshold producer ownership. |
| `lowerUpperFrontiers` | do not touch under current ownership | It routes through `P3MoserIntegratedClosure`, but producing it belongs to the high-excursion worker. |

### `P3MoserRegularityProducer.lean` lite change

This is a good reduction and should be committed independently:

* `energyContinuous`: real frontier, keep.
* `gradientTimeIntegrable`: real frontier, keep.
* `powerTimeIntegrable`: small wiring from `energyContinuous + 0 ≤ T`, remove from explicit data.
* `initialPowerBound`: already algebraic via `max integral 0`.

Suggested names from the local work are good:

```lean
IntervalDomainIntegratedMoserRegularityFrontierDataLite
intervalDomain_powerTimeIntegrable_of_energyContinuous
intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
intervalDomain_lowerAverageEpsilonData_of_classical_lite
intervalDomain_firstCrossingStep_of_classical_and_frontiers_lite
```

This does not rely on high-excursion producer files.

## Top reduction 1: actual-linear stability 2.3/2.5 vacuity

Add this in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` or, if preferred for general reuse, in `IntervalDomainStatementAssembly.lean`.  Since it uses actual-linear-small hypotheses, I would put it in `IntervalDomainActualLinearStatementAssembly.lean`.

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- In the actual-linear-small route, the only non-vacuous Theorem 2.3--2.5
stability fields are the positive-sensitivity nonminimal Theorem 2.4 branches.
The `χ₀ ≤ 0` Theorem 2.3 branches contradict `0 < χ₀`, and the minimal
Theorem 2.5 branches contradict `0 < a`. -/
structure IntervalDomainPaper3Stability24ActualLinearFrontierData
    (p : CM2Params) (C : Paper3Constants intervalDomain p) : Prop where
  global24 :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
          GloballyAsymptoticallyStableNonminimal intervalDomain p
            eq.1 eq.2
  exp24 :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain
                  intervalDomainStabilityNorms u v eq.1 eq.2 A rate

/-- Fill the full stability 2.3--2.5 frontier from the non-vacuous Theorem 2.4
branches in the actual-linear-small regime. -/
def IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h : IntervalDomainPaper3Stability24ActualLinearFrontierData p C)
    (ha_pos : 0 < p.a) (hchi_pos : 0 < p.χ₀) :
    IntervalDomainPaper3Stability23To25FrontierData p C where
  globalNonminimal23 := by
    intro hchi_nonpos _hm ha hb
    exfalso
    linarith
  globalMinimal23 := by
    intro hchi_nonpos _hm _ha0 _hb0 uStar huStar
    exfalso
    linarith
  expNonminimal23 := by
    intro hchi_nonpos _hm ha hb
    exfalso
    linarith
  expMinimal23 := by
    intro hchi_nonpos _hm _ha0 _hb0 uStar huStar
    exfalso
    linarith
  global24 := h.global24
  exp24 := h.exp24
  global25 := by
    intro ha0 _hb0 _hm _hbeta uStar huStar
    exfalso
    linarith
  exp25 := by
    intro ha0 _hb0 _hm _hbeta uStar huStar
    exfalso
    linarith

end

end ShenWork.Paper3
```

Classification: **pure logical/vacuity wiring**.  It removes six explicit frontier fields from the actual-linear-small route and does not change the theorem’s mathematical strength under the existing hypotheses.

## Top reduction 2: shared initial continuity + positive-`a` compactness lite

This can be layered on top of reduction 1.  It uses the existing `intervalDomainSupNormCompactnessData` and `IntervalDomainPaper3SupNormCompactnessRegularizationData.toConcrete`, then fills the minimal upper branch by contradiction from `0 < p.a`.

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Compactness/regularization data needed in the actual-linear-small route after
choosing the canonical sup-norm upper envelope and using `0 < a` to make the
minimal-upper branch vacuous.  The shared initial-continuity field is supplied by
the surrounding mainline data. -/
structure IntervalDomainPaper3SupNormCompactnessAPosData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  compact : TimeTranslateCompactnessRaw intervalDomain p locallyConverges
  resolvent :
    NeumannResolventGradientBoundExistsRaw intervalDomain
      neumannResolventGradientBound

/-- Convert positive-`a` compactness data into the existing sup-norm compactness
package. -/
def IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound)
    (ha_pos : 0 < p.a)
    (hcont : IntervalDomainInitialContinuityRaw p) :
    IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound where
  compact := h.compact
  initialContinuity := hcont
  minimalUpper := by
    intro ha0 _hb0 _hm _hbeta _hchi0 _hchi u v huv
    exfalso
    linarith
  resolvent := h.resolvent

/-- Thin actual-linear raw-Theorem-2.2 mainline data: persistence is produced by
actual-linear-small, initial continuity is carried once, the compactness upper
field is definitional, and the minimal-upper field is vacuous from `0 < a`. -/
structure IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  theorem22Nonminimal :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  theorem22Minimal :
    LinearStabilityInstabilityMinimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the thin actual-linear data to the current full mainline data surface. -/
def IntervalDomainPaper3MainlineActualLinear22ThinFrontierData.toCurrent
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound)
    (ha_pos : 0 < p.a) (hchi_pos : 0 < p.χ₀) :
    IntervalDomainPaper3MainlineActualLinear22FrontierData
      p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) where
  core :=
    { initialContinuity := h.initialContinuity
      theorem22Nonminimal := h.theorem22Nonminimal
      theorem22Minimal := h.theorem22Minimal }
  compactness :=
    (h.compactness.toSupNormData ha_pos h.initialContinuity).toConcrete
  stability := h.stability24.toStability23To25 ha_pos hchi_pos

/-- Mainline target from the thin actual-linear raw-Theorem-2.2 route. -/
theorem intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ (hData.toCurrent ha hχ0)

end

end ShenWork.Paper3
```

Classification: **pure wiring + branch-vacuity reduction**.  It removes:

* duplicate `initialContinuity`;
* `upperEq` for canonical sup-norm compactness;
* `minimalUpper` under actual-linear `0 < p.a`;
* the six vacuous Theorem 2.3/2.5 stability fields if combined with reduction 1.

Remaining non-vacuous fields in this thin mainline package are exactly:

```text
initialContinuity
theorem22Nonminimal
theorem22Minimal
compact
resolvent
global24
exp24
```

plus the statement-level proposition data outside the mainline:

```text
negativeBound
paper2Main
```

## Sectorial raw-linear sibling route: audit of the uncommitted direction

The planned `IntervalDomainSectorialTheorem22LinearRawExistence` / `IntervalDomainSectorialMainlineLinearRawExistence` route is correct and non-conflicting.

Minimal intended shape:

```lean
import ShenWork.Paper3.IntervalDomainSectorial

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Sectorial Theorem 2.1/2.2 target data when Theorem 2.2 is supplied directly
by the raw linear stability/instability branches. -/
structure IntervalDomainSectorialTheorem22LinearRawExistence
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  persistence : IntervalDomainSectorialTheorem21Persistence p uBar
  theorem22Nonminimal :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  theorem22Minimal :
    LinearStabilityInstabilityMinimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical

/-- Sectorial Theorem 2.1/2.2 target from persistence plus raw linear Theorem 2.2
branches, bypassing `IntervalDomainSectorialMainlineCoreExistence`. -/
theorem intervalDomain_sectorialTheorem21And22Target_of_linearRawExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (h : IntervalDomainSectorialTheorem22LinearRawExistence
      p M0 uBar vLower) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower := by
  have h22 :
      Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
    intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw
      p intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
      (intervalDomainSectorialPaper3Constants_usesCriticalSpectrum
        p M0 uBar vLower)
      h.theorem22Nonminimal h.theorem22Minimal
  have h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
    intervalDomain_Theorem_2_1_sectorialMainline_of_persistence
      p M0 uBar vLower h.persistence
  exact ⟨h22, h21⟩

end

end ShenWork.Paper3
```

Then the actual-linear small wrapper should fill `persistence` by:

```lean
intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
```

Classification:

* assembling `h22` and `h21`: pure wiring;
* actual-linear persistence: already produced;
* raw linear branches: real analytic frontier;
* `IntervalDomainSectorialMainlineCoreExistence`: redundant for this raw-linear route only.

## What not to attack next

Do not spend this coordination slot on:

* `P3MoserHighExcursionProducer.lean` or `P3MoserThresholdPlanProducer.lean`; they are owned by another worker.
* `lowerUpperFrontiers` producers; keep them explicit or use the already exposed integrated-step atom.
* proving `energyContinuous` or `gradientTimeIntegrable` from `IsPaper2ClassicalSolution` alone.  The current explicit/lite regularity frontier is the honest interface.
* trying to derive `negativeBound` from Paper2 main targets.  The statement layer explicitly separates Paper3 Proposition 1.2 from Paper2 main theorem targets.

## Recommended next commit order

1. Finish and commit `P3MoserRegularityProducer.lean` lite data.  This is safe and local to Moser regularity:

```text
IntervalDomainIntegratedMoserRegularityFrontierDataLite
powerTimeIntegrable derived from energyContinuous
lite wrappers for lowerAverage/firstCrossing
```

2. Finish and commit the `IntervalDomainSectorial.lean` raw-linear sibling route.  This gives a reusable sectorial target independent of `IntervalDomainSectorialMainlineCoreExistence`.

3. Add the actual-linear statement-layer thin data described above.  This can be done entirely in `IntervalDomainActualLinearStatementAssembly.lean` and does not touch high-excursion files.  It reduces the current actual-linear statement surface to the genuinely non-vacuous fields:

```text
propositions.negativeBound
propositions.paper2Main
initialContinuity
theorem22Nonminimal
theorem22Minimal
compact
resolvent
global24
exp24
```

Everything else in the current route is either already produced, pure wiring, duplicated, or vacuous under `0 < p.a` / `0 < p.χ₀`.
