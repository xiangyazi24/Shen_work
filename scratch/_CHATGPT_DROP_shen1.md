# Q2916 (shen1) — anchored Moser first-crossing and positive-time locality

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target files: `ShenWork/PDE/P3MoserActualWiring.lean`, `ShenWork/PDE/P3MoserIntegratedClosure.lean`, `ShenWork/PDE/P3MoserRegularityProducer.lean`, `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`, `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`  
Source edit requested: none; answer file only.

## Verdict

The correct Lean route is:

1. Build all **regularity / FTC / integrated-dissipation** objects for the **anchored** representative

```lean
uA := intervalDomainWithInitialSlice u₀ u
```

because these objects see `t = 0` and are not safely positive-time-local.

2. Produce

```lean
IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0
```

for the anchored representative.

3. Transfer only the final **positive-time** consequences back to raw `u` using locality lemmas, especially:

```lean
LpPowerBoundedBefore intervalDomain p T uA ↔
LpPowerBoundedBefore intervalDomain p T u
```

and

```lean
IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0 →
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

because both predicates quantify only `0 < t < T`.

This is a pure WIRE NOW step. It is not an analytic frontier.

But do **not** try to coerce anchored `IntegratedMoserFirstCrossingRegularity`, `IntervalDomainIntegratedMoserClassicalRegularityData`, `IntegratedMoserDissipationDropBefore`, or endpoint-energy continuity into raw-`u` versions: those contain `t = 0` data and the raw Picard representative can be wrong there.

## Existing source status

I did not find an existing pushed lemma named like:

```lean
LpPowerBoundedBefore_congr
IntegratedMoserFirstCrossingStep_congr
IntegratedMoserFirstCrossingStep_of_eqOn_Ioo
```

The visible existing locality tool is around classical solutions:

```lean
classicalSolutionLocalityUnderIooAgreement_intervalDomain
```

which is the right kind of theorem for positive-time classical facts, but it does not transfer `LpPowerBoundedBefore` or `IntegratedMoserFirstCrossingStep`.

The definitions make the needed transfer straightforward:

```lean
-- ShenWork/Paper2/Statements.lean
def LpPowerBoundedBefore
    (D : BoundedDomainData) (pExp Tmax : ℝ)
    (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ C, ∀ t, 0 < t → t < Tmax →
    D.integral (fun x => (u t x) ^ pExp) ≤ C
```

and:

```lean
-- ShenWork/PDE/P3MoserIntegratedClosure.lean
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u
```

So both are exactly positive-time-local.

## Add these locality lemmas

Put these in a non-Zinan wiring file, preferably `P3MoserIntegratedClosure.lean` near `IntegratedMoserFirstCrossingStep`, or in a small shared locality file imported by both `P3MoserActualWiring.lean` and `IntervalDomainStatementAssembly.lean`.

### 1. Positive-time equality predicate, optional but useful

```lean
def EqOnPositiveTimesBefore
    {D : BoundedDomainData} (T : ℝ)
    (u w : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T → ∀ x : D.Point, u t x = w t x
```

You can also avoid the definition and use the hypothesis inline.

### 2. Transfer `LpPowerBoundedBefore`

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- `LpPowerBoundedBefore` only sees positive times, so it is invariant under
agreement on `0 < t < T`. -/
theorem LpPowerBoundedBefore_congr_pos
    {D : BoundedDomainData} {p T : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : ∀ t, 0 < t → t < T → ∀ x : D.Point, u t x = w t x) :
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D p T w := by
  intro h
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro t ht0 htT
  have hfun :
      (fun x : D.Point => (w t x) ^ p) =
        (fun x : D.Point => (u t x) ^ p) := by
    funext x
    rw [← hEq t ht0 htT x]
  simpa [hfun] using hC t ht0 htT

/-- Symmetric form of positive-time locality for `LpPowerBoundedBefore`. -/
theorem LpPowerBoundedBefore_iff_of_pos_eq
    {D : BoundedDomainData} {p T : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : ∀ t, 0 < t → t < T → ∀ x : D.Point, u t x = w t x) :
    LpPowerBoundedBefore D p T u ↔
      LpPowerBoundedBefore D p T w := by
  constructor
  · exact LpPowerBoundedBefore_congr_pos hEq
  · exact LpPowerBoundedBefore_congr_pos
      (fun t ht0 htT x => (hEq t ht0 htT x).symm)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

This is expected to compile with only minor namespace adjustment. If `LpPowerBoundedBefore` is not in scope, add:

```lean
open ShenWork.Paper2
```

or fully qualify it as `ShenWork.Paper2.LpPowerBoundedBefore`.

### 3. Transfer `AbstractLpBootstrapHypothesis`

This is needed when a local/statement producer has a raw bootstrap hypothesis but the anchored step construction wants the bootstrap package for `uA`.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- The abstract bootstrap hypothesis is positive-time-local because its only
`u`-dependent field is `LpPowerBoundedBefore`. -/
theorem AbstractLpBootstrapHypothesis_congr_pos
    {D : BoundedDomainData} {N T rho p0 : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : ∀ t, 0 < t → t < T → ∀ x : D.Point, u t x = w t x)
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0) :
    AbstractLpBootstrapHypothesis D w N T rho p0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AbstractLpBootstrapHypothesis.rho_pos hboot
  · exact AbstractLpBootstrapHypothesis.T_pos hboot
  · exact AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
  · exact LpPowerBoundedBefore_congr_pos hEq
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If the field accessors differ locally, the constructor order is the same pattern already used in `P3MoserActualWiring.abstract_prop25_bootstrap_two_gamma`:

```lean
⟨rho_pos, T_pos, p0_gt_threshold, initial_lp_bound⟩
```

### 4. Transfer `IntegratedMoserFirstCrossingStep`

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- `IntegratedMoserFirstCrossingStep` is positive-time-local because it is a
map between `LpPowerBoundedBefore` predicates. -/
theorem IntegratedMoserFirstCrossingStep_congr_pos
    {D : BoundedDomainData} {T rho p0 : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : ∀ t, 0 < t → t < T → ∀ x : D.Point, u t x = w t x) :
    IntegratedMoserFirstCrossingStep D u T rho p0 →
      IntegratedMoserFirstCrossingStep D w T rho p0 := by
  intro hstep p hp hLp_w
  have hLp_u : LpPowerBoundedBefore D p T u :=
    LpPowerBoundedBefore_congr_pos
      (fun t ht0 htT x => (hEq t ht0 htT x).symm) hLp_w
  exact LpPowerBoundedBefore_congr_pos hEq (hstep p hp hLp_u)

/-- Symmetric form for `IntegratedMoserFirstCrossingStep`. -/
theorem IntegratedMoserFirstCrossingStep_iff_of_pos_eq
    {D : BoundedDomainData} {T rho p0 : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hEq : ∀ t, 0 < t → t < T → ∀ x : D.Point, u t x = w t x) :
    IntegratedMoserFirstCrossingStep D u T rho p0 ↔
      IntegratedMoserFirstCrossingStep D w T rho p0 := by
  constructor
  · exact IntegratedMoserFirstCrossingStep_congr_pos hEq
  · exact IntegratedMoserFirstCrossingStep_congr_pos
      (fun t ht0 htT x => (hEq t ht0 htT x).symm)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

This is the main WIRE NOW lemma.

### 5. Interval-domain anchored equality lemma

Put this next to `intervalDomainWithInitialSlice`.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- The anchored representative agrees with the raw representative at every
strictly positive time. -/
theorem intervalDomainWithInitialSlice_eq_raw_of_pos
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    {t : ℝ} (ht : 0 < t) :
    intervalDomainWithInitialSlice u₀ u t = u t := by
  funext x
  simp [intervalDomainWithInitialSlice, ne_of_gt ht]

/-- Pointwise version convenient for locality lemmas. -/
theorem intervalDomainWithInitialSlice_eq_raw_of_pos_apply
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    {t : ℝ} (ht : 0 < t) (x : intervalDomain.Point) :
    intervalDomainWithInitialSlice u₀ u t x = u t x := by
  simpa using congrFun (intervalDomainWithInitialSlice_eq_raw_of_pos
    (u₀ := u₀) (u := u) ht) x

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## Wrapper: anchored step to raw step

Once you have an anchored step, the raw step is pure locality.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserIntegratedClosure

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Use an anchored first-crossing step as a raw first-crossing step, since both
`IntegratedMoserFirstCrossingStep` and `LpPowerBoundedBefore` only see
`0 < t < T`. -/
theorem intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
    {T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hstepA :
      IntegratedMoserFirstCrossingStep intervalDomain
        (intervalDomainWithInitialSlice u₀ u) T rho p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  refine IntegratedMoserFirstCrossingStep_congr_pos ?_ hstepA
  intro t ht0 _htT x
  exact intervalDomainWithInitialSlice_eq_raw_of_pos_apply ht0 x

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

This is the safest bridge into raw APIs.

## What not to transfer

Do **not** add raw/anchored congruence lemmas for the following unless the theorem statement explicitly avoids `t = 0`:

```lean
IntegratedMoserFirstCrossingRegularity
IntervalDomainIntegratedMoserClassicalRegularityData
IntervalDomainIntegratedMoserGlobalClassicalRegularityData
IntegratedMoserDissipationDropBefore
IntegratedMoserEnergyWindowFTC
IntervalDomainInitialPowerEnergyContinuityAtZero
IntervalDomainPowerEnergyEndpointContinuity
```

These contain `t = 0`, endpoint continuity, or windows with `t1 = 0`; raw and anchored representatives can differ there. Transferring them would be false or would require extra compatibility assumptions.

In particular:

```lean
IntegratedMoserDissipationDropBefore D u T rho p0
```

is not obviously positive-time-local: its windows are quantified over

```lean
t1 ∈ Set.Icc 0 T, t2 ∈ Set.Icc t1 T
```

so `t1 = 0` is allowed and the term `D.integral (fun x => (u t1 x)^p)` sees the stored zero slice. Build this predicate for anchored `uA` if needed; do not transfer raw to anchored or anchored to raw without additional endpoint compatibility.

## How to use this in the existing statement stack

### Correct pattern inside a solution-specific producer

Given raw solution data:

```lean
hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v
htrace  : InitialTrace intervalDomain u₀ u
hdatum  : PaperPositiveInitialDatum intervalDomain u₀
hgrad   : IntervalDomainRawMoserGradientTimeIntegrability u T p0
```

construct the anchored object:

```lean
let uA := intervalDomainWithInitialSlice u₀ u
```

prove the anchored regularity / FTC / lower-upper data and hence:

```lean
hstepA : IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0
```

then immediately export the raw step:

```lean
have hstepRaw : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored hstepA
```

Then existing raw-`u` consumers can be used safely:

```lean
intervalDomain_boundedBefore_of_integrated_first_crossing_step
all_exponents_of_integrated_first_crossing_step_lpmono
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

because the thing they consume is now a raw-`u` step.

### But do not try to fill the old universal local `hstep` field from anchoring

The pushed `P3MoserActualWiring` route expects a field of this shape:

```lean
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
  IsPaper2ClassicalSolution intervalDomain params T u v →
  CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
  AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0 →
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

The anchored theorem cannot produce this field by itself, because it needs additional data that the local signature does not provide:

```lean
u₀
InitialTrace intervalDomain u₀ u
PaperPositiveInitialDatum intervalDomain u₀
IsPaper2GlobalClassicalSolution intervalDomain params u v
IntervalDomainRawMoserGradientTimeIntegrability u T p0
```

Therefore the existing purely local statement-layer field is too thin for the anchored route. This is not an analytic obstacle; it is a route-shape mismatch.

## Smallest route wrapper to add

Add a new frontier/wrapper whose step field has the data needed to build the anchored representative but whose output is a raw step.

A minimal theorem-level wrapper:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- Build a raw first-crossing step through the anchored representative.  This is
pure wiring after the anchored first-crossing step has been produced. -/
theorem intervalDomain_integratedMoserFirstCrossingStep_of_globalClassicalTraceAnchored
    {params : CM2Params} {T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hgradRaw : IntervalDomainRawMoserGradientTimeIntegrability u T p0)
    -- plus the honest analytic/window frontiers needed to turn anchored regularity
    -- into an anchored first-crossing step:
    (hstepA :
      IntegratedMoserFirstCrossingStep intervalDomain
        (intervalDomainWithInitialSlice u₀ u) T rho p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  exact intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored hstepA

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
```

In practice, the wrapper should not take `hstepA` as a field if you already have lower/upper-window producers. Instead it should build `hstepA` internally from:

```lean
IntegratedMoserFirstCrossingRegularity intervalDomain (intervalDomainWithInitialSlice u₀ u) T p0
IntegratedMoserEnergyNonnegativity intervalDomain (intervalDomainWithInitialSlice u₀ u) T p0
IntegratedMoserDissipationDropBefore intervalDomain (intervalDomainWithInitialSlice u₀ u) T rho p0
RelativeMoserInterpolationBefore intervalDomain (intervalDomainWithInitialSlice u₀ u) T rho p0
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData ...
```

and then call `intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored`.

## Statement-layer recommendation

Do not keep trying to satisfy:

```lean
IntervalDomainPaper2Prop25IntegratedStepFrontierData.integratedStep
```

from the anchored theorem unless you have a separate way to supply global trace data for every local classical branch.

Instead add a global-trace/anchored statement-layer record. Its key field should return a raw step after internally anchoring:

```lean
structure IntervalDomainPaper2Prop25AnchoredIntegratedStepFrontierData
    (p : CM2Params) : Prop where
  integratedStepFromGlobalTrace :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PaperPositiveInitialDatum intervalDomain u₀ →
    ∀ {T rho p0 : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingStep intervalDomain u T rho p0

  quantitativeEndpoint :
    -- existing endpoint field, raw-u, because the final raw step supplies raw Lp bounds
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

Then write theorem-level consumers where the headline context actually has `hglobal` and `htrace`. This avoids pretending to prove a local Proposition 2.5 atom for arbitrary local branches.

## Optional transfer lemmas for final boundedness

If some route already produces final boundedness for anchored `uA`, transfer it explicitly:

```lean
theorem IsPaper2BoundedBefore_congr_pos
    {D : BoundedDomainData} {T : ℝ}
    {u w : ℝ → D.Point → ℝ}
    (hSup : ∀ t, 0 < t → t < T, D.supNorm (u t) = D.supNorm (w t)) :
    IsPaper2BoundedBefore D T u → IsPaper2BoundedBefore D T w := by
  intro h
  rcases h with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht0 htT
  simpa [← hSup t ht0 htT] using hM t ht0 htT
```

For `intervalDomainWithInitialSlice`, prove the `hSup` equality from `intervalDomainWithInitialSlice_eq_raw_of_pos`.

But this is usually second-best. Prefer transferring the first-crossing step to raw and then running existing raw endpoint/Prop.2.5 consumers.

## Classification

### WIRE NOW

* `LpPowerBoundedBefore_congr_pos`
* `AbstractLpBootstrapHypothesis_congr_pos`
* `IntegratedMoserFirstCrossingStep_congr_pos`
* `intervalDomainWithInitialSlice_eq_raw_of_pos`
* `intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored`
* optional `IsPaper2BoundedBefore_congr_pos`

These are all positive-time locality lemmas and should not require new analysis.

### HONEST FRONTIER

* Producing `IntervalDomainRawMoserGradientTimeIntegrability`.
* Producing anchored `IntegratedMoserDissipationDropBefore`, `IntegratedMoserEnergyWindowFTC`, lower-average windows, upper-data-gap choices, etc.
* Proving a universal local `integratedStep` field from the anchored theorem without adding global/trace/datum hypotheses. That is not valid as a wiring theorem; it is a statement-shape mismatch.

## Bottom line

Use anchoring only for objects that see `t = 0`; after producing the anchored first-crossing step, cross back to raw `u` through positive-time locality. The existing Paper2 raw APIs can then be used safely. The needed bridge is small and should be added as locality lemmas, not as a fake proof that raw zero-time regularity equals anchored zero-time regularity.
