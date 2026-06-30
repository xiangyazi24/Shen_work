# Q2674 (shen1) — at-zero endpoint package audit

Repo: `xiangyazi24/Shen_work`, Lean 4.  
Scope: non-Zinan files only.  Do **not** edit or rely on
`ShenWork/PDE/P3MoserHighExcursionProducer.lean` or
`ShenWork/PDE/P3MoserThresholdPlanProducer.lean`.

## Verdict

The at-zero endpoint field

```lean
∀ p, p0 ≤ p →
  ContinuousWithinAt
    (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
    (Set.Icc (0 : ℝ) T) 0
```

is an **honest residual** under the current repository APIs.  I do not see a
Lean-compilable theorem deriving it from existing `InitialTrace`,
`IsPaper2GlobalClassicalSolution`, or current interval-domain energy-continuity
helpers.

The key reason is exact and repository-local: the current classical/global
solution interfaces are interior-time interfaces, while `InitialTrace` controls
only positive times against `u₀`; neither constrains the actual value `u 0`, and
the target `ContinuousWithinAt` is continuity to the value computed from `u 0`.

## Source audit

### 1. `InitialTrace` does not mention `u 0`

Current definition in `ShenWork/Paper2/Statements.lean`:

```lean
def InitialTrace
    (D : BoundedDomainData) (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    D.supNorm (fun x => u t x - u₀ x) < ε
```

and the only direct accessor is:

```lean
lemma InitialTrace.eventually_small
    {D : BoundedDomainData} {u₀ : D.Point → ℝ} {u : ℝ → D.Point → ℝ}
    (h : InitialTrace D u₀ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      D.supNorm (fun x => u t x - u₀ x) < ε :=
  h ε hε
```

So `InitialTrace` gives a right-limit statement for `t > 0`, but it does not say
`u 0 = u₀`, and it does not state any energy convergence theorem.

### 2. `IsPaper2GlobalClassicalSolution` also does not control `t = 0`

Current definition:

```lean
def IsPaper2GlobalClassicalSolution
    (D : BoundedDomainData) (p : CM2Params)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ T > 0, IsPaper2ClassicalSolution D p T u v
```

and `IsPaper2ClassicalSolution` only quantifies its positivity/PDE fields over
`0 < t ∧ t < T`.  Its `D.classicalRegularity T u v` field is also the
interval-domain `intervalDomainClassicalRegularity`, whose time-regularity fields
are on `Set.Ioo (0 : ℝ) T`, not at `0`.

Thus a global classical branch lets you prove right-endpoint continuity at any
positive `T` by viewing `T` as an interior point of a longer horizon, which is
exactly what the current theorem does.  It still says nothing about the left
endpoint `0`.

### 3. Existing endpoint helper consumes `atZero`; it does not produce it

Current theorem in `ShenWork/PDE/P3MoserEnergyContinuity.lean`:

```lean
theorem intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero :
      ∀ p, p0 ≤ p →
        ContinuousWithinAt
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T) 0) :
    IntervalDomainPowerEnergyEndpointContinuity u T p0
```

This is the right theorem: it derives `atRight` from the global branch and keeps
`atZero` explicit.

### 4. Existing interior continuity also does not reach `0`

Current theorem:

```lean
theorem intervalDomain_energyContinuousOn_Ioo
    {params : CM2Params} {T p : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (Ioo (0 : ℝ) T)
```

This proves interior continuity only.  It is enough for `(0,T)` and, under global
classical solution, for the right endpoint `T` by extending to `T+1`; it cannot
prove continuity at `0`.

### 5. The L² closed-energy trace package is too special

`ShenWork/PDE/P3MoserLemmaDischarge.lean` has:

```lean
structure ClosedEnergyIdentityTraceData
    (T : ℝ) (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) where
  nonnegT : 0 ≤ T
  g : ℝ → ℝ
  g_integrable : IntegrableOn g (Set.uIcc (0 : ℝ) T) volume
  energy_eq :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      intervalDomainLpAbsEnergy 2 u t =
        intervalDomainLpAbsEnergy 2 u 0 + ∫ s in (0 : ℝ)..t, g s
  initial_trace_energy :
    intervalDomainLpAbsEnergy 2 u 0 =
      intervalDomain.integral (fun x : intervalDomain.Point => |u₀ x| ^ (2 : ℝ))
  ...
```

and

```lean
theorem ClosedEnergyIdentityTraceData.energyContinuous
    ... :
    ContinuousOn (fun t => intervalDomainLpAbsEnergy 2 u t)
      (Set.Icc (0 : ℝ) T)
```

This only handles the L² absolute energy through an explicit integrated energy
identity.  It is not a general `∀ p ≥ p0` power-energy-at-zero theorem, and it is
not derived from `InitialTrace` alone.

## Why `InitialTrace` alone cannot imply the target

The failure is structural, not just a missing lemma name.

`InitialTrace intervalDomain u₀ u` is invariant under changing `u 0`, because it
only quantifies over `0 < t`.  `IsPaper2GlobalClassicalSolution` is also invariant
under changing `u 0`, because its fields are all for interior positive times.

But the target value is

```lean
intervalDomain.integral (fun x => (u 0 x) ^ p)
```

so changing `u 0` changes the claimed limit target.  Semantically, one can keep
`u t = u₀` for all sufficiently small `t > 0`, redefine `u 0` to a different
positive profile, and preserve the current `InitialTrace` and positive-time
classical/global predicates while breaking continuity at `0` for, say, `p = 1`
when that exponent is in range.

Even adding `∀ x, u 0 x = u₀ x` would not be enough with the current repo theorem
inventory for arbitrary real powers: one would still need a proved bridge from
sup-norm trace convergence plus positivity/floor control to convergence of
`∫ (u t)^p` for all `p ≥ p0`.  I did not find such a theorem in the current
Moser/initial-trace files.

## Smallest honest interface patch

The current field in
`IntervalDomainIntegratedMoserGlobalClassicalRegularityData` is already the
smallest honest residual.  If you want it named independently for reuse, put this
in `ShenWork/PDE/P3MoserEnergyContinuity.lean` near
`IntervalDomainPowerEnergyEndpointContinuity`.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Left-endpoint power-energy continuity on `[0,T]`, exponent-by-exponent.

This is the honest residual not supplied by either `InitialTrace` or the current
positive-time classical/global solution API. -/
def IntervalDomainPowerEnergyAtZeroContinuity
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ContinuousWithinAt
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (Set.Icc (0 : ℝ) T) 0

/-- Named-data version of
`intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical`. -/
theorem intervalDomain_powerEnergyEndpointContinuity_of_atZeroContinuity_and_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainPowerEnergyAtZeroContinuity u T p0) :
    IntervalDomainPowerEnergyEndpointContinuity u T p0 :=
  intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
    hglobal hT hzero

#print axioms IntervalDomainPowerEnergyAtZeroContinuity
#print axioms
  intervalDomain_powerEnergyEndpointContinuity_of_atZeroContinuity_and_global_classical

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
```

Inside the existing file, do not duplicate the imports; just add the `def` and
wrapper theorem after `IntervalDomainPowerEnergyEndpointContinuity` or after the
existing global-classical endpoint theorem.  Then change the global regularity
package field, if desired, from the expanded function type to:

```lean
atZero : IntervalDomainPowerEnergyAtZeroContinuity u T p0
```

and the existing converter remains the same modulo the wrapper name.

## Future producer target, if someone wants to attack it later

The honest analytic target should be named as a producer from **stronger** trace
inputs, not from `InitialTrace` alone.  A good theorem target would be something
like:

```lean
-- Suggested target name only; do not add as an axiom.
theorem intervalDomain_powerEnergyAtZeroContinuity_of_initialTrace_zeroValue_floor
    {T p0 : ℝ} {u₀ u : ℝ →?} :
    -- inputs should include:
    -- * InitialTrace intervalDomain u₀ u
    -- * exact zero value: ∀ x, u 0 x = u₀ x
    -- * positive floor / rpow control near zero, especially for real powers
    -- * a supNorm-to-integral convergence lemma for `(·)^p`
    IntervalDomainPowerEnergyAtZeroContinuity u T p0 := by
  -- real analytic proof, not currently available
```

I would **not** introduce this theorem until the needed sup-norm/rpow/integral
continuity lemmas are actually proved.  For now, the clean interface is to keep
`IntervalDomainPowerEnergyAtZeroContinuity` as the named residual consumed by the
existing global-classical endpoint theorem.
