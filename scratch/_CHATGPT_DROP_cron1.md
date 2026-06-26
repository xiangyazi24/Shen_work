# Q717 / cron1: producers of `PhysicalResolverJointC2Data`

Repo inspected: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

## Verdict

Yes, the repo has an existing producer of `PhysicalResolverJointC2Data` for an arbitrary trajectory `u`, but it is **generic** and requires source-side physical time-`C²` data.  I did **not** find a heat-semigroup-specific producer for

```lean
PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

or for the equivalent level-0 heat trajectory.

The main producer is:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

```lean
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

This is the only direct theorem I found whose conclusion is `PhysicalResolverJointC2Data ...`.  It is not tied to heat; it works for any trajectory `u` once you provide:

```lean
H : PhysicalSourceTimeC2 p u Es
```

The resolver coefficient bound is then built by factoring the constant elliptic weight:

```lean
resolverTimeCoeff p u k t = intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

and transferring `ContDiff ℝ 2` plus three-order coefficient bounds from `srcTimeCoeff` to `resolverTimeCoeff`.

## Structure definition and consumers

The structure itself is defined in:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

The same file mostly **consumes** the structure to produce resolver joint regularity:

```lean
theorem coupledChemical_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) ... :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) ... :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

These are consumers, not producers of the data bundle.

## Direct producer: `physicalResolverJointC2Data_of_floor`

File:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

The upstream source-side structure is:

```lean
structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
  src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
```

The producer:

```lean
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k) where
  coeff_contDiff k := by
    have : resolverTimeCoeff p u k =
        fun t => intervalNeumannResolverWeight p k * srcTimeCoeff p u k t := by
      funext t; exact resolverTimeCoeff_eq_weight_smul p u k t
    rw [this]
    exact contDiff_const.mul (H.src_contDiff k)
  coeff_bound i k t hi :=
    resolverTimeCoeff_bound p u H.src_contDiff H.src_bound i k t hi
  value_summable := H.value_summable
  grad_summable := H.grad_summable
```

This exactly fills the four fields requested in the question:

1. `coeff_contDiff`: from `H.src_contDiff k` and constant multiplication by `intervalNeumannResolverWeight p k`.
2. `coeff_bound`: from `resolverTimeCoeff_bound`, i.e. the source bound multiplied by the resolver weight.
3. `value_summable`: copied from `H.value_summable`.
4. `grad_summable`: copied from `H.grad_summable`.

## Source-side producer feeding it

There is a source-side producer in:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

It proves `PhysicalSourceTimeC2` from floored source time data plus summability assumptions:

```lean
theorem physicalSourceTimeC2_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H)
```

Therefore the existing generic pipeline is:

```lean
FlooredSourceTimeData p u s₁ s₂
+ source weighted value/gradient summability
  ⟹ PhysicalSourceTimeC2 p u (builtEs H)
  ⟹ PhysicalResolverJointC2Data p u (fun i k => w_k * builtEs H i k)
```

where the second implication is `physicalResolverJointC2Data_of_floor`.

## End-to-end wrappers that use the producer internally

Also in `IntervalPhysicalResolverDataConcrete.lean`:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_floor
    (H : PhysicalSourceTimeC2 p u Es)
    (other : ...) :
    CoupledChemDivFluxFactorJointC2Inputs p u :=
  ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemDivFluxFactorJointC2Inputs_of_physical
    (physicalResolverJointC2Data_of_floor H) other
```

This is not itself a `PhysicalResolverJointC2Data` result, but it internally calls the producer and then consumes the result.

In:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

there is the more concrete iterate pipeline:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate
    (H : IterateSourceTimeData p u du d2u)
    (hval : ...)
    (hgrad : ...)
    (other : ...) :
    CoupledChemDivFluxFactorJointC2Inputs p u :=
  ShenWork.IntervalPhysicalResolverDataConcrete.coupledChemDivFluxFactorJointC2Inputs_of_floor
    (physicalSourceTimeC2_of_floored (flooredSourceTimeData_of_iterate H) hval hgrad)
    other
```

This is an end-to-end factor-input producer, but it does **not** expose `PhysicalResolverJointC2Data` as its conclusion.

## Files that only consume `PhysicalResolverJointC2Data`

Search hits included several consumers.  Important examples:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    (H : PhysicalResolverJointC2Data p u Bt)
    ... :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    (H : PhysicalResolverJointC2Data p u Bt)
    ... :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

```text
ShenWork/PDE/IntervalChemDivMixedReprWitness.lean
```

This file consumes `PhysicalResolverJointC2Data` in its mixed-representative witness machinery; its header says the `v`-side continuous representatives come from bounded-weight value/grad/time joint series, with `PhysicalResolverJointC2Data` providing the resolver-side input.

```text
ShenWork/PDE/IntervalIterateGradMajorant.lean
```

```lean
theorem chemDivMixedClosedRepr_of_iterateGradSummable
    (H : PhysicalResolverJointC2Data p u Bt)
    (Hu : IteratePicardJointC2Data u c Btu)
    ... :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

These are all consumers, not producers.

## Heat-semigroup status

Searches run:

```text
PhysicalResolverJointC2Data
PhysicalResolverJointC2Data p u
physicalResolverJointC2Data_of
PhysicalSourceTimeC2 PhysicalResolverJointC2Data
physicalResolverJointC2Data_of_floor conjugatePicardIter
physicalSourceTimeC2_of_floored conjugatePicardIter
PhysicalResolverJointC2Data conjugatePicardIter
level0 PhysicalResolverJointC2Data
```

I found no heat-level specialization.

So for the heat semigroup `u t = conjugatePicardIter p u₀ 0 t`, the nearest existing route is to instantiate the generic source-side package:

```lean
PhysicalSourceTimeC2 p (conjugatePicardIter p u₀ 0) Es
```

then feed it to:

```lean
physicalResolverJointC2Data_of_floor
```

Concretely, the missing heat-specific work is exactly to prove the `PhysicalSourceTimeC2` inputs for

```lean
srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t
  = cosineCoeffs (fun x => p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ) k
```

namely:

* `src_contDiff`: `t ↦ srcTimeCoeff ... k t` is `ContDiff ℝ 2` on the intended domain/window;
* `src_bound`: three-order source coefficient bounds;
* weighted bounded-majorant summability for value and gradient.

The global version of these fields is stronger than a positive-window heat statement because the existing structures quantify over all `t : ℝ`.  For heat smoothing, a positive-window/localized version may be more natural unless the repo already has a global extension/cutoff convention for these heat coefficients.

## Bottom line

There is one direct generic producer:

```lean
physicalResolverJointC2Data_of_floor
```

There is no discovered direct heat-semigroup producer.  To package heat, use the existing producer after proving or adapting a heat-specific `PhysicalSourceTimeC2`/`FlooredSourceTimeData` package and the two bounded-weight summability fields.
