# Q794 / cron1: heatTerm and boundedWeightJointTerm

Repo inspected: xiangyazi24/Shen_work
Branch written: chatgpt-scratch

## Verdict

Yes. `heatTerm` has exactly the same separated form as `boundedWeightJointTerm`.

`boundedWeightJointTerm` is defined in `ShenWork/PDE/IntervalResolverJointC2Physical.lean` as a generic separated mode term:

```lean
def boundedWeightJointTerm (c : Nat -> Real -> Real) (n : Nat) : Real × Real -> Real :=
  fun q => c n q.1 * cosineMode n q.2
```

The one-mode estimate

```lean
boundedWeightJointTerm_iteratedFDeriv_le
```

is also generic in `c : Nat -> Real -> Real`; it is not tied to resolver coefficients. It only asks for `ContDiff Real 2 (c n)` and pointwise bounds on the time derivatives of `c n`.

## Exact rewrite

`heatTerm` is currently:

```lean
def heatTerm (u0 : intervalDomainPoint -> Real) (n : Nat) : Real × Real -> Real :=
  fun q => (Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u0) n) * cosineMode n q.2
```

So define:

```lean
def heatTimeCoeff (u0 : intervalDomainPoint -> Real) : Nat -> Real -> Real :=
  fun n t => Real.exp (-t * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u0) n
```

Then this should close by definitional equality:

```lean
theorem heatTerm_eq_boundedWeightJointTerm
    (u0 : intervalDomainPoint -> Real) (n : Nat) :
    heatTerm u0 n =
      ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm
        (heatTimeCoeff u0) n := by
  rfl
```

If imports/unfolding get in the way, use `funext q; rfl`.

## Caveat: Bt cannot depend on time

The idea is right, but `Bt` has type

```lean
Nat -> Nat -> Real
```

so it cannot be `norm (iteratedFDeriv ... t)` as a function of `t`. For the pointwise theorem, the hypothesis is checked at the current `q.1`, but the bound is still the time-independent number `Bt i n`. For the series assembler, the required hypothesis is uniform in all `t`.

Therefore the estimate using `Real.exp (-(c / 2) * lambda_n)` only works on the region `t >= c / 2`. It is not a global bound for the raw uncutoff `heatTerm` on all real times, because the exponential grows for negative time.

## Best route for the cutoff series

For the global cutoff-series proof, fold the cutoff into the coefficient family instead:

```lean
def cutoffHeatTimeCoeff (u0 : intervalDomainPoint -> Real) (c : Real) : Nat -> Real -> Real :=
  fun n t => smoothRightCutoff (c / 2) c t *
    (Real.exp (-t * unitIntervalCosineEigenvalue n) *
      cosineCoeffs (intervalDomainLift u0) n)
```

Then `cutoffHeatTerm u0 c n` should be definitional as

```lean
boundedWeightJointTerm (cutoffHeatTimeCoeff u0 c) n
```

This lets `boundedWeightJointTerm_iteratedFDeriv_le` handle the joint `(t,x)` Leibniz split and the cosine spatial weights. The remaining bound is one-dimensional in time:

```lean
forall i <= 2, forall n t,
  norm (iteratedFDeriv Real i (cutoffHeatTimeCoeff u0 c n) t) <= Bt i n
```

A natural `Bt` has the coarse shape

```text
C_i * (1 + unitIntervalCosineEigenvalue n)^i * M0 *
  exp (-(c / 2) * unitIntervalCosineEigenvalue n)
```

where `C_i` absorbs the finitely many cutoff derivative bounds and binomial constants.

## Exp coefficient

For the raw time coefficient `t |-> exp (-t * lambda_n) * ahat_n`, the expected formula is correct:

```text
D^i = (-lambda_n)^i * ahat_n * exp (-t * lambda_n)
```

For `i <= 2`, Lean may be easier if you split cases `i = 0`, `i = 1`, `i = 2` rather than proving a general iterated-derivative formula and then bridging to `iteratedFDeriv` norms.

## Bottom line

- Yes, express `heatTerm` as `boundedWeightJointTerm heatTimeCoeff`.
- Yes, `boundedWeightJointTerm_iteratedFDeriv_le` accepts arbitrary coefficient families.
- But the majorant `Bt` must be independent of `t`.
- For raw `heatTerm`, the exponential majorant is only valid on positive-time slabs.
- For the global cutoff proof, use `boundedWeightJointTerm` with the cutoff included in the time coefficient; this reuses the existing bounded-weight cosine machinery and leaves only a one-dimensional time-coefficient derivative bound.
