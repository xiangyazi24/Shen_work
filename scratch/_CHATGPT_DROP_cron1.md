# Q852 / cron1: direct resolver joint `C²` vs `PhysicalResolverJointC2Data`

Repo inspected: `xiangyazi24/Shen_work`

Source ref inspected: `main`

Branch written: `chatgpt-scratch`

## Verdict

Yes, **in principle** you can feed resolver coefficients directly to

```lean
boundedWeightJointSeries_contDiff_two
```

and get joint `C²` of the resolver cosine series without first constructing

```lean
PhysicalResolverJointC2Data
```

as a named object.

But this is mostly a packaging shortcut, not a mathematical shortcut.  The fields you must prove for the direct call are essentially the fields of `PhysicalResolverJointC2Data`:

```lean
∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
∀ i k t, i ≤ 2 → ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
∀ m ≤ 2, Summable (boundedWeightJointMajorant Bt m)
```

and, if you also need the spatial-gradient resolver field, the gradient analogue:

```lean
∀ m ≤ 2, Summable (boundedWeightJointGradMajorant Bt m)
```

So: **yes, direct feeding works**, but **no, it does not avoid the coefficient-time-`C²` and summable-majorant work**.  It only avoids naming the bundle.

## What the repo already has

The generic assembler is exactly available:

```lean
theorem boundedWeightJointSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointTerm c n q)
```

The concrete resolver coefficient family is also already defined:

```lean
def resolverTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverCoeff p (u t) k).re
```

and the repo already proves that this is just the source coefficient multiplied by the constant elliptic weight:

```lean
theorem resolverTimeCoeff_eq_weight_smul
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    resolverTimeCoeff p u k t =
      intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

So your formula

```lean
resolver coeff = source coeff / (μ + λ_k)
```

is already committed as `resolverTimeCoeff_eq_weight_smul`, with
`intervalNeumannResolverWeight p k = 1 / (μ + λ_k)`.

## Existing direct physical resolver route

The file

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

already does the direct resolver-series assembly from `PhysicalResolverJointC2Data`:

```lean
theorem coupledChemical_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo 0 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

Its proof is literally:

```lean
have hseries : ContDiff ℝ (2 : ℕ∞)
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, boundedWeightJointTerm (resolverTimeCoeff p u) k q) :=
  boundedWeightJointSeries_contDiff_two H.coeff_contDiff
    (fun i k t hi => H.coeff_bound i k t hi) H.value_summable
```

and then it uses the already-proved series equality on `[0,1]`.

The gradient version is also already committed:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) ... :
    ContDiffAt ℝ 2
      (fun q => deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

That one feeds the gradient bounded-weight series assembler and uses `H.grad_summable`.

## What this means for the proposed shortcut

If your immediate goal is only:

```lean
ContDiffAt ℝ 2
  (fun q => intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s,x)
```

then a local theorem can inline `boundedWeightJointSeries_contDiff_two` and avoid constructing the `PhysicalResolverJointC2Data` value.

But if your goal is the FAC/chem-div infrastructure, building `PhysicalResolverJointC2Data` is probably still the best interface, because downstream already consumes it for:

```lean
coupledChemical_jointContDiffAt_two
coupledChemical_grad_jointContDiffAt_two
coupledChemical_innerCommute_of_physicalJointC2
coupledChemDivFlux_timeBridge_of_physicalJointC2
```

Bypassing the structure means you will likely re-prove or locally duplicate these consumers.

## The real gap does not disappear

The hard part is not the resolver series assembly.  The hard part is proving, for the heat semigroup source coefficients, the source/resolver coefficient hypotheses:

1. `t ↦ srcTimeCoeff p u k t` or `t ↦ resolverTimeCoeff p u k t` is `ContDiff ℝ 2`,
2. its first two time derivatives are the expected cosine coefficients of explicit time-derivative slices,
3. those slices have uniform zeroth-mode bounds and `(kπ)⁻²` decay,
4. after multiplying by the elliptic weight, the value and gradient bounded-weight majorants are summable.

This is exactly why `FlooredSourceTimeData` exists.  It packages the time-Leibniz chain, joint continuity of the derivative slices, space-`C²` Neumann regularity of the three time-order slices, and the zeroth/Laplacian coefficient bounds.

So proving resolver coefficient `C²` directly is equivalent to proving a lighter, resolver-specific version of `FlooredSourceTimeData` / `PhysicalSourceTimeC2`.

## Important local/global caveat

`boundedWeightJointSeries_contDiff_two` is a **global** `ContDiff` theorem for the uncut series.  For the heat semigroup on a positive window `[c,T]`, raw exponential coefficients are well-behaved only after localizing away from `t = 0` / negative time.  The heat semigroup joint-regularity file solves this with a smooth time cutoff.

So for a heat-semigroup standalone theorem, there are two viable designs:

### Option A: produce `PhysicalResolverJointC2Data` under a globally smooth/cutoff coefficient family

This fits the existing consumer API but may require defining a cutoff heat trajectory or proving enough global-in-time bounds.

### Option B: prove a positive-window/local resolver theorem directly

This is likely shorter for level 0:

```lean
theorem heatResolver_jointContDiffAt_two_direct
    {c T : ℝ} (hc : 0 < c) ...
    {s x : ℝ} (hs : c < s) (hx : x ∈ Ioo (0:ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1) q.2) (s, x) := by
  -- use cutoff/localized resolver coefficients
  -- feed boundedWeightJointSeries_contDiff_two to the cutoff series
  -- use eventual equality near `(s,x)` to return to the real resolver series
```

This mirrors `heatSemigroup_jointContDiffAt_two`: prove global `ContDiff` of a cutoff series, then use eventual equality near positive `s`.

## Recommendation

For a standalone heat-semigroup result, do **not** route through `DuhamelSourceTimeC2Coeff` or the old eigen-cube ladder.

The shortest robust plan is:

1. Define the heat-level resolver coefficient family, preferably reusing
   `resolverTimeCoeff p (conjugatePicardIter p u₀ 0)`.
2. Prove a heat/window coefficient package:
   `ContDiff`/`ContDiffAt` in time up to order 2 plus bounded-weight summable majorants.
3. Feed that package directly to `boundedWeightJointSeries_contDiff_two` (value) and `boundedWeightJointGradSeries_contDiff_two` (gradient), using a cutoff if the theorem is local on `s > c`.
4. If downstream wants existing FAC lemmas, wrap the same package as `PhysicalResolverJointC2Data`; otherwise inline the assembler in a local direct theorem.

Bottom line: **direct feeding is technically valid and may be the right level-0 shortcut, but it does not eliminate the source coefficient time-`C²` problem.  It replaces `FlooredSourceTimeData` with an equivalent heat-specific coefficient package.**
