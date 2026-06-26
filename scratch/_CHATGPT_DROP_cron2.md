# Q768 (cron2): Sub-sorry 3A, eventual source continuity

Static repo inspection only; I did not run a Lean build.

## Answer

Yes: if you can prove the per-slice statement for **all** `s`, then the `∀ᶠ s in 𝓝 τ` field is immediate.

The Lean shape should be one of:

```lean
have hsrc_all : ∀ s : ℝ,
    ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1) := by
  ...

have hsrc_ev :
    ∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1) :=
  Filter.Eventually.of_forall hsrc_all
```

or equivalently:

```lean
filter_upwards with s using hsrc_all s
```

I did **not** find repo uses of a lowercase `Filter.eventually_of_forall`; existing code uses the constructor form:

```lean
Filter.Eventually.of_forall
```

So I would use that spelling.

If you only prove the positive-time statement,

```lean
∀ s, 0 < s → ContinuousOn ...
```

then that only gives the eventual statement at `τ > 0`, via `Ioi_mem_nhds` / a positive neighborhood. It does **not** handle arbitrary `τ`, especially `τ ≤ 0`. For the global `CoupledChemDivFluxJointC2Hyp` / FAC slab shape, `τ` is arbitrary, so an all-`s` proof, or a separate nonpositive-time branch, is needed.

For your proposed heat route, the all-`s` reduction is sound **provided** the actual Level0 trajectory really is the zeroed heat semigroup for `s ≤ 0` in the relevant definition. Then the structure is:

```lean
have hsrc_all : ∀ s : ℝ,
    ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1) := by
  intro s
  by_cases hs : 0 < s
  · -- heat smoothing: S(s)u₀ smooth, resolver smooth/regular, chemDiv source continuous
    ...
  · -- nonpositive-time branch: u s = 0, resolver/source simplify to 0
    ...

exact Filter.Eventually.of_forall hsrc_all
```

## Does the repo already have a per-slice continuity producer for `coupledChemDivSourceLift`?

I did **not** find a named direct theorem of the form:

```lean
∀ s, ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)
```

or

```lean
ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)
```

Searches for `coupledChemDivSourceLift_continuousOn`, `coupledChemDivSourceLift ContinuousOn`, and quoted `ContinuousOn (coupledChemDivSourceLift` turned up mostly structures/assemblers where this is still an **input field**, not a producer.

The key definition is:

```lean
def coupledChemDivSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (fun x => intervalDomainChemotaxisDiv p (u s)
      (coupledChemicalConcentration p u s) x)
```

File:

```text
ShenWork/PDE/IntervalCoupledSourceTimeC1.lean
```

And the FAC local slab package still carries the 3A field explicitly:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
```

File:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
```

Likewise, the global chain-rule / flux packages carry the same source-continuity field as part of their local slab data, rather than deriving it internally:

```text
ShenWork/PDE/IntervalChemDivTimeDerivative.lean
ShenWork/PDE/IntervalChemDivOuterCommute.lean
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

## Nearby partial tools

The closest per-slice spatial regularity tool is:

```lean
chemDivLift_contDiffOn_two_of_global
```

File:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

It proves:

```lean
ContDiffOn ℝ 2 (chemDivLift p u v) (Icc (0 : ℝ) 1)
```

from global `C⁴` of the lifted `u` and `v` profiles plus positivity of `1+v`. This immediately implies continuity via `.continuousOn`, but it is stated for the per-slice `chemDivLift p u v`, not directly for `coupledChemDivSourceLift p u s`. You would still need the bridge/unfolding step identifying the slice

```lean
coupledChemDivSourceLift p u s
```

with the corresponding `chemDivLift p (u s) (coupledChemicalConcentration p u s)` on `Icc 0 1`.

Other nearby tools consume continuity as a hypothesis rather than producing it, e.g.

```lean
coupledChemDivSource_zeroCoeff_of_uniformSup
```

in

```text
ShenWork/PDE/IntervalChemDivFluxFACSourceDecay.lean
```

requires:

```lean
hcont : ∀ s, 0 ≤ s →
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)
```

## Practical conclusion

For sub-sorry 3A, the fastest Lean shape is probably not to build a new “eventual” proof directly. Prove an all-slices lemma first:

```lean
theorem level0_coupledChemDivSourceLift_continuousOn_all_s
    ... :
    ∀ s : ℝ,
      ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
        (Icc (0 : ℝ) 1) := by
  intro s
  by_cases hs : 0 < s
  · -- positive smoothing route
  · -- nonpositive zero route
```

Then the FAC/FluxJointC2Hyp 3A field is just:

```lean
exact Filter.Eventually.of_forall level0_coupledChemDivSourceLift_continuousOn_all_s
```

or inline:

```lean
filter_upwards with s
exact level0_coupledChemDivSourceLift_continuousOn_all_s s
```
