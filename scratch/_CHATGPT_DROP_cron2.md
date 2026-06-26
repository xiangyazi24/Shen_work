# Q744 (cron2): `CoupledChemDivFluxJointC2Hyp` at `τ ≤ 0`

Static repo inspection only; I did not run a Lean build.

## Executive verdict

`CoupledChemDivFluxJointC2Hyp` is a genuinely **global** package:

```lean
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ...
```

So if you construct this exact structure, Lean requires fields for **every** `τ : ℝ`, including `τ ≤ 0`.  The fields are not vacuous at `τ ≤ 0`: `Metric.ball τ δ` contains `τ` itself, and the closed slab `Icc (τ - δ) (τ + δ) ×ˢ Icc 0 1` is nonempty.  Choosing `δ = 1` does not make the obligations trivial.

For the heat-level-0 situation, `δ = 1` at `τ ≤ 0` is especially suspect because:

* for `τ` near `0`, the ball crosses the bad `t = 0` wall;
* the concrete full heat semigroup has the degenerate value `S(0)f = 0`, not `f`;
* positive-time smoothing/positivity lemmas generally require `0 < s`;
* the current comments claiming “S(s)u₀ is jointly C∞ for s > 0” do not justify a slab crossing `s = 0` or negative times.

The downstream target in `level0_chemDiv_timeDerivData` is only on `[c,T]` with `0 < c`, so **mathematically the `τ ≤ 0` parts should be unnecessary**.  But the current code routes through global structures and even defines a global `hderiv_global : ∀ s n, HasDerivAt ...`, which calls `hchain.exists_local_slab s` for arbitrary `s`.  That current route makes the `τ ≤ 0` obligations syntactically part of the proof.

Recommended fix: do **not** try to prove a global `CoupledChemDivFluxJointC2Hyp` for the heat semigroup unless you really want to solve the wall/negative-time behavior.  Instead, prove a positive-window/local version, or inline the chain-rule argument only for `s ∈ Icc c T`, choosing local radii inside positive time such as `δ ≤ s / 2`.  If you leave `sorry`s, you can of course put a `by sorry` branch for `τ ≤ 0`, but that is a real axiom placeholder, not a trivial/degenerate slab.

## Definition: global nature of `CoupledChemDivFluxJointC2Hyp`

File:

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

The structure is:

```lean
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun r : ℝ => deriv (coupledChemDivFluxLift p u r) x) =ᶠ[𝓝 s]
        (fun r : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (r, x) (0, 1))) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

The five/final fields are real analytic content.  They are not logically vacuous for `τ ≤ 0`.

## How `FluxJointC2Hyp` is consumed

Same file:

```lean
theorem coupledChemDivOuterCommuteAtoms_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivOuterCommuteAtoms p u := by
  refine ⟨fun τ => ?_⟩
  rcases H.exists_local_slab τ with
    ⟨δ, hδ, hsource_cont, hflux_c2, hspatial, htime, htime_cont⟩
  ...
```

Then:

```lean
theorem coupledChemDivLocalChainRule_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivLocalChainRule p u :=
  coupledChemDivLocalChainRule_of_outerCommuteAtoms
    (coupledChemDivOuterCommuteAtoms_of_fluxJointC2 H)
```

So the global `∀ τ` is preserved into `CoupledChemDivLocalChainRule`.

## How `CoupledChemDivLocalChainRule` is used

File:

```text
ShenWork/PDE/IntervalChemDivTimeDerivative.lean
```

`CoupledChemDivLocalChainRule` is also global:

```lean
structure CoupledChemDivLocalChainRule
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ...
```

The global source-time-C¹ producer uses it globally:

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_fields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (F : CoupledChemDivTimeC1Fields p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s := by
  rcases F.hchain.exists_local_slab s with
    ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
  exact
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
      ...
```

And `coupledChemDivSource_timeC1_of_fields` builds a global:

```lean
DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u)
```

by proving `∀ s n, HasDerivAt ...`.

File:

```text
ShenWork/Wiener/EWA/ChemDivAdot.lean
```

The same global pattern appears there:

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (s : ℝ) (n : ℕ) :
    HasDerivAt ... := by
  rcases hchain.exists_local_slab s with
    ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
  ...
```

Then the windowed derivative theorem restricts that global `HasDerivAt` to `[0,T]` via `.hasDerivWithinAt`.

## Current Level0 code path

File:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

Inside `level0_chemDiv_timeDerivData`, the target is windowed:

```lean
∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
  (∀ s ∈ Icc c T, ∀ n,
    HasDerivWithinAt
      (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
      (adot s n) (Icc c T) s) ∧
  ...
```

with `0 < c`.

But the current proof attempts to build a global `CoupledChemDivFluxJointC2Hyp`:

```lean
have hfluxC2 : CoupledChemDivFluxJointC2Hyp
    p (conjugatePicardIter p u₀ 0) := by
  apply coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
  refine ⟨fun τ => ?_⟩
  refine ⟨1, one_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
```

That is where the `τ ≤ 0` problem enters.

The proof later uses `hchain.exists_local_slab` only at positive-window points for the joint-continuity step:

```lean
intro ⟨s, x⟩ hsx
obtain ⟨hs, hx⟩ := mem_prod.1 hsx
rcases hchain.exists_local_slab s with ⟨δ, hδ, _, _, hcont⟩
```

Here `s ∈ Icc c T`, so `s ≥ c > 0`.

However, it also introduces:

```lean
have hderiv_global : ∀ s n,
    HasDerivAt
      (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
      (adot s n) s := by
  intro s n
  rcases hchain.exists_local_slab s with ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
  ...
```

That statement calls `hchain.exists_local_slab s` for arbitrary `s : ℝ`.  So in the current proof skeleton, the global `τ ≤ 0` fields are not merely hidden in the structure: they are also forced by `hderiv_global`, even though the final target only uses `s ∈ Icc c T`.

This can be refactored.  Instead of proving `hderiv_global : ∀ s n`, prove only:

```lean
have hderiv : ∀ s ∈ Icc c T, ∀ n,
    HasDerivWithinAt ... (Icc c T) s := by
  intro s hs n
  -- now `0 < s` follows from `hc` and `hs.1`
  -- obtain a positive-time local slab at `s`, with δ ≤ s/2, and apply the same local theorem
```

Then the proof only queries slabs at positive `s`.

## Can `τ ≤ 0` be filled with a trivial/degenerate slab?

### If using `sorry`

Yes, syntactically you can branch on `τ ≤ 0` and put `sorry` there.  Lean will accept it.  But that is not a trivial proof; it is an axiom placeholder for nontrivial or possibly false regularity across/near the `t = 0` wall.

### Without `sorry`

No, not by just choosing `δ = 1`.

Reasons:

1. `Metric.ball τ 1` is nonempty and contains `τ`.
2. If `τ = 0`, every `δ > 0` crosses positive and nonpositive times.
3. The concrete heat semigroup has `S(0)f = 0`, not `f`, so continuity/smoothness through `0` is not automatic and is generally suspect for nonzero data.
4. The intended heat smoothness facts are positive-time facts.
5. `ContinuousOn (Function.uncurry (...)) (Icc (τ - δ) (τ + δ) ×ˢ Icc 0 1)` is a real closed-slab continuity statement; it is not vacuous.

For `τ < 0`, a degenerate/zero route might be possible if one proves that the concrete heat semigroup and all relevant derived fields are identically zero on a sufficiently small negative-time slab.  But that is not currently landed in the files I inspected, and it would still fail to cover `τ = 0` without a real wall argument.

## Recommended route

Do not use the global `CoupledChemDivFluxJointC2Hyp` as the Level0 heat proof vehicle unless you are prepared to solve all-time regularity.

Instead, introduce a positive-window/local version, e.g. conceptually:

```lean
structure CoupledChemDivFluxJointC2HypOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c T : ℝ) : Prop where
  exists_local_slab_on : ∀ τ ∈ Icc c T, ∃ δ : ℝ, 0 < δ ∧
    δ ≤ τ / 2 ∧
    -- same local fields, with balls/slabs now contained in positive time
```

or do not introduce a structure at all: inline the local slab proof inside `level0_chemDiv_timeDerivData` for each `s ∈ Icc c T`.

The key local-radius move is:

```lean
have hs_pos : 0 < s := lt_of_lt_of_le hc hs.1
let δ := min 1 (s / 2)
```

or similar, so that `r ∈ Metric.ball s δ` implies `0 < r`.

Then apply the positive-time heat/resolver regularity facts only where they are valid.

## Bottom line

* `CoupledChemDivFluxJointC2Hyp` requires nontrivial data for all `τ : ℝ`.
* The existing conversion to `CoupledChemDivLocalChainRule` preserves the global `∀ τ`.
* Some existing consumers (`coupledChemDivCoeff_hasDerivAt_of_fields`, `coupledChemDivCoeff_hasDerivAt_of_chainRule`) explicitly call `exists_local_slab s` for arbitrary `s` to produce global `HasDerivAt`.
* In the current Level0 proof, the final target is only `[c,T]` with `0 < c`, but the skeleton unnecessarily creates global packages and a global derivative theorem.
* A `τ ≤ 0` branch with `δ = 1` is not mathematically trivial.  It can be `sorry`ed, but that is a real placeholder, not a safe degenerate slab.
* Best fix: refactor to a positive-window/local chain-rule proof and avoid constructing `CoupledChemDivFluxJointC2Hyp` globally for heat level 0.
