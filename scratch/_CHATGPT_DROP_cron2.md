# Q1484 (cron2) — `grad_summable` needs quartic source decay

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

Your diagnosis is correct: the current `builtEs` constructed from `FlooredSourceTimeData.laplBound` has only `(kπ)⁻²` decay, and that is **not sufficient** for the source-side `grad_summable` obligation

```lean
Summable (boundedWeightJointGradMajorant
  (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)
```

at `m = 2`.

The best fix is **not** to try to prove the old `builtEs` goal. That goal is false by asymptotics. The correct route is to strengthen the source envelope used by `PhysicalSourceTimeC2`: add a quartic-decay field to `FlooredSourceTimeData` (or equivalently introduce a new `builtEs4` and use that instead of the old `builtEs`). In the current API, a pure “direct bypass” of `builtEs` is not type-correct unless it replaces the envelope `Es` used to build `PhysicalSourceTimeC2`.

## What the repo currently says

The relevant source-side structure is in:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

There, `FlooredSourceTimeData` contains:

```lean
zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t →
  |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D

laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
  |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

and `builtEs` is exactly the zeroth-mode bound at `k = 0`, otherwise the `(kπ)⁻²` `laplBound` envelope:

```lean
def builtEs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) : ℝ :=
  if hi : i ≤ 2 then
    (if k = 0 then Classical.choose (H.zerothBound i hi)
     else Classical.choose (H.laplBound i hi) / ((k:ℝ) * Real.pi) ^ 2)
  else 0
```

Then `physicalSourceTimeC2_of_floored` requires both value and gradient summability for exactly this envelope:

```lean
(hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointMajorant
    (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
(hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
  Summable (boundedWeightJointGradMajorant
    (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
```

So the current theorem does **not** derive `grad_summable`; it asks for it as a hypothesis. The remaining `sorry` in `IntervalHeatSemigroupHighRegularity.lean` currently has a misleading comment saying the gradient summability follows from `(kπ)⁻²` plus the elliptic weight. That comment is wrong.

## The divergent term

The gradient majorant is defined in:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

as

```lean
def boundedWeightJointGradMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * gradCosWeight (k - i) n
```

The repo already expands the `m = 2` case in:

```text
ShenWork/PDE/IntervalIterateGradMajorant.lean
```

as

```lean
boundedWeightJointGradMajorant Bt 2 k
  = |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k
    + 2 * (unitIntervalCosineEigenvalue k * Bt 1 k)
    + |(k : ℝ) * Real.pi| * Bt 2 k
```

For the source/resolver envelope, `Bt i k = w_k * builtEs H i k`, where

```lean
w_k = intervalNeumannResolverWeight p k ≈ 1 / (kπ)^2.
```

With the current `builtEs H 0 k = O((kπ)⁻²)`, the worst `m = 2`, `i = 0` term is

```text
|kπ| * λ_k * w_k * builtEs H 0 k
  ≈ |kπ| * (kπ)^2 * (kπ)^-2 * (kπ)^-2
  = O(k^-1),
```

so the series diverges. Equivalently, using your notation:

```text
wk * builtEs * gradCosWeight(2,k)
  = O(k^-2) * O(k^-2) * O(k^3)
  = O(k^-1).
```

Thus the old `hgrad` target for `builtEs` is not merely hard; it is mathematically false.

## What other `grad_summable` proofs do

The repo pattern is already the right one: gradient summability is treated as an honest stronger leg, not something obtained from value summability.

In `IntervalIterateGradMajorant.lean`, the comment explicitly says the order-2 gradient majorant carries one extra `|kπ|` weight and cannot be supplied by the committed value majorant. The file provides:

```lean
theorem grad2_summable_of_components {Bt : ℕ → ℕ → ℝ}
    (h0 : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k))
    (h1 : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Bt 1 k))
    (h2 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 2 k)) :
    Summable (boundedWeightJointGradMajorant Bt 2)
```

In `IntervalIterateGradSummableFromSourceL1.lean`, the proof goes further and expands all `m ≤ 2` cases into explicit weighted summability assumptions:

```lean
theorem iterate_gradSummable_of_weightedBtuSummable {Btu : ℕ → ℕ → ℝ}
    (s0 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 0 k))
    (s1a : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 0 k))
    (s1 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 1 k))
    (s2a : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Btu 0 k))
    (s2b : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 1 k))
    (s2c : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 2 k)) :
    ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Btu m)
```

So there is no existing repo pattern where an order-2 gradient majorant is honestly proved from only an order-2 value/Laplacian envelope. The pattern is: expand the gradient weights and feed stronger weighted summability.

## Existing quartic tool

The repo already has the right analytic lemma in:

```text
ShenWork/PDE/IntervalSourceDecayQuantitative.lean
```

namely:

```lean
theorem intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv)
    {B₂ : ℝ} (hB₂ : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) ≤ B₂) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4
```

and also:

```lean
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|)
```

For the current source-side `builtEs` problem, the first theorem is the more directly useful one because it gives an explicit uniform quartic coefficient envelope.

## Recommendation

Extend `FlooredSourceTimeData` with a `quartBound` field and make the envelope used by `PhysicalSourceTimeC2` quartic on nonzero modes.

Do **not** leave `builtEs` as the `(kπ)⁻²` envelope and try to “bypass” it only inside `hgrad`: the type of `hgrad` is about the specific function `fun i k => w_k * builtEs H i k`. If `builtEs` remains quadratic, the goal is false. A bypass is only viable if it introduces a different envelope, say `builtEs4`, and uses `PhysicalSourceTimeC2 p u builtEs4`; that is essentially the same design as extending `FlooredSourceTimeData` with quartic data.

The least disruptive patch is:

1. Keep `laplBound` for the existing C²/IBP bookkeeping.
2. Add `quartBound` for each time-slice `i ≤ 2`.
3. Redefine `builtEs` to use `quartBound` for `k ≥ 1`, or define a new `builtEs4` and migrate `physicalSourceTimeC2_of_floored` callers to it.
4. Prove `value_summable` and `grad_summable` from the quartic envelope using `λ_k * w_k ≤ 1`, `w_k ≤ 1 / μ`, and p-series comparisons.
5. Update `IterateSourceTimeData` and `heatSemigroup_flooredSourceTimeData` constructors to carry/pass the new quartic bound.

## Patch shape

A direct structural patch looks like this.

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalSourceDecayQuantitative

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  d0 : ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s) ∧
    ContinuousOn (Function.uncurry s₁) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  d1 : ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (s₁ s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => s₁ r x) (s₂ s x) s) ∧
    ContinuousOn (Function.uncurry s₂) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t →
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0:ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t →
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 1 = 0
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
  /-- New field: the nonzero-mode quartic envelope needed by `grad_summable`. -/
  quartBound : ∀ i : ℕ, i ≤ 2 → ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ Q / ((k:ℝ) * Real.pi) ^ 4

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

Then either replace `builtEs` or introduce `builtEs4`. If you want the smallest API churn, redefine `builtEs` itself:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- Quartic source envelope: zeroth mode handled separately, nonzero modes use the
new `quartBound`.  This is the envelope that can honestly feed both value and
order-2 gradient majorants after the elliptic resolver weight is folded in. -/
def builtEs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) : ℝ :=
  if hi : i ≤ 2 then
    if hk : k = 0 then
      Classical.choose (H.zerothBound i hi)
    else
      Classical.choose (H.quartBound i hi) / ((k : ℝ) * Real.pi) ^ 4
  else 0

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

Then `srcTimeCoeff_bound` should use `quartBound` in the nonzero case:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

-- In the existing proof of `srcTimeCoeff_bound`, replace the nonzero-mode branch by:
--
--   · rw [if_neg (Nat.pos_iff_ne_zero.mp hk)]
--     exact (Classical.choose_spec (H.quartBound i hi)).2 t ht k hk
--
-- The zeroth-mode branch remains unchanged.

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

If you want to preserve the old quadratic `builtEs` for other users, use this naming instead:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- Old quadratic envelope, useful only for value/C² bookkeeping. -/
def builtEs2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) : ℝ :=
  if hi : i ≤ 2 then
    if k = 0 then Classical.choose (H.zerothBound i hi)
    else Classical.choose (H.laplBound i hi) / ((k:ℝ) * Real.pi) ^ 2
  else 0

/-- New quartic envelope, required for `grad_summable`. -/
def builtEs4
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) : ℝ :=
  if hi : i ≤ 2 then
    if k = 0 then Classical.choose (H.zerothBound i hi)
    else Classical.choose (H.quartBound i hi) / ((k:ℝ) * Real.pi) ^ 4
  else 0

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

The latter is slightly cleaner mathematically but requires changing callers of `physicalSourceTimeC2_of_floored` to use `builtEs4`, or adding a parallel theorem `physicalSourceTimeC2_of_floored_quartic`.

## Summability proof plan for the quartic envelope

Let

```lean
Bt i k = intervalNeumannResolverWeight p k * builtEs4 H i k.
```

For `k ≥ 1`, the quartic bound gives

```text
builtEs4 H i k ≤ Q_i / (kπ)^4 = Q_i / λ_k^2.
```

Use the existing resolver-weight facts:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one
ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu
```

The hardest `m = 2` gradient pieces become:

```text
i = 0: |kπ| * λ_k * w_k * Q_0 / λ_k^2
       ≤ |kπ| * Q_0 / λ_k^2
       = O(k^-3)

i = 1: λ_k * w_k * Q_1 / λ_k^2
       ≤ Q_1 / λ_k^2
       = O(k^-4)

i = 2: |kπ| * w_k * Q_2 / λ_k^2
       ≤ (1/μ) * |kπ| * Q_2 / λ_k^2
       = O(k^-3)
```

All are summable. The `m = 0` and `m = 1` cases are easier.

This should be packaged as a generic helper, analogous to the iterate-side helper in `IntervalIterateGradSummableFromSourceL1.lean`:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

open ShenWork.PDE (intervalNeumannResolverWeight)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointGradMajorant)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (eigenvalue_mul_resolverWeight_le_one resolverWeight_le_inv_mu)

/-- Sketch theorem: quartic source envelope plus elliptic resolver weight gives all
bounded-weight gradient majorant summability for orders `m ≤ 2`.

Implementation should split `m = 0,1,2`, expand the finite sums as in
`IntervalIterateGradSummableFromSourceL1.lean`, handle `k = 0` separately, and
compare the positive modes to `C * (1 / (k : ℝ)^3)` or `C * (1 / (k : ℝ)^4)`. -/
theorem weighted_quartic_builtEs_grad_summable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) :
    ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m) := by
  intro m hm
  -- Proof shape:
  --   1. `have hm2 : m ≤ 2 := by exact_mod_cast hm`.
  --   2. `interval_cases m`.
  --   3. Expand `boundedWeightJointGradMajorant` for m = 0,1,2.
  --   4. For each component, split k = 0 / k ≥ 1.
  --   5. Use `Classical.choose_spec (H.quartBound i hi)` to get the constant Q_i.
  --   6. Use `eigenvalue_mul_resolverWeight_le_one p k` for terms with a λ_k factor.
  --   7. Use `resolverWeight_le_inv_mu p k` for terms without enough λ cancellation.
  --   8. Compare to `Real.summable_one_div_nat_pow` with p = 3 or p = 4.
  sorry

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

The corresponding value summability helper is easier, because the value majorant has at most `λ_k` spatial growth, not `|kπ| * λ_k`.

## Constructor updates needed

Adding `quartBound` to `FlooredSourceTimeData` will force updates in at least these places:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

For the iterate-side wrapper, extend `IterateSourceTimeData` with a matching field:

```lean
quartBound : ∀ i : ℕ, i ≤ 2 → ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
  |cosineCoeffs ((sliceFam (srcSlice p u) (srcSlice1 p u du)
    (srcSlice2 p u du d2u) i) t) k| ≤ Q / ((k:ℝ) * Real.pi) ^ 4
```

and pass it through in `flooredSourceTimeData_of_iterate`:

```lean
quartBound i hi := by
  obtain ⟨Q, hQ, hb⟩ := H.quartBound i hi
  exact ⟨Q, hQ, fun t _ht k hk => hb t k hk⟩
```

For the heat-semigroup level-0 constructor, add an input `hquartBound` next to `hlaplBound` and assign it to the new field.

The actual source of `hquartBound` should be the existing H4 route:

```lean
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
```

applied to each time-derivative slice `i = 0,1,2` at positive time. Analytically, this means each slice needs a uniform-in-positive-time weak-H4 Neumann tower / fourth-derivative L¹ envelope. That is exactly the missing regularity strength; `sliceC2 + sliceNeumann + laplBound` is not enough.

## Final answer to the design question

Extend `FlooredSourceTimeData` with `quartBound` and make the physical source envelope quartic for nonzero modes. That is the cleanest and most type-compatible repair.

A “direct O(k⁻⁴) bypass” is only acceptable if it means replacing the envelope passed to `PhysicalSourceTimeC2` by a quartic envelope (`builtEs4`). It should **not** mean keeping the old quadratic `builtEs` and trying to prove `hgrad` anyway.

So the recommended patch is:

```text
FlooredSourceTimeData.laplBound    -- keep: C² / old bookkeeping
FlooredSourceTimeData.quartBound   -- add: H4 / gradient summability
builtEs or builtEs4                -- use quartBound for k ≥ 1
physicalSourceTimeC2_of_floored    -- consume quartic envelope
heatSemigroup_level0_resolverJointC2Data.grad_summable
                                   -- prove from quartic, not laplacian
```

This matches the repo’s existing philosophy: gradient summability is an honest stronger leg, just as `IntervalIterateGradMajorant.lean` and `IntervalIterateGradSummableFromSourceL1.lean` already encode on the iterate side.
