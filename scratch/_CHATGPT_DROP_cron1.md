# Q1705 (cron1) -- `srcSlice` / `srcTimeCoeff` positive-time obstruction

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt I received was only:

```text
Q1705 (cron1): cron1 /tmp/q_cron1_srcslice.txt
```

The local file `/tmp/q_cron1_srcslice.txt` is not accessible through the GitHub connector. I used the connector only and inferred the target from the current `cron1` source-side C² thread in the repository. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link. I did not run Lean locally.

The relevant files are:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
ShenWork/Paper2/IntervalConjugatePicard.lean
ShenWork/PDE/IntervalNeumannFullKernel.lean
ShenWork/PDE/HeatSemigroup.lean
```

## Short answer

The `srcSlice` definition itself is fine:

```lean
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ
```

and the committed bridge is:

```lean
theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k
```

The obstruction is not `srcSlice`; it is a quantifier mismatch.

`FlooredSourceTimeData` now carries only **positive-time** information:

```lean
sliceC2      : ∀ i ≤ 2, ∀ t, 0 < t → ...
sliceNeumann : ∀ i ≤ 2, ∀ t, 0 < t → ...
zerothBound  : ∀ i ≤ 2, ∃ D, 0 ≤ D ∧ ∀ t, 0 < t → ...
laplBound    : ∀ i ≤ 2, ∃ M, 0 ≤ M ∧ ∀ t, 0 < t → ...
```

but `PhysicalSourceTimeC2` still asks for **global-in-time** data:

```lean
src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
src_bound    : ∀ i k t, i ≤ 2 →
  ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
```

So `physicalSourceTimeC2_of_floored` cannot honestly close its current `src_contDiff` and `src_bound` fields from `FlooredSourceTimeData` as stated.

## The key point about `t ≤ 0`

For the **heat level-0 iterate** only,

```lean
conjugatePicardIter p u₀ 0 t x
```

unfolds to:

```lean
intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

The heat kernel is defined without an `if 0 < t` guard:

```lean
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))
```

In Lean, for `t ≤ 0`, the factor `Real.sqrt (4 * Real.pi * t)` is `0`; hence `1 / 0 = 0`, so the whole `heatKernel t x` term reduces to `0`. Therefore, for the heat level-0 iterate, one can prove:

```lean
intervalFullSemigroupOperator t (intervalDomainLift u₀) x = 0
```

for `t ≤ 0`, and consequently:

```lean
srcSlice p (conjugatePicardIter p u₀ 0) t x = 0
srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t = 0
```

for `t ≤ 0`, using `p.hγ : 0 < p.γ` to rewrite `0 ^ p.γ = 0`.

But this does **not** solve `src_contDiff : ContDiff ℝ 2 ...` globally. At `t = 0`, the heat level-0 extension is generally discontinuous: from the left it is zero, while from the right it tends to the initial datum `u₀` (and hence the source tends to `ν·u₀^γ`). Unless `u₀` is specially zero, global `ContDiff` across `0` is false.

So:

* For `t < 0`, the source coefficient is locally zero, so derivative bounds are mechanical.
* For `t > 0`, the existing `srcTimeCoeff_bound H i k t hi ht` applies.
* At `t = 0`, global `ContDiff` is the real obstruction.
* For **abstract** `u`, even the `t ≤ 0` zero fact is unavailable; it only holds after specializing to `u = conjugatePicardIter p u₀ 0`.

## Nonpositive-time helper lemmas for heat level 0

These are the helper lemmas I would add only if you specifically need to reason about the nonpositive half-line for the level-0 heat iterate. They are **not** enough to prove the current global `PhysicalSourceTimeC2`, but they explain the `srcSlice` behavior.

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.Paper2.IntervalConjugatePicard

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalNeumannFullKernel intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete
  (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)

namespace ShenWork.Paper2.Cron1SrcSlice

lemma heatKernel_eq_zero_of_nonpos {t x : ℝ} (ht : t ≤ 0) :
    heatKernel t x = 0 := by
  unfold heatKernel
  have hnonpos : 4 * Real.pi * t ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4 * Real.pi) ht
  rw [Real.sqrt_eq_zero_of_nonpos hnonpos]
  simp

lemma intervalNeumannFullKernel_eq_zero_of_nonpos {t x y : ℝ} (ht : t ≤ 0) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  simp [heatKernel_eq_zero_of_nonpos ht]

lemma intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_eq_zero_of_nonpos ht]

lemma conjugatePicardIter_level0_eq_zero_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (ht : t ≤ 0) (x : intervalDomainPoint) :
    conjugatePicardIter p u₀ 0 t x = 0 := by
  simp [conjugatePicardIter,
    intervalFullSemigroupOperator_eq_zero_of_nonpos ht]

lemma intervalDomainLift_level0_eq_zero_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = 0 := by
  unfold intervalDomainLift
  split_ifs with hx
  · exact conjugatePicardIter_level0_eq_zero_of_nonpos p u₀ ht ⟨x, hx⟩
  · rfl

lemma srcSlice_level0_eq_zero_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    srcSlice p (conjugatePicardIter p u₀ 0) t x = 0 := by
  unfold srcSlice
  rw [intervalDomainLift_level0_eq_zero_of_nonpos p u₀ ht x]
  have hγne : p.γ ≠ 0 := ne_of_gt p.hγ
  simp [Real.zero_rpow hγne]

lemma srcTimeCoeff_level0_eq_zero_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (ht : t ≤ 0) (k : ℕ) :
    srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t = 0 := by
  rw [srcTimeCoeff_eq_cosineCoeffs]
  have hslice : srcSlice p (conjugatePicardIter p u₀ 0) t = fun _ => 0 := by
    funext x
    exact srcSlice_level0_eq_zero_of_nonpos p u₀ ht x
  rw [hslice]
  -- Depending on the local simp set, either `simp [cosineCoeffs]` closes this,
  -- or unfold `cosineCoeffs`, `unitIntervalNeumannCosineCoeff`, and
  -- `unitIntervalCosineRawCoeff`, then use integral of zero.
  simp [cosineCoeffs]

end ShenWork.Paper2.Cron1SrcSlice
```

Possible elaboration notes:

* If `Real.sqrt_eq_zero_of_nonpos` has a slightly different local name in the current Mathlib, search for `sqrt_eq_zero_of_nonpos` / `Real.sqrt_eq_zero`.
* If `simp [cosineCoeffs]` does not close the zero-coefficient lemma, unfold through `unitIntervalNeumannCosineCoeff` and `unitIntervalCosineRawCoeff`; the integrand is definitionally zero.

## Why the generic theorem cannot use those lemmas

The theorem with the current sorries is generic:

```lean
theorem physicalSourceTimeC2_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    ... :
    PhysicalSourceTimeC2 p u (builtEs H) where
  src_contDiff k := by
    sorry
  src_bound i k t hi := by
    sorry
```

Here `u` is arbitrary. `FlooredSourceTimeData` only gives positive-time facts. It does **not** say that `u t = 0` for `t ≤ 0`, nor that `srcTimeCoeff p u k` is smooth across `0`. Therefore the nonpositive-time lemmas above cannot fill this generic theorem.

A counterexample-shaped obstruction is: choose an arbitrary `u` whose positive-time behavior satisfies the positive-time fields but whose nonpositive-time behavior is discontinuous or unbounded. The current `FlooredSourceTimeData` fields do not control that behavior. Thus the current generic conclusion is stronger than the hypotheses.

## Correct structural fix

The clean fix is to make the source/resolver physical data positive-time/local, or to move the smooth cutoff into the coefficients before demanding global `ContDiff`.

### Option A: positive-time physical source data

Replace global source fields with positive-time fields:

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointGradMajorant)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

structure PhysicalSourceTimeC2Pos
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  src_contDiffAt_pos : ∀ k : ℕ, ∀ {t : ℝ}, 0 < t →
    ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t
  src_bound_pos : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 → 0 < t →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant
      (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k * Es i k) m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant
      (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k * Es i k) m)

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

Then the producer from `FlooredSourceTimeData` is honest and direct:

```lean
theorem physicalSourceTimeC2Pos_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2Pos p u (builtEs H) where
  src_contDiffAt_pos k ht := srcTimeCoeff_contDiffAt H k ht
  src_bound_pos i k t hi ht := srcTimeCoeff_bound H i k t hi ht
  value_summable := hval
  grad_summable := hgrad
```

This matches the actual available theorem:

```lean
srcTimeCoeff_contDiffAt H k ht
srcTimeCoeff_bound H i k t hi ht
```

### Option B: cutoff the coefficient before asking for global `ContDiff`

If the downstream assembler really wants global `ContDiff ℝ 2`, do not use raw `srcTimeCoeff`. Use the cutoff coefficient:

```lean
def cutoffSrcTimeCoeff
    (c : ℝ) (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) :
    ℝ → ℝ :=
  fun t => smoothRightCutoff (c / 2) c t * srcTimeCoeff p u k t
```

For `c > 0`, this coefficient is identically zero near `t ≤ c/2`, including a whole neighborhood of `0`. On `t > c/2`, all times are positive, so `srcTimeCoeff_contDiffAt` and `srcTimeCoeff_bound` apply. This is the same structural reason the cutoff resolver proof is the right route.

This option is usually better for `contDiff_tsum`, because the global theorem is then true for the cutoff series even though the raw heat semigroup is not globally smooth at `t = 0`.

## What not to do

Do not try to prove:

```lean
ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k)
```

for the raw level-0 heat iterate on all of `ℝ`. The current definition makes the negative-time side zero and the positive-time side the heat semigroup source. At `t = 0`, this is not a smooth gluing in general.

Also do not try to fill the generic `physicalSourceTimeC2_of_floored` by unfolding `intervalFullSemigroupOperator`: that theorem is generic in `u`, so there is no semigroup definition to unfold.

## Recommended patch direction

For the current cron1 lane, the best patch is:

1. Keep `FlooredSourceTimeData` positive-time only.
2. Replace the global `PhysicalSourceTimeC2` producer by a positive-time/local producer, or introduce a cutoff-source physical data structure.
3. Use cutoff coefficients to feed any global `contDiff_tsum` assembler.
4. Use the nonpositive-time zero lemmas only as auxiliary facts for the specialized heat level-0 iterate, not as the main proof of the generic source-data producer.

## Bottom line

`srcSlice` is not the bug. The bug is that the producer has positive-time hypotheses but the target structure still demands global-in-time `ContDiff`/bounds. For heat level 0, the nonpositive side is zero, but the raw coefficient is generally not `C²` at `t = 0`. The honest formalization should either be positive-time/local, or should insert the smooth cutoff before making a global `ContDiff` claim.
