# Q1506 (cron1) -- quartic `PhysicalSourceTimeC2` skeleton

Repository: `xiangyazi24/Shen_work`
Branch: `chatgpt-scratch`
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method

Connector-only repository search. I did not run Lean locally and did not edit Lean source.

Relevant files inspected:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
ShenWork/PDE/IntervalResolverJointC2Physical.lean
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
ShenWork/PDE/IntervalSourceDecayQuantitative.lean
```

The important fact from the repo is:

```lean
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
```

with shape:

```lean
(hf : IntervalWeakH2Neumann f)
(hf'' : IntervalWeakH2Neumann hf.secondDeriv)
(hB2 : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) <= B2)
⊢ ∀ k, 1 <= k -> |cosineCoeffs f k| <= 2 * B2 / ((k : ℝ) * Real.pi) ^ 4
```

## Placement warning

The cleanest implementation should live in

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

right after the current `srcTimeCoeff_bound`, because the quartic proof wants the private helper

```lean
srcTimeCoeff_iteratedDeriv_eq
```

which identifies the `i`-th time derivative of `srcTimeCoeff` with the cosine coefficient of the `i`-th source slice for `i <= 2`, `t > 0`.

If this skeleton is placed in another file, first make that helper public or restate it.

## Core skeleton

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalSourceDecayQuantitative

open Filter Topology Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointGradMajorant)
open ShenWork.IntervalResolverSpectralJointC2Concrete
  (valueCosWeight gradCosWeight valueCosWeight_nonneg gradCosWeight_nonneg)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff PhysicalSourceTimeC2)
open ShenWork.PDE (intervalNeumannResolverWeight)
open ShenWork.PDE.IntervalMildSourceDecayHelper
  (IntervalWeakH2Neumann)
open ShenWork.IntervalSourceDecayQuantitative

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- Quartic source envelope.  `D i` controls the zero mode of time slice `i`;
`Q i` controls the fourth-derivative `L1` bound of time slice `i`, so nonzero
modes have `O((k*pi)^-4)` decay. -/
def quarticEs (D Q : ℕ -> ℝ) (i k : ℕ) : ℝ :=
  if hi : i <= 2 then
    if k = 0 then D i
    else 2 * Q i / (((k : ℝ) * Real.pi) ^ 4)
  else 0

/-- Positive-time quartic bound for the source time coefficients.

Put this next to `srcTimeCoeff_bound` so the private lemma
`srcTimeCoeff_iteratedDeriv_eq` is in scope. -/
theorem srcTimeCoeff_quartic_bound_pos
    {p : CM2Params} {u : ℝ -> intervalDomainPoint -> ℝ}
    {s1 s2 : ℝ -> ℝ -> ℝ}
    (H : FlooredSourceTimeData p u s1 s2)
    (D Q : ℕ -> ℝ)
    (hzero : ∀ i, i <= 2 -> ∀ t, 0 < t ->
      |cosineCoeffs ((sliceFam (srcSlice p u) s1 s2 i) t) 0| <= D i)
    (hH4 : ∀ i, i <= 2 -> ∀ t, 0 < t ->
      ∃ hf : IntervalWeakH2Neumann ((sliceFam (srcSlice p u) s1 s2 i) t),
      ∃ hf2 : IntervalWeakH2Neumann hf.secondDeriv,
        (∫ x in (0:ℝ)..1, |hf2.secondDeriv x|) <= Q i)
    (i k : ℕ) (t : ℝ) (hi : i <= 2) (ht : 0 < t) :
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ <= quarticEs D Q i k := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    srcTimeCoeff_iteratedDeriv_eq H i k hi ht,
    Real.norm_eq_abs, quarticEs, dif_pos hi]
  by_cases hk : k = 0
  · rw [if_pos hk]
    subst k
    exact hzero i hi t ht
  · rw [if_neg hk]
    have hk1 : 1 <= k := Nat.one_le_iff_ne_zero.mpr hk
    rcases hH4 i hi t ht with ⟨hf, hf2, hB4⟩
    exact intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
      hf hf2 hB4 k hk1
```

The theorem above is the actual replacement for the old `builtEs`/quadratic tail in the positive-time branch.

## Summability helper skeletons

These are the algebra lemmas that make the new envelope work.  The main point is that, for `k >= 1`, the value spatial weights are at worst `lambda`, and the gradient spatial weights are at worst `freq * lambda`.  With quartic decay:

```text
w_k * O(freq^-4) * lambda          = O(freq^-2)
w_k * O(freq^-4) * (freq*lambda)  = O(freq^-3)
```

both are summable.

```lean
private theorem weighted_quartic_value_summand_summable
    {p : CM2Params} {D Q : ℕ -> ℝ}
    (hD_nonneg : ∀ i, i <= 2 -> 0 <= D i)
    (hQ_nonneg : ∀ i, i <= 2 -> 0 <= Q i)
    (i j : ℕ) (hi : i <= 2) (hj : j <= 2) :
    Summable (fun k : ℕ =>
      intervalNeumannResolverWeight p k * quarticEs D Q i k * valueCosWeight j k) := by
  -- Split k = 0 and k >= 1.
  -- k = 0 is a single supported term.
  -- For k >= 1, unfold `quarticEs` and `valueCosWeight`.
  -- Cases j = 0,1,2:
  --   j = 0:  w * (2Q/freq^4) * 1      <= C/freq^4
  --   j = 1:  w * (2Q/freq^4) * freq   <= C/freq^3
  --   j = 2:  w * (2Q/freq^4) * lambda <= C/freq^2
  -- Use:
  --   ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu
  --   ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one
  --   Real.summable_one_div_nat_pow for powers 2,3,4
  -- Then combine zero-mode finite support + tail summability.
  sorry

private theorem weighted_quartic_grad_summand_summable
    {p : CM2Params} {D Q : ℕ -> ℝ}
    (hD_nonneg : ∀ i, i <= 2 -> 0 <= D i)
    (hQ_nonneg : ∀ i, i <= 2 -> 0 <= Q i)
    (i j : ℕ) (hi : i <= 2) (hj : j <= 2) :
    Summable (fun k : ℕ =>
      intervalNeumannResolverWeight p k * quarticEs D Q i k * gradCosWeight j k) := by
  -- Split k = 0 and k >= 1.
  -- For k >= 1, unfold `quarticEs` and `gradCosWeight`.
  -- Cases j = 0,1,2:
  --   j = 0:  w * (2Q/freq^4) * freq          <= C/freq^3 or better
  --   j = 1:  w * (2Q/freq^4) * lambda        <= C/freq^2 or better
  --   j = 2:  w * (2Q/freq^4) * freq*lambda   <= C/freq^3
  -- The last line is the crucial fix: with quadratic `builtEs` it was only
  -- O(freq^-1), but quartic gives O(freq^-3).
  -- Use `lambda * w <= 1`, `w <= 1/mu`, and `Real.summable_one_div_nat_pow`.
  sorry

theorem quartic_value_summable
    {p : CM2Params} {D Q : ℕ -> ℝ}
    (hD_nonneg : ∀ i, i <= 2 -> 0 <= D i)
    (hQ_nonneg : ∀ i, i <= 2 -> 0 <= Q i) :
    ∀ m : ℕ, (m : ℕ∞) <= (2 : ℕ∞) ->
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * quarticEs D Q i k) m) := by
  intro m hm
  have hmNat : m <= 2 := by exact_mod_cast hm
  unfold boundedWeightJointMajorant
  -- Finite sum in `i`; each summand is summable by
  -- `weighted_quartic_value_summand_summable` with `j = m - i`.
  -- The binomial coefficient is a scalar multiplier.
  -- Suggested implementation: `Finset.induction_on` the range or use the repo's
  -- existing finite-sum summability API if available.
  refine Finset.summable_sum ?_
  intro i hi_mem
  have hi_le_m : i <= m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
  have hi2 : i <= 2 := le_trans hi_le_m hmNat
  have hj2 : m - i <= 2 := le_trans (Nat.sub_le m i) hmNat
  exact (weighted_quartic_value_summand_summable
    (p := p) (D := D) (Q := Q) hD_nonneg hQ_nonneg i (m - i) hi2 hj2).mul_left
      (Nat.choose m i : ℝ)

theorem quartic_grad_summable
    {p : CM2Params} {D Q : ℕ -> ℝ}
    (hD_nonneg : ∀ i, i <= 2 -> 0 <= D i)
    (hQ_nonneg : ∀ i, i <= 2 -> 0 <= Q i) :
    ∀ m : ℕ, (m : ℕ∞) <= (2 : ℕ∞) ->
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * quarticEs D Q i k) m) := by
  intro m hm
  have hmNat : m <= 2 := by exact_mod_cast hm
  unfold boundedWeightJointGradMajorant
  refine Finset.summable_sum ?_
  intro i hi_mem
  have hi_le_m : i <= m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
  have hi2 : i <= 2 := le_trans hi_le_m hmNat
  have hj2 : m - i <= 2 := le_trans (Nat.sub_le m i) hmNat
  exact (weighted_quartic_grad_summand_summable
    (p := p) (D := D) (Q := Q) hD_nonneg hQ_nonneg i (m - i) hi2 hj2).mul_left
      (Nat.choose m i : ℝ)
```

If `Finset.summable_sum` is not the exact Mathlib name in this environment, replace those two blocks by an induction over `Finset.range (m+1)` and repeated `Summable.add` / `Summable.mul_left`.

## Direct `PhysicalSourceTimeC2` constructor with where fields

This is the direct constructor that bypasses `physicalSourceTimeC2_of_floored` and never uses `builtEs`.

```lean
/-- Direct quartic physical source-time data.  This is the replacement for
`physicalSourceTimeC2_of_floored hFSTD ... ...` when the gradient summability
needs quartic decay. -/
theorem physicalSourceTimeC2_of_floored_quartic
    {p : CM2Params} {u : ℝ -> intervalDomainPoint -> ℝ}
    {s1 s2 : ℝ -> ℝ -> ℝ}
    (H : FlooredSourceTimeData p u s1 s2)
    (D Q : ℕ -> ℝ)
    (hD_nonneg : ∀ i, i <= 2 -> 0 <= D i)
    (hQ_nonneg : ∀ i, i <= 2 -> 0 <= Q i)
    (hzero : ∀ i, i <= 2 -> ∀ t, 0 < t ->
      |cosineCoeffs ((sliceFam (srcSlice p u) s1 s2 i) t) 0| <= D i)
    (hH4 : ∀ i, i <= 2 -> ∀ t, 0 < t ->
      ∃ hf : IntervalWeakH2Neumann ((sliceFam (srcSlice p u) s1 s2 i) t),
      ∃ hf2 : IntervalWeakH2Neumann hf.secondDeriv,
        (∫ x in (0:ℝ)..1, |hf2.secondDeriv x|) <= Q i)
    -- Keep these two as explicit hypotheses until the all-real extension of
    -- `srcTimeCoeff_contDiffAt` / `src_bound` is finished.
    (hsrcC2 : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k))
    (hsrc_nonpos : ∀ i k t, i <= 2 -> ¬ 0 < t ->
      ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ <= quarticEs D Q i k) :
    PhysicalSourceTimeC2 p u (quarticEs D Q) where
  src_contDiff k := hsrcC2 k
  src_bound i k t hi := by
    by_cases ht : 0 < t
    · exact srcTimeCoeff_quartic_bound_pos H D Q hzero hH4 i k t hi ht
    · exact hsrc_nonpos i k t hi ht
  value_summable m hm :=
    quartic_value_summable (p := p) (D := D) (Q := Q) hD_nonneg hQ_nonneg m hm
  grad_summable m hm :=
    quartic_grad_summable (p := p) (D := D) (Q := Q) hD_nonneg hQ_nonneg m hm
```

This is the requested `where`-field construction.  The two explicit hypotheses `hsrcC2` and `hsrc_nonpos` are deliberate: the existing `physicalSourceTimeC2_of_floored` still has corresponding all-real extension work in its own `src_contDiff` and `src_bound` fields.  The quartic change is orthogonal to that issue.

## How to use it in `IntervalHeatSemigroupHighRegularity.lean`

In `heatSemigroup_level0_resolverJointC2Data`, replace:

```lean
set Es := ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD
have hSTC2 : PhysicalSourceTimeC2 p u Es :=
  ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored hFSTD
    ...
    ...
```

by:

```lean
set Es4 := ShenWork.IntervalPhysicalSourceTimeC2Concrete.quarticEs D Q
have hSTC2 : ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2 p u Es4 :=
  ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored_quartic
    hFSTD D Q hD_nonneg hQ_nonneg hzero hH4 hsrcC2 hsrc_nonpos
```

Then the existing resolver step remains unchanged:

```lean
exact ⟨_, ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor hSTC2⟩
```

because `physicalResolverJointC2Data_of_floor` only needs `PhysicalSourceTimeC2 p u Es`; it does not care how `Es` was produced.

## Why quartic fixes `grad_summable`

With quadratic `builtEs`, the worst gradient-majorant term at joint order `m = 2` is:

```text
w_k * O(freq^-2) * (freq * lambda) = O(freq^-1)
```

which is not summable.

With quartic `quarticEs`, the same term becomes:

```text
w_k * O(freq^-4) * (freq * lambda)
```

Using `lambda * w_k <= 1`, this is bounded by:

```text
O(freq^-3)
```

which is summable.  Value summability is easier: the worst value spatial weight is only `lambda`, giving `O(freq^-2)`.

## Notes for implementation

1. If Lean complains about `Finset.summable_sum`, use finite-set induction with `Summable.add`.
2. If the nonzero-mode algebra is noisy, first prove small lemmas:

```lean
freq_mul_resolverWeight_le_inv_freq
quartic_value_weight_le_inv_square
quartic_grad_weight_le_inv_square_or_cube
```

3. Do not route through `builtEs`; the whole point is to make the resolver envelope `Bt i k = w_k * quarticEs D Q i k`.
4. The H4 tower should be supplied per time-order slice `i = 0,1,2`; otherwise the second time derivative source slice still lacks quartic decay.

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```
