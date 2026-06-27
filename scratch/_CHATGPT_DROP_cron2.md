# Q1161 (cron2) — `FlooredSourceTimeData.d1` for level-0 heat

Static GitHub-connector inspection only. I did **not** run Lean locally.

## What already exists

`ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean` already has exactly the chain-rule lemma needed for `d1`:

```lean
theorem hasDerivAt_srcSlice1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    {t x : ℝ} (hpos : 0 < intervalDomainLift (u t) x)
    (hdu : HasDerivAt (fun r => intervalDomainLift (u r) x) (du t x) t)
    (hd2u : HasDerivAt (fun r => du r x) (d2u t x) t) :
    HasDerivAt (fun r => srcSlice1 p u du r x) (srcSlice2 p u du d2u t x) t
```

So `d1` should not re-prove the product/rpow algebra.  It should only supply:

1. positivity of the heat slice at the evaluation point;
2. `HasDerivAt` of `t ↦ S(t)u₀(x)` with derivative `heatDu u₀ t x`;
3. `HasDerivAt` of `t ↦ heatDu u₀ t x` with derivative `heatD2u u₀ t x`;
4. eventual closed-slice continuity of `srcSlice1`;
5. closed-slab joint continuity of `srcSlice2`.

`IntervalFlooredSourceTimeDataIterate.lean` also has the higher-level abstraction:

```lean
structure IterateSourceTimeData ... where
  time2 : ∀ τ, ∃ δ > 0, ...

theorem flooredSourceTimeData_of_iterate
    (H : IterateSourceTimeData p u du d2u) :
    FlooredSourceTimeData p u (srcSlice1 p u du) (srcSlice2 p u du d2u)
```

So the clean long-term route is to build an `IterateSourceTimeData` instance for the heat semigroup and let `flooredSourceTimeData_of_iterate` fill `d0` and `d1` uniformly.

## Important theorem-statement issue

As `IntervalHeatSemigroupFlooredSourceTimeData.lean` currently stands, `heatSemigroup_flooredSourceTimeData` assumes only:

```lean
(_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
(_hu₀_cont : Continuous u₀)
```

That is not enough for `d1`.  The formulas contain powers `u^(γ-1)` and `u^(γ-2)`, and the `Real.rpow` derivative theorem used by `hasDerivAt_srcSlice1` needs the base to be nonzero, supplied in practice by a positive floor:

```lean
hfloor : ∀ t, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

or by a stronger datum such as `PositiveInitialDatum intervalDomain u₀`, from which this floor is produced by heat-kernel positivity. Without some floor/positivity hypothesis, the `d1` obligation is not provable for arbitrary continuous `u₀`.

## Generic continuity helpers for `srcSlice1` and `srcSlice2`

These are small and should go in `IntervalFlooredSourceTimeDataIterate.lean` or locally in the heat file.

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)

noncomputable section

namespace ShenWork.IntervalFlooredSourceTimeDataIterate

/-- Closed-slice continuity of `srcSlice1 = νγ u^(γ-1) du` from component continuity
and a nonzero floor for `u`. -/
theorem srcSlice1_continuousOn_Icc_of_components
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du : ℝ → ℝ → ℝ}
    {t : ℝ}
    (hu : ContinuousOn (fun x : ℝ => intervalDomainLift (u t) x) (Icc (0 : ℝ) 1))
    (hdu : ContinuousOn (du t) (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, intervalDomainLift (u t) x ≠ 0) :
    ContinuousOn (srcSlice1 p u du t) (Icc (0 : ℝ) 1) := by
  have hpow : ContinuousOn
      (fun x : ℝ => intervalDomainLift (u t) x ^ (p.γ - 1)) (Icc (0 : ℝ) 1) :=
    hu.rpow_const_of_ne (fun x hx => Or.inl (hpos x hx))
  simpa [srcSlice1, mul_assoc] using
    (((continuousOn_const.mul continuousOn_const).mul hpow).mul hdu)

/-- Joint continuity of `srcSlice2` from component joint continuity and a nonzero
floor for `u` on the slab. -/
theorem srcSlice2_jointContinuousOn_of_components
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    {K : Set (ℝ × ℝ)}
    (hu : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) K)
    (hdu : ContinuousOn (Function.uncurry du) K)
    (hd2u : ContinuousOn (Function.uncurry d2u) K)
    (hpos : ∀ q ∈ K, intervalDomainLift (u q.1) q.2 ≠ 0) :
    ContinuousOn (Function.uncurry (srcSlice2 p u du d2u)) K := by
  have hpow2 : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2 ^ (p.γ - 1 - 1)) K :=
    hu.rpow_const_of_ne (fun q hq => Or.inl (hpos q hq))
  have hpow1 : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2 ^ (p.γ - 1)) K :=
    hu.rpow_const_of_ne (fun q hq => Or.inl (hpos q hq))
  have hdu_sq : ContinuousOn (fun q : ℝ × ℝ => (Function.uncurry du q) ^ (2 : ℕ)) K :=
    hdu.pow 2
  have hterm1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.ν * p.γ * (p.γ - 1) *
          intervalDomainLift (u q.1) q.2 ^ (p.γ - 1 - 1) *
            (Function.uncurry du q) ^ (2 : ℕ)) K := by
    simpa [mul_assoc] using
      ((((continuousOn_const.mul continuousOn_const).mul continuousOn_const).mul hpow2).mul hdu_sq)
  have hterm2 : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.ν * p.γ * intervalDomainLift (u q.1) q.2 ^ (p.γ - 1) *
          Function.uncurry d2u q) K := by
    simpa [mul_assoc] using
      (((continuousOn_const.mul continuousOn_const).mul hpow1).mul hd2u)
  simpa [Function.uncurry, srcSlice2, mul_assoc] using hterm1.add hterm2

end ShenWork.IntervalFlooredSourceTimeDataIterate
```

## Heat-specific atoms needed by `d1`

I did not find existing declarations with these names or equivalent public theorems in the repo.  They are the heat-specific content needed by the `d1` body.

```lean
namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

open ShenWork.IntervalFlooredSourceTimeDataIterate
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)

-- Time derivative of the heat value.
theorem level0_heat_hasDerivAt_heatDu
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t x : ℝ}
    (ht : 0 < t)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r => intervalDomainLift (conjugatePicardIter p u₀ 0 r) x)
      (heatDu u₀ t x) t := by
  -- Proof route: rewrite `conjugatePicardIter` to the full heat semigroup, bridge
  -- to `unitIntervalCosineHeatValue` on a positive-time neighborhood, and apply
  -- `RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2` or the
  -- existing positive-time summable-bound variant.  Then unfold `heatDu`; the
  -- `if_pos ht` branch gives the Laplacian value.
  sorry

-- Time derivative of the heat Laplacian.
theorem level0_heatDu_hasDerivAt_heatD2u
    {u₀ : intervalDomainPoint → ℝ} {M₀ t x : ℝ}
    (ht : 0 < t)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    HasDerivAt (fun r => heatDu u₀ r x) (heatD2u u₀ t x) t := by
  -- Proof route: on `Ioi 0`, `heatDu` is the Laplacian cosine series
  -- `∑ -λ exp(-tλ) a_k cos(kπx)`.  Differentiate termwise in time; the derivative
  -- is `∑ λ^2 exp(-tλ) a_k cos(kπx)`, which is exactly `heatD2u` under `if_pos ht`.
  -- The summable majorant is polynomial times exponential, available from the
  -- heat high-regularity summability lemmas.
  sorry

-- Closed-slice continuity of the heat value and its first two time derivatives.
theorem level0_heat_lift_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (ht : 0 < t)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) :
    ContinuousOn (fun x => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
      (Icc (0 : ℝ) 1) := by
  -- Use the positive-time cosine representative and `hagree_zero`.
  sorry

theorem level0_heatDu_continuousOn_Icc
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (ht : 0 < t)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContinuousOn (heatDu u₀ t) (Icc (0 : ℝ) 1) := by
  -- Unfold `heatDu`, use `if_pos ht`, and continuity of the Laplacian cosine series.
  sorry

theorem level0_heatD2u_jointContinuousOn_slab
    {u₀ : intervalDomainPoint → ℝ} {M₀ τ δ : ℝ}
    (hleft : 0 < τ - δ)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContinuousOn (Function.uncurry (heatD2u u₀))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  -- Unfold `heatD2u`; on the slab all times are positive, so the `if_pos` branch
  -- is active.  Use uniform convergence of the `λ^2 exp(-tλ)` cosine series on
  -- the closed positive slab.
  sorry

theorem level0_heat_lift_jointContinuousOn_slab
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ δ : ℝ}
    (hleft : 0 < τ - δ)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) :
    ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  -- Same bridge as above, using the heat value cosine series on the positive slab.
  sorry

theorem level0_heatDu_jointContinuousOn_slab
    {u₀ : intervalDomainPoint → ℝ} {M₀ τ δ : ℝ}
    (hleft : 0 < τ - δ)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContinuousOn (Function.uncurry (heatDu u₀))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  -- Unfold `heatDu`; use the Laplacian cosine series uniformly on the positive slab.
  sorry

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

The `sorry`s above are not part of the `d1` proof body; they are the missing heat spectral atoms.  Once these atoms exist, `d1` is short and uses the already-committed `hasDerivAt_srcSlice1`.

## Pasteable `d1` body

This is the body for the `d1 := by` field, assuming the theorem has a positive heat floor hypothesis:

```lean
    intro τ hτ
    let δ : ℝ := min (1 : ℝ) (τ / 2)
    have hδ : 0 < δ := lt_min one_pos (half_pos hτ)
    have hleft : 0 < τ - δ := by
      have hδ_le : δ ≤ τ / 2 := min_le_right (1 : ℝ) (τ / 2)
      linarith

    refine ⟨δ, hδ, ?_, ?_, ?_⟩

    · -- (a) eventual closed-slice continuity of `srcSlice1`.
      apply Filter.eventually_of_mem (Metric.ball_mem_nhds τ hδ)
      intro s hs
      have hs_pos : 0 < s := by
        have hdist := Metric.mem_ball.mp hs
        rw [Real.dist_eq] at hdist
        have hlt := lt_of_lt_of_le hdist (min_le_right (1 : ℝ) (τ / 2))
        linarith [(abs_lt.mp hlt).1]
      apply ShenWork.IntervalFlooredSourceTimeDataIterate
        .srcSlice1_continuousOn_Icc_of_components
      · exact level0_heat_lift_continuousOn_Icc
          (p := p) (u₀ := u₀) (M₀ := M₀) hs_pos _hu₀_bound _hu₀_cont
      · exact level0_heatDu_continuousOn_Icc
          (u₀ := u₀) (M₀ := M₀) hs_pos _hu₀_bound
      · intro x hx
        exact ne_of_gt (hfloor s hs_pos x hx)

    · -- (b) pointwise derivative of `srcSlice1` is `srcSlice2`.
      intro x hx s hs
      have hs_pos : 0 < s := by
        have hdist := Metric.mem_ball.mp hs
        rw [Real.dist_eq] at hdist
        have hlt := lt_of_lt_of_le hdist (min_le_right (1 : ℝ) (τ / 2))
        linarith [(abs_lt.mp hlt).1]
      have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
      exact ShenWork.IntervalFlooredSourceTimeDataIterate.hasDerivAt_srcSlice1
        (p := p)
        (u := conjugatePicardIter p u₀ 0)
        (du := heatDu u₀)
        (d2u := heatD2u u₀)
        (hfloor s hs_pos x hxIcc)
        (level0_heat_hasDerivAt_heatDu
          (p := p) (u₀ := u₀) (M₀ := M₀) hs_pos _hu₀_bound _hu₀_cont hxIcc)
        (level0_heatDu_hasDerivAt_heatD2u
          (u₀ := u₀) (M₀ := M₀) hs_pos _hu₀_bound)

    · -- (c) joint closed-slab continuity of `srcSlice2`.
      have hUjoint : ContinuousOn
          (fun q : ℝ × ℝ =>
            intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
        level0_heat_lift_jointContinuousOn_slab
          (p := p) (u₀ := u₀) (M₀ := M₀) hleft _hu₀_bound _hu₀_cont
      have hdujoint : ContinuousOn (Function.uncurry (heatDu u₀))
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
        level0_heatDu_jointContinuousOn_slab
          (u₀ := u₀) (M₀ := M₀) hleft _hu₀_bound
      have hd2ujoint : ContinuousOn (Function.uncurry (heatD2u u₀))
          (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
        level0_heatD2u_jointContinuousOn_slab
          (u₀ := u₀) (M₀ := M₀) hleft _hu₀_bound
      apply ShenWork.IntervalFlooredSourceTimeDataIterate
        .srcSlice2_jointContinuousOn_of_components
      · exact hUjoint
      · exact hdujoint
      · exact hd2ujoint
      · intro q hq
        exact ne_of_gt (hfloor q.1 (by exact lt_of_lt_of_le hleft hq.1.1) q.2 hq.2)
```

## Even shorter route if you build `IterateSourceTimeData`

If you construct:

```lean
Hheat : ShenWork.IntervalFlooredSourceTimeDataIterate.IterateSourceTimeData
  p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)
```

then the field is simply:

```lean
  d1 := by
    exact (ShenWork.IntervalFlooredSourceTimeDataIterate
      .flooredSourceTimeData_of_iterate Hheat).d1
```

or, if Lean expects arguments explicitly:

```lean
  d1 := by
    intro τ hτ
    exact (ShenWork.IntervalFlooredSourceTimeDataIterate
      .flooredSourceTimeData_of_iterate Hheat).d1 τ hτ
```

That is the clean architectural route, because `flooredSourceTimeData_of_iterate` already uses `hasDerivAt_srcSlice1` internally.
