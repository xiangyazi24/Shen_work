# Q1023 (cron2) — `τ ≤ 0` branch in Level0 `hfluxC2`

Static repo inspection only; I did **not** run Lean.

## Executive verdict

1. The actual convention is **zero for non-positive heat time**, not `u₀`.

   At Level0,

   ```lean
   conjugatePicardIter p u₀ 0 τ x
   ```

   is definitionally the same heat-semigroup profile as

   ```lean
   picardIter p u₀ 0 τ x
   ```

   namely

   ```lean
   intervalFullSemigroupOperator τ (intervalDomainLift u₀) x.1
   ```

   The operator has no explicit `if τ ≤ 0 then 0`; instead the zero convention comes from the definition of `heatKernel`: for `t ≤ 0`, `Real.sqrt (4 * Real.pi * t) = 0`, hence the prefactor `1 / sqrt(...)` is `0` in Lean's total division convention. The repo already records this as

   ```lean
   theorem heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
       heatKernel t x = 0
   ```

   in `ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean`.

2. The seven `sorry`s in the `τ ≤ 0` branch of `level0_chemDiv_timeDerivData` are **not trivially fillable as written**.

   The reason is not the value at strictly negative times; it is the point `τ = 0`, plus the current choice `δ = 1` for the whole `τ ≤ 0` branch.

   For `τ < 0`, one could choose a smaller radius such as `δ < -τ`, keeping the ball entirely in negative time. Then the heat-semigroup profile is zero throughout that ball, so many fields should collapse to constant/zero obligations.

   But for `τ = 0`, **no positive ball avoids positive times**. The Level0 profile is zero at `t = 0` and for `t < 0`, while for `t > 0` it is the heat evolution `S(t)u₀`; the repo documentation in `IntervalDuhamelClosedC2.lean` explicitly notes that `S(0)f = f` is false for this implementation and the correct statement is only the right-limit approximate identity as `t ↓ 0`. Thus `(t,x) ↦ intervalDomainLift (conjugatePicardIter p u₀ 0 t) x` is generally discontinuous at `t = 0` unless `u₀` is identically zero. In particular, the F2 field

   ```lean
   ContDiffAt ℝ 2
     (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)
   ```

   cannot hold at `s = 0` in general. So the `τ ≤ 0` branch is not merely missing simp lemmas; at `τ = 0` the global structure is asking for a false local regularity statement.

3. The right fix is to **avoid the global `∀ τ : ℝ` package** in this positive-window theorem.

   `level0_chemDiv_timeDerivData` only needs data on `s ∈ Icc c T`, with `hc : 0 < c`. Its result is already window-local:

   ```lean
   ∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
     (∀ s ∈ Icc c T, ∀ n,
       HasDerivWithinAt
         (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
         (adot s n) (Icc c T) s) ∧
     (∀ n, ContinuousOn (fun s => adot s n) (Icc c T)) ∧
     (∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ Mdot)
   ```

   So constructing a full

   ```lean
   CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)
   ```

   is stronger than needed and is exactly what forces the impossible `τ = 0` obligation.

## Evidence from the repository

### Picard/conjugate Level0 definitions

`ShenWork/Paper2/IntervalMildPicard.lean` defines

```lean
/-- The Picard iteration: u₀(t,x) = S(t)u₀(x), u_{n+1} = Φ(u₀, u_n). -/
def picardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    : ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x => intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x
```

`ShenWork/Paper2/IntervalConjugatePicard.lean` similarly defines

```lean
/-- B-form Picard iteration:
`u₀(t,x) = S(t)u₀(x)`, `u_{n+1} = Φᴮ(u_n)`. -/
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x
```

The target file also states the definitional equality in its Section 1 comment:

```lean
`conjugatePicardIter p u₀ 0` is definitionally `picardIter p u₀ 0`, which is
`fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1`.
```

### Heat kernel and semigroup at non-positive time

`ShenWork/PDE/HeatSemigroup.lean` defines

```lean
/-- The heat kernel on ℝ at time t > 0. -/
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))
```

There is no guard in the definition. The zero convention is proved in `ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean`:

```lean
/-- The heat kernel vanishes for non-positive time (Lean's `Real.sqrt` returns `0`
on non-positive inputs, so the prefactor `1/√(4πt)` is `0`). -/
theorem heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    heatKernel t x = 0 := by
  unfold heatKernel
  have h4t : 4 * Real.pi * t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  rw [Real.sqrt_eq_zero'.mpr h4t]
  simp
```

`IntervalMildPicard.lean` has file-private helper lemmas showing the same collapse propagates to the full Neumann kernel and semigroup operator:

```lean
private theorem intervalNeumannFullKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x y : ℝ) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  have hzero : (fun k : ℤ =>
      heatKernel t (x - y + 2 * (k : ℝ)) +
        heatKernel t (x + y + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
    funext k
    rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht,
      ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht]
    simp
  rw [hzero, tsum_zero]

private theorem intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  have hzero : (fun y : ℝ => intervalNeumannFullKernel t x y * f y) =
      fun _ : ℝ => (0 : ℝ) := by
    funext y
    rw [intervalNeumannFullKernel_of_nonpos ht x y]
    simp
  rw [hzero]
  simp
```

These are `private`, so they are not directly importable by `IntervalConjugateLevel0BFormSourceOn.lean`; a local copy or exported lemma would be needed if one wanted to prove strictly-negative-time collapse directly.

### Why `τ = 0` is the obstruction

`ShenWork/PDE/IntervalDuhamelClosedC2.lean` documents the implementation convention:

```lean
`S(0)f = f` is FALSE (`heatKernel 0 = 0`); the correct statement is the
approximate-identity limit, already proved:
`ShenWork.IntervalSemigroupApproxIdentity.intervalFullSemigroup_tendsto_id_at_zero`
(`S(t)f x → f x` as `t↓0`, ...)
```

Therefore the Level0 heat profile is generally not continuous at zero:

```text
S(t)u₀ = 0        for t ≤ 0   -- by the zero heat-kernel convention
S(t)u₀ → u₀      as t ↓ 0    -- approximate identity
```

Unless `u₀ = 0`, this rules out `ContDiffAt` at `t = 0` for the lifted Level0 trajectory. The current `τ ≤ 0` branch must handle `τ = 0`, and it chooses `δ = 1`, so the ball contains both non-positive and positive times. Thus the branch cannot be solved by proving “everything is zero”.

## What can be salvaged from the negative branch?

A strictly-negative branch could be made trivial-ish by splitting further:

```lean
by_cases hτ0 : τ = 0
· -- impossible / should not be required by the window-local theorem
  ...
· -- with hτ : ¬ 0 < τ and hτ0 : τ ≠ 0, get τ < 0
  have hτ_neg : τ < 0 := lt_of_le_of_ne (not_lt.mp hτ) hτ0
  refine ⟨min 1 (-τ / 2), ?pos, ...⟩
  -- then `s ∈ Metric.ball τ δ` implies `s < 0`, so heat semigroup terms vanish.
```

But this is not the recommended path, because the `τ = 0` case remains false for the current global structure.

## Recommended refactor: localize to `[c,T]`

The existing code constructs

```lean
have hfluxC2 : CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0) := by
  ...
```

and then obtains

```lean
have hchain : CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ 0) :=
  coupledChemDivLocalChainRule_of_fluxJointC2 hfluxC2
```

This is too strong. `CoupledChemDivFluxJointC2Hyp`, `CoupledChemDivOuterCommuteAtoms`, and `CoupledChemDivLocalChainRule` all quantify over **all** real `τ`:

```lean
exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ...
```

But the Level0 On theorem only needs `τ ∈ Icc c T` and has `hc : 0 < c`.

A better local target is:

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalConjugatePicard

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- Window-local replacement for the global `CoupledChemDivLocalChainRule` in Level0. -/
structure CoupledChemDivLocalChainRuleOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c T : ℝ) : Prop where
  exists_local_slab : ∀ τ ∈ Icc c T, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => coupledChemDivSourceLift p u r x)
        (coupledChemDivTimeDerivativeLift p u s x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

Then, inside `level0_chemDiv_timeDerivData`, replace the global `hfluxC2/hchain` construction with a window-local slab lemma:

```lean
-- Sketch only; not checked by Lean in this inspection.
have hchain_on :
    CoupledChemDivLocalChainRuleOn p (conjugatePicardIter p u₀ 0) c T := by
  refine ⟨fun τ hτ => ?_⟩
  -- Since τ ∈ [c,T] and c > 0, choose δ ≤ c/2.
  refine ⟨min 1 (c / 2), lt_min one_pos (half_pos hc), ?_, ?_, ?_⟩
  · -- source regularity near τ; all nearby times are positive
    -- same positive-time proof as the old `hτ : 0 < τ` branch, but use `hc`.
    sorry
  · -- pointwise chain rule near τ; all nearby times are positive
    intro x hx s hs
    have hs_pos : 0 < s := by
      have hdist := Metric.mem_ball.mp hs
      rw [Real.dist_eq] at hdist
      have hlt := lt_of_lt_of_le hdist (min_le_right 1 (c / 2))
      have hτ_ge_c : c ≤ τ := hτ.1
      have habs := abs_lt.mp hlt
      linarith
    -- continue with positive-time heat/resolver regularity
    sorry
  · -- joint continuity on the positive slab
    sorry
```

Then consume `hchain_on` directly, without producing a global `HasDerivAt` for all `s`:

```lean
-- Joint continuity only on `[c,T] × [0,1]`.
have hjointcont : ContinuousOn
    (Function.uncurry
      (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
    (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  intro ⟨s, x⟩ hsx
  obtain ⟨hs, hx⟩ := mem_prod.1 hsx
  rcases hchain_on.exists_local_slab s hs with ⟨δ, hδ, _, _, hcont⟩
  have hmem : (s, x) ∈ Icc (s - δ) (s + δ) ×ˢ Icc (0 : ℝ) 1 :=
    mem_prod.2 ⟨⟨by linarith, by linarith⟩, hx⟩
  have h_slab_nhds : Icc (s - δ) (s + δ) ×ˢ Icc (0 : ℝ) 1 ∈
      𝓝[Icc c T ×ˢ Icc (0 : ℝ) 1] (s, x) := by
    rw [mem_nhdsWithin]
    exact ⟨Ioo (s - δ) (s + δ) ×ˢ Set.univ,
      isOpen_Ioo.prod isOpen_univ,
      ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩,
      fun ⟨_, _⟩ ⟨h_in_U, h_in_target⟩ =>
        ⟨Ioo_subset_Icc_self h_in_U.1, h_in_target.2⟩⟩
  exact (hcont.continuousWithinAt hmem).mono_of_mem_nhdsWithin h_slab_nhds

-- Derivative only where the theorem needs it.
have hderiv : ∀ s ∈ Icc c T, ∀ n,
    HasDerivWithinAt
      (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
      (adot s n) (Icc c T) s := by
  intro s hs n
  rcases hchain_on.exists_local_slab s hs with ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
  have hAt : HasDerivAt
      (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
      (adot s n) s := by
    simpa only [coupledChemDivSourceCoeffs, hadot_def,
      coupledChemDivAdot] using
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
        (f := coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0))
        (f' := coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0))
        (τ := s) (δ := δ) (n := n) hδ hf_cont hdiff hcont_deriv
  exact hAt.hasDerivWithinAt
```

This eliminates the entire `by_cases hτ : 0 < τ` split from the Level0 On proof. More importantly, it matches the theorem's actual contract: a `DuhamelSourceTimeC1On`-style package on `[c,T]`, not a global `DuhamelSourceTimeC1` package on all real time.

## Caveat: this does not solve the positive-time analytic residuals

Avoiding the `τ ≤ 0` branch removes a false/unnecessary global obligation. It does **not** by itself solve the existing positive-time residuals in the `τ > 0` branch:

- `3A-sub` still records the boundary obstruction from `intervalDomainLift` and `ContinuousOn ... (Icc 0 1)`.
- `3C`/`3D` still need resolver joint C² and resolver-gradient joint C².
- `3E` still needs the positivity floor.
- `3F`/`3G` still need the flux time-derivative bridge and joint continuity.

So the recommendation is not “fill the seven negative sorries by simp”; it is “do not ask for them”. The current global helper packages are too strong for the Level0 positive-window theorem.

## Concrete answer to the three questions

### 1. What is the actual definition at `τ ≤ 0`?

For Level0:

```lean
conjugatePicardIter p u₀ 0 τ x
= picardIter p u₀ 0 τ x
= intervalFullSemigroupOperator τ (intervalDomainLift u₀) x.1
```

For `τ ≤ 0`, the heat kernel is zero, hence the full Neumann kernel and full semigroup operator are zero. Thus the actual Lean behavior is **zero**, not `u₀`.

### 2. Can the seven `τ ≤ 0` sorries be filled trivially?

No, not as currently structured.

Strictly negative times could likely be made trivial by choosing a ball contained in `(-∞,0)`. But the branch includes `τ = 0`, and at `τ = 0` any neighborhood sees both the zero convention at non-positive times and the genuine heat semigroup for positive times. The required `ContDiffAt`/continuity fields are generally false there.

The current `δ = 1` also prevents a simple negative-time proof for small negative `τ`, because the ball crosses into positive time.

### 3. Can the by-cases be avoided?

Yes, and that is the recommended route.

Do not construct global

```lean
CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)
```

or global

```lean
CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ 0)
```

inside `level0_chemDiv_timeDerivData`. Instead, construct a window-local chain-rule package only for `τ ∈ Icc c T`, using `hc : 0 < c` to keep all local slabs in positive time. Then build `hjointcont` and `hderiv` directly from that localized package.

This aligns with the surrounding file, whose purpose is already `DuhamelSourceTimeC1On` on a positive window `[c,T]`.
