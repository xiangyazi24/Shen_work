# Q1272 / cron1 — `srcTimeCoeff` at nonpositive time

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

For the concrete definitions currently in the repo,

```lean
intervalFullSemigroupOperator t f x = 0
```

for every `f` and `x` whenever `t ≤ 0`.

So for the level-0 conjugate Picard iterate

```lean
u = conjugatePicardIter p u₀ 0
```

we have, definitionally/provably,

```lean
u t x = 0
```

for all interval points `x` whenever `t ≤ 0`.

Consequently,

```lean
srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

is the source coefficient of the zero profile for `t ≤ 0`. Since `p.hγ : 0 < p.γ`, the source `p.ν * 0 ^ p.γ` is zero, so this coefficient should simplify to `0`.

This does **not** solve global `ContDiff ℝ 2` at `t = 0` for generic nonzero/positive initial datum. It shows the raw time extension is zero on `(-∞,0]`, while the positive-time heat semigroup tends to the initial datum as `t → 0+`. Hence the source coefficient generally jumps at `0` unless the corresponding initial source coefficient vanishes. The safe route for all-real `ContDiff` is a cutoff or a changed data interface, not just combining positive-time `ContDiffAt` with the nonpositive side.

## Evidence in the repo

### 1. The full semigroup is an integral against the full Neumann kernel

In `ShenWork/PDE/IntervalNeumannFullKernel.lean`:

```lean
import ShenWork.PDE.IntervalNeumannFullKernel

open MeasureTheory
open ShenWork.IntervalDomain

namespace ShenWork.IntervalNeumannFullKernel

/-- The **full** periodised method-of-images Neumann heat kernel on `[0,1]`. -/
def intervalNeumannFullKernel (t x y : ℝ) : ℝ :=
  ∑' k : ℤ, (heatKernel t (x - y + 2 * k) + heatKernel t (x + y + 2 * k))

/-- The full periodised-image Neumann heat propagator on `[0,1]`. -/
def intervalFullSemigroupOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1

end ShenWork.IntervalNeumannFullKernel
```

### 2. The underlying heat kernel vanishes for nonpositive time

The heat kernel itself is defined in `ShenWork/PDE/HeatSemigroup.lean` as

```lean
import ShenWork.PDE.HeatSemigroup

def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))
```

The important already-proved nonpositive-time lemma is in
`ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean`:

```lean
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

namespace ShenWork.IntervalNeumannFullKernel

/-- The heat kernel vanishes for non-positive time (Lean's `Real.sqrt` returns `0`
on non-positive inputs, so the prefactor `1/√(4πt)` is `0`). -/
theorem heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    heatKernel t x = 0 := by
  unfold heatKernel
  have h4t : 4 * Real.pi * t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  rw [Real.sqrt_eq_zero'.mpr h4t]
  simp

end ShenWork.IntervalNeumannFullKernel
```

This is stronger than the older zero-time-only fact.

### 3. The zero-time-only semigroup lemma already exists

In `ShenWork/PDE/IntervalSemigroupAtZero.lean`:

```lean
import ShenWork.PDE.IntervalSemigroupAtZero

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalSemigroupAtZero

/-- The period-`2` image Neumann kernel is **identically zero** at time `0`. -/
theorem intervalNeumannFullKernel_zero (x y : ℝ) :
    intervalNeumannFullKernel 0 x y = 0 := by
  unfold intervalNeumannFullKernel
  simp [heatKernel_zero]

/-- **The actual value of the propagator at time `0`.** -/
theorem intervalFullSemigroupOperator_zero (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator 0 f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_zero]

end ShenWork.IntervalSemigroupAtZero
```

The repo does not appear to have a named `intervalFullSemigroupOperator_nonpos` lemma, but it is a direct generalization using `heatKernel_of_nonpos`.

## Lemma to add: full semigroup vanishes for `t ≤ 0`

A natural place is `ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean`, after `heatKernel_of_nonpos`, or in a small downstream helper imported by the heat-level-0 work.

```lean
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open MeasureTheory
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

/-- The full periodised Neumann kernel is identically zero for nonpositive time. -/
theorem intervalNeumannFullKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x y : ℝ) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  simp [heatKernel_of_nonpos ht]

/-- The full Neumann heat propagator is the zero operator for nonpositive time. -/
theorem intervalFullSemigroupOperator_of_nonpos {t : ℝ} (ht : t ≤ 0)
    (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_of_nonpos (t := t) ht]

end ShenWork.IntervalNeumannFullKernel
```

This proof is the same shape as the existing `intervalFullSemigroupOperator_zero`, except it uses the already-landed `heatKernel_of_nonpos` instead of a zero-time lemma.

## Consequence for `conjugatePicardIter p u₀ 0`

In `ShenWork/Paper2/IntervalConjugatePicard.lean`, level `0` is defined by the full semigroup:

```lean
import ShenWork.Paper2.IntervalConjugatePicard

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

namespace ShenWork.IntervalConjugatePicard

/-- B-form Picard iteration:
`u₀(t,x) = S(t)u₀(x)`, `u_{n+1} = Φᴮ(u_n)`. -/
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
        p u₀ (conjugatePicardIter p u₀ n) t x

end ShenWork.IntervalConjugatePicard
```

After adding `intervalFullSemigroupOperator_of_nonpos`, the level-0 nonpositive-time lemma should be:

```lean
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable
import ShenWork.Paper2.IntervalConjugatePicard

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- The heat-level-0 conjugate Picard iterate is zero for nonpositive time,
because the concrete full semigroup is zero for nonpositive time. -/
theorem conjugatePicardIter_zero_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {t : ℝ} (ht : t ≤ 0) (x : intervalDomainPoint) :
    conjugatePicardIter p u₀ 0 t x = 0 := by
  change intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 = 0
  exact intervalFullSemigroupOperator_of_nonpos ht (intervalDomainLift u₀) x.1

end ShenWork.IntervalConjugatePicard
```

## Consequence for `srcTimeCoeff`

The source coefficient is defined in `ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean`:

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete

open ShenWork.PDE (intervalNeumannResolverSourceCoeff)

namespace ShenWork.IntervalPhysicalResolverDataConcrete

/-- The `k`-th **source** cosine coefficient of the chemotaxis source `ν·u(t)^γ`
in time: `srcTimeCoeff p u k t = (â_k(u t)).re`. -/
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re

end ShenWork.IntervalPhysicalResolverDataConcrete
```

The source coefficient itself is defined in `ShenWork/PDE/IntervalNeumannEllipticResolverR.lean`:

```lean
import ShenWork.PDE.IntervalNeumannEllipticResolverR

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

namespace ShenWork.PDE

/-- The `k`-th Neumann cosine coefficient of the elliptic source
`p.ν · u ^ p.γ`, viewed as a complex number. -/
def intervalNeumannResolverSourceCoeff
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) : ℂ :=
  ((ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
      (fun x : ℝ =>
        ((p.ν * intervalDomainLift u x ^ p.γ : ℝ) : ℂ)) k : ℝ) : ℂ)

end ShenWork.PDE
```

Therefore for `u = conjugatePicardIter p u₀ 0`, the previous lemma gives `u t = 0` for `t ≤ 0`, hence the integrand/source function in `intervalNeumannResolverSourceCoeff` is zero. Since `CM2Params` has `hγ : 0 < γ`, `0 ^ p.γ = 0`, so the coefficient is zero.

A convenient pair of downstream lemmas would be:

```lean
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)

noncomputable section

namespace ShenWork.IntervalPhysicalResolverDataConcrete

/-- The source coefficient of the zero interval profile is zero. -/
theorem intervalNeumannResolverSourceCoeff_zero
    (p : CM2Params) (k : ℕ) :
    ShenWork.PDE.intervalNeumannResolverSourceCoeff
      p (fun _ : intervalDomainPoint => 0) k = 0 := by
  unfold ShenWork.PDE.intervalNeumannResolverSourceCoeff
  -- `p.hγ : 0 < p.γ` makes the source `p.ν * 0 ^ p.γ` vanish.
  -- Depending on imported simp-normal forms this may close directly, or may need
  -- the local zero-lift lemma for `intervalDomainLift (fun _ => 0)`.
  simp [intervalDomainLift, Real.zero_rpow (ne_of_gt p.hγ)]

/-- For the heat-level-0 Picard iterate, `srcTimeCoeff` is zero for nonpositive time. -/
theorem srcTimeCoeff_heatLevel0_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (k : ℕ)
    {t : ℝ} (ht : t ≤ 0) :
    srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t = 0 := by
  unfold srcTimeCoeff
  have hu : conjugatePicardIter p u₀ 0 t = fun _ : intervalDomainPoint => 0 := by
    funext x
    exact ShenWork.IntervalConjugatePicard.conjugatePicardIter_zero_of_nonpos
      p u₀ ht x
  rw [hu, intervalNeumannResolverSourceCoeff_zero]
  rfl

end ShenWork.IntervalPhysicalResolverDataConcrete
```

If the `simp [intervalDomainLift, Real.zero_rpow ...]` line does not close, prove the missing helper first:

```lean
import ShenWork.PDE.IntervalDomain

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

namespace ShenWork.IntervalDomain

/-- Lifting the zero interval profile gives the zero real-line profile. -/
theorem intervalDomainLift_zero :
    intervalDomainLift (fun _ : intervalDomainPoint => 0) = fun _ : ℝ => 0 := by
  funext x
  -- Should be by unfolding the concrete lift/clamp definition.
  simp [intervalDomainLift]

end ShenWork.IntervalDomain
```

Then use:

```lean
  rw [ShenWork.IntervalDomain.intervalDomainLift_zero]
  simp [Real.zero_rpow (ne_of_gt p.hγ)]
```

## Implication for `src_contDiff`

`PhysicalSourceTimeC2` asks for global all-real smoothness:

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete

namespace ShenWork.IntervalPhysicalResolverDataConcrete

structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  /-- Each source coefficient is `C²` in time (`u^γ` smooth under the floor). -/
  src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
  /-- Three-time-order source coefficient bounds. -/
  src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k

end ShenWork.IntervalPhysicalResolverDataConcrete
```

For heat level `0`, the positive-time theorem in `ShenWork/Paper2/IntervalHeatResolverJointC2.lean` has only the form:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- The source time coefficient `srcTimeCoeff p u k` is `ContDiffAt ℝ 2` at any
positive time `t > 0` for the heat semigroup base iterate. -/
theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    {t : ℝ} (_ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  sorry

end ShenWork.Paper2.HeatResolverJointC2Direct
```

The nonpositive-time calculation does not extend this to global `ContDiff ℝ 2`. Instead it says the raw coefficient is zero on `(-∞,0]`. For generic positive `u₀`, the right limit as `t → 0+` should be the coefficient of `p.ν * u₀^γ`, not zero. Thus the raw function is not even expected to be continuous at `0`.

So the likely architectural conclusion is:

1. **Do not try to prove global `ContDiff ℝ 2` for the raw heat-level-0 coefficient** unless the initial source coefficient is zero/trivial.
2. For all-real `ContDiff` goals, use the already-visible cutoff pattern from `IntervalHeatResolverJointC2.lean`: multiply by `smoothRightCutoff (c/2) c`, where the cutoff is zero near nonpositive time and support lies in positive time.
3. Or weaken/refactor `PhysicalSourceTimeC2.src_contDiff` to a positive-time/local-on-`(0,∞)` condition if downstream only consumes positive time slabs.
4. Or redefine the level-0 time extension at `t≤0` to match the initial data and derivatives, but that is **not** the current `intervalFullSemigroupOperator` definition.

## Minimal answer to the original question

`intervalFullSemigroupOperator` at `t ≤ 0` is the zero operator, not the identity and not a constant equal to `u₀`:

```lean
intervalFullSemigroupOperator t f x = 0        -- for ht : t ≤ 0
conjugatePicardIter p u₀ 0 t x = 0            -- for ht : t ≤ 0
srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t = 0
                                                    -- expected, via zero source
```

The exact existing lemma is `heatKernel_of_nonpos`; the exact existing semigroup lemma is only `intervalFullSemigroupOperator_zero` at `t = 0`. Add `intervalFullSemigroupOperator_of_nonpos` as above if you need a named nonpositive-time rewrite.

No local `lake build` was run; this drop was produced through the GitHub connector only.
