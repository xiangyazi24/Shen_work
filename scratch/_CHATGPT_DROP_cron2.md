# Q1533 (cron2) — bypassing `FlooredSourceTimeData` and going directly to `PhysicalSourceTimeC2`

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

Yes, `PhysicalSourceTimeC2` can be constructed **without** `FlooredSourceTimeData`, because it is an independent structure. `physicalResolverJointC2Data_of_floor` only needs a value

```lean
H : PhysicalSourceTimeC2 p u Es
```

and then produces

```lean
PhysicalResolverJointC2Data p u
  (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

But this does **not** make the blocker disappear. It only moves the burden from the `FlooredSourceTimeData` fields

```lean
zerothBound
laplBound
```

to the direct `PhysicalSourceTimeC2` field

```lean
src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
```

with `Es` independent of `t`.

`srcTimeCoeff_contDiffAt` or any local `ContDiffAt` proof is **not enough** for `src_bound`: differentiability gives existence/identification of the derivatives, not a uniform numerical envelope. So Option B is architecturally possible, but `heatSemigroup_contDiff_four + heatSemigroup_pos_of_pos` alone does not supply `PhysicalSourceTimeC2` as currently defined.

The viable bypass is:

```text
skip FlooredSourceTimeData
prove PhysicalSourceTimeC2 directly from explicit heat-source coefficient formulas
```

but it still requires explicit global/windowed coefficient envelopes for the source coefficient and its first two time derivatives.

## What `physicalResolverJointC2Data_of_floor` actually needs

File:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

`PhysicalSourceTimeC2` is:

```lean
structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
  src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
```

Then `physicalResolverJointC2Data_of_floor` is just the constant-resolver-weight transport:

```lean
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k) where
  coeff_contDiff k := by
    have : resolverTimeCoeff p u k =
        fun t => intervalNeumannResolverWeight p k * srcTimeCoeff p u k t := by
      funext t; exact resolverTimeCoeff_eq_weight_smul p u k t
    rw [this]
    exact contDiff_const.mul (H.src_contDiff k)
  coeff_bound i k t hi :=
    resolverTimeCoeff_bound p u H.src_contDiff H.src_bound i k t hi
  value_summable := H.value_summable
  grad_summable := H.grad_summable
```

So it uses all four source fields and nothing from `FlooredSourceTimeData` directly.

The name `_of_floor` is misleading now: the theorem itself only consumes `PhysicalSourceTimeC2`; the floor was one old route for producing it.

## Generic direct constructor

A useful tiny helper would make the bypass explicit:

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete

open ShenWork.PDE (intervalNeumannResolverWeight)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointGradMajorant)

noncomputable section

namespace ShenWork.IntervalPhysicalResolverDataConcrete

/-- Direct constructor: no `FlooredSourceTimeData`, no `builtEs`.
The analytic work is entirely in `hsrcC2`, `hsrcB`, `hval`, and `hgrad`. -/
theorem physicalSourceTimeC2_direct
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (hsrcC2 : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k))
    (hsrcB : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * Es i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * Es i k) m)) :
    PhysicalSourceTimeC2 p u Es where
  src_contDiff := hsrcC2
  src_bound := hsrcB
  value_summable := hval
  grad_summable := hgrad

/-- Direct resolver producer, bypassing `FlooredSourceTimeData`. -/
theorem physicalResolverJointC2Data_direct
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (hsrcC2 : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k))
    (hsrcB : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * Es i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * Es i k) m)) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k) :=
  physicalResolverJointC2Data_of_floor
    (physicalSourceTimeC2_direct hsrcC2 hsrcB hval hgrad)

end ShenWork.IntervalPhysicalResolverDataConcrete
```

This is probably worth adding, because it decouples the resolver path from the old `FlooredSourceTimeData` route. But it is only an API cleanup; it does not prove the missing analytic estimates.

## Can `PhysicalSourceTimeC2` be built directly from heat semigroup C⁴?

Only partially.

The relevant heat facts are:

```lean
theorem heatSemigroup_contDiff_four
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 4 (fun x => ∑' k,
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x)
```

and positivity:

```lean
theorem heatSemigroup_pos_of_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

These are enough to prove **spatial** regularity of the positive-time heat profile and to justify the nonlinear chain rule in space:

```text
u(t,·) is C⁴, positive ⇒ x ↦ ν u(t,x)^γ is C⁴/C².
```

That can feed coefficient decay of the zeroth time-order source coefficient (`i = 0`) on fixed positive windows, and perhaps quartic decay if you build the H⁴ route.

But `PhysicalSourceTimeC2` needs **time** regularity and **time-derivative bounds** of the coefficient map

```lean
srcTimeCoeff p u k : ℝ → ℝ
```

where

```lean
def srcTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverSourceCoeff p (u t) k).re
```

So `src_bound` is not just a spatial C⁴ statement. For `i = 1,2`, it is asking for bounds on

```text
d/dt   cosineCoeff(ν u(t)^γ)
d²/dt² cosineCoeff(ν u(t)^γ)
```

For the heat profile these derivatives are, morally,

```text
s₀ = ν u^γ
s₁ = ν γ u^(γ-1) u_t = ν γ u^(γ-1) Δu
s₂ = ν γ(γ-1)u^(γ-2)(Δu)^2 + ν γ u^(γ-1) Δ²u.
```

`heatSemigroup_contDiff_four` helps identify `Δu` and `Δ²u` spatially at a fixed positive time, but it does not by itself provide a global-in-`t` coefficient envelope for `s₁` and `s₂`.

## Does `srcTimeCoeff_contDiffAt` give `src_bound`?

No.

In `IntervalPhysicalSourceTimeC2Concrete.lean`, the local theorem

```lean
theorem srcTimeCoeff_contDiffAt
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t
```

only proves local differentiability at a positive time. It is built from local derivative-under-integral facts:

```lean
srcTimeCoeff_hasDerivAt :
  HasDerivAt (srcTimeCoeff p u k) (cosineCoeffs (s₁ t) k) t

cosS1_hasDerivAt :
  HasDerivAt (fun s => cosineCoeffs (s₁ s) k) (cosineCoeffs (s₂ t) k) t
```

The bound theorem is separate:

```lean
theorem srcTimeCoeff_bound
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) (t : ℝ)
    (hi : i ≤ 2) (ht : 0 < t) :
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ builtEs H i k
```

and it depends exactly on `H.zerothBound` and `H.laplBound`, via:

```lean
exact (Classical.choose_spec (H.zerothBound i hi)).2 t ht
exact (Classical.choose_spec (H.laplBound i hi)).2 t ht k hk
```

So the repo already separates the two issues:

```text
srcTimeCoeff_contDiffAt  = local differentiability / derivative identity
srcTimeCoeff_bound       = uniform envelope / coefficient decay
```

The former does not imply the latter.

Also, if you bypass `FlooredSourceTimeData`, the existing `srcTimeCoeff_contDiffAt` is not directly usable anyway, because it requires `H : FlooredSourceTimeData p u s₁ s₂` and is currently in the old producer file. You would need to replicate its proof or extract a lower-level derivative-under-integral lemma.

## The real obstruction in direct `PhysicalSourceTimeC2`

If you try to construct `PhysicalSourceTimeC2` directly, the hard fields are:

```lean
hsrcB : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤ Es i k
```

and the summability of `w_k * Es i k` against the value/gradient majorants.

This is at least as strong as proving the old zeroth/laplacian bounds, because for positive time the identities are:

```text
∂ₜ⁰ srcTimeCoeff k = cosineCoeff(s₀(t)) k
∂ₜ¹ srcTimeCoeff k = cosineCoeff(s₁(t)) k
∂ₜ² srcTimeCoeff k = cosineCoeff(s₂(t)) k
```

So the old `zerothBound`/`laplBound` obligations reappear as the `k = 0` and `k ≥ 1` cases of `src_bound`, just without being named that way.

Moreover, `PhysicalSourceTimeC2.src_bound` is global in `t : ℝ`, and `Es` has no time parameter. For the heat semigroup generated from merely continuous/bounded-coefficient initial data, heat smoothing constants blow as `t → 0+`. Thus a global uniform positive-time bound for `s₁`/`s₂` is generally not available without stronger initial regularity, a positive-time window, or an explicit cutoff/restart.

There is also a global-continuity issue: `src_contDiff` asks for

```lean
ContDiff ℝ 2 (srcTimeCoeff p u k)
```

on all of `ℝ`, not just `Ioi 0`. The heat semigroup facts here are positive-time facts. If `intervalFullSemigroupOperator t` is zero for `t ≤ 0`, then at `t = 0` there is typically a jump from the zero extension to the positive initial source value. So global `ContDiff` at `0` is not expected for positive `u₀` unless the API is localized or cut off.

## Best interpretation of Option B

Option B is good as an **API bypass**:

```text
Do not build FlooredSourceTimeData.
Build PhysicalSourceTimeC2 directly.
Then apply physicalResolverJointC2Data_of_floor.
```

But it is not a proof shortcut from `heatSemigroup_contDiff_four + heatSemigroup_pos_of_pos` alone.

The direct source theorem should have hypotheses that honestly state the missing direct heat-source coefficient bounds:

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

open Set Filter Topology
open ShenWork.PDE (intervalNeumannResolverWeight)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointMajorant boundedWeightJointGradMajorant)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (PhysicalSourceTimeC2 PhysicalResolverJointC2Data srcTimeCoeff
   physicalResolverJointC2Data_of_floor)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupDirectPhysicalSource

/-- Honest direct route: bypass `FlooredSourceTimeData`, but keep the actual
source-coefficient regularity/bound/summability obligations explicit. -/
theorem heatSemigroup_physicalResolverJointC2Data_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (hsrcC2 : ∀ k,
      ContDiff ℝ (2 : ℕ∞)
        (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k))
    (hsrcB : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i
        (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤ Es i k)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * Es i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * Es i k) m)) :
    PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0)
      (fun i k => intervalNeumannResolverWeight p k * Es i k) := by
  refine physicalResolverJointC2Data_of_floor ?H
  exact {
    src_contDiff := hsrcC2
    src_bound := hsrcB
    value_summable := hval
    grad_summable := hgrad
  }

end ShenWork.Paper2.HeatSemigroupDirectPhysicalSource
```

This cleanly bypasses `heatSemigroup_flooredSourceTimeData`. But the real next theorem is to prove `hsrcC2`, `hsrcB`, `hval`, and `hgrad` for a suitable envelope `Es`.

## What direct heat proof would need

A direct positive-time theorem should be windowed, something like:

```lean
-- schematic only
theorem heatSemigroup_sourceCoeff_bounds_on_window
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {c T M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x, 0 < u₀ x)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ∃ Es : ℕ → ℕ → ℝ,
      (∀ i k t, i ≤ 2 → t ∈ Icc c T →
        ‖iteratedFDeriv ℝ i
          (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤ Es i k) ∧
      ...summability of weighted majorants...
```

On a window `t ∈ [c,T]`, heat smoothing constants are finite. Then `heatSemigroup_contDiff_four` plus the explicit heat time derivatives can plausibly give:

```text
s₀ = ν u^γ
s₁ = νγu^(γ-1)Δu
s₂ = νγ(γ-1)u^(γ-2)(Δu)^2 + νγu^(γ-1)Δ²u
```

with coefficient decay and summability.

But the existing `PhysicalSourceTimeC2` is not windowed. It asks for all `t : ℝ`, so the windowed theorem will not plug in unless you also introduce a windowed/local variant of `PhysicalSourceTimeC2` or a cutoff construction.

## Answer to the key question

> are `src_bound` estimates available from `srcTimeCoeff_contDiffAt`?

No. `srcTimeCoeff_contDiffAt` gives only local `C²` in time. It does not give any bound on the size of `∂ₜⁱ srcTimeCoeff`, and in Lean it cannot synthesize an `Es i k` independent of `t`. The old proof of `srcTimeCoeff_bound` explicitly needs `zerothBound` and `laplBound`; direct construction needs an equivalent explicit envelope hypothesis/proof.

## Recommendation

Use Option B only in the following precise form:

1. Add `physicalSourceTimeC2_direct` / `physicalResolverJointC2Data_direct` as API shims.
2. Prove or assume direct source-coefficient envelopes `hsrcB` for the heat source, preferably on a positive time window.
3. Do **not** expect `heatSemigroup_contDiff_four + heatSemigroup_pos_of_pos` to close global `PhysicalSourceTimeC2` by themselves.
4. If the downstream consumer only needs local positive-time regularity, the more honest long-term fix is a windowed/local `PhysicalSourceTimeC2On` and a windowed resolver joint-C² assembler.

So the direct bypass is valid as a design, but it does not eliminate the analytic blocker; it relocates it to the exact field `PhysicalSourceTimeC2.src_bound` and the two summability fields.
