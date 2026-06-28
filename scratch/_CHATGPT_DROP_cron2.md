# Q1542 (cron2) — global half-line H4 majorant for `ν · (S(t)u₀)^γ`

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

Yes, for the **zeroth time-order source slice**

```text
x ↦ ν · (S(t)u₀(x))^γ
```

there should be a single finite bound

```text
B₀(c) : ℝ
```

such that

```text
∀ t ≥ c/2,
  ∫₀¹ |∂ₓ⁴ (ν · (S(t)u₀)^γ)| ≤ B₀(c).
```

The clean proof should **not** be “take a compact interval `[c/2,T]`, then use decay for `t ≥ T`.”  That is analytically true, but awkward in Lean. The better proof is direct: for every spatial derivative order `r`, the heat coefficients carry

```text
exp(-t λₙ) ≤ exp(-(c/2) λₙ)        when t ≥ c/2,
```

so all heat spatial derivatives have a uniform-in-`t ≥ c/2` spectral majorant. Then apply the explicit fourth-derivative chain rule for `z ↦ ν z^γ` under a uniform positive lower bound and a uniform upper bound for `u = S(t)u₀`.

The caveat: this answers the `m = 0` quartic source slice. For the full direct route with

```text
m = 0, 1, 2
```

one needs the same kind of bound for the time-derivative slices

```text
s₀ = ν u^γ
s₁ = ν γ u^(γ-1) Δu
s₂ = ν γ(γ-1)u^(γ-2)(Δu)^2 + ν γ u^(γ-1) Δ²u.
```

To get **quartic coefficient decay** for `s_m`, you need an `L¹` bound on `∂ₓ⁴ s_m`. Since `∂ₜ^m u = Δ^m u`, this requires heat spatial derivatives up to order

```text
4 + 2m.
```

So:

```text
m = 0 needs heat derivatives up to order 4;
m = 1 needs heat derivatives up to order 6;
m = 2 needs heat derivatives up to order 8.
```

The current `heatSemigroup_contDiff_four` only covers the `m = 0` quartic source slice. The repo has a `unitIntervalCosineHeatValue_contDiff_seven` route, which should cover up to order 7; the `m = 2` quartic route wants a C8/general-order version.

## Why the half-line bound is finite

Let

```text
u(t,x) = S(t)u₀(x).
```

For `r ≥ 1`, the `r`-th spatial derivative has the spectral form

```text
∂ₓ^r u(t,x) = Σₙ e^{-tλₙ} aₙ · ∂ₓ^r cos(nπx)
```

and

```text
|∂ₓ^r cos(nπx)| ≤ |nπ|^r.
```

If `|aₙ| ≤ M₀` and `t ≥ c/2`, then

```text
|∂ₓ^r u(t,x)|
  ≤ M₀ · Σₙ |nπ|^r · exp(-(c/2)λₙ),
```

and the sum is finite by the Gaussian/exponential tail lemma. This gives a constant

```text
G_r(c) := M₀ · Σₙ |nπ|^r · exp(-(c/2)λₙ)
```

such that

```text
∀ t ≥ c/2, ∀ x ∈ [0,1], |∂ₓ^r u(t,x)| ≤ G_r(c).
```

For `r = 0`, `u` itself does not decay to zero because the zeroth mode remains. It tends to the mean. Use the full-kernel `L∞ → L∞` contraction instead:

```text
|u(t,x)| ≤ M∞
```

where `M∞` is a bound for `|u₀|` on `[0,1]`.

For negative powers in the real-rpow chain rule, use a quantitative positive lower bound. Since `u₀` is continuous and strictly positive on compact `[0,1]`, choose

```text
δ₀ := min_{x∈[0,1]} u₀(x) > 0.
```

The full Neumann heat semigroup preserves this lower bound, so

```text
δ₀ ≤ u(t,x)
```

for all `t > 0`, `x ∈ [0,1]`.

Then every real power appearing in the chain rule

```text
u^(γ-j),  j = 1,2,3,4
```

is uniformly bounded on the range `δ₀ ≤ u ≤ M∞`.

Finally, the fourth derivative formula is

```text
∂ₓ⁴(ν u^γ)
 = νγ u^(γ-1) u₄
 + 4νγ(γ-1) u^(γ-2) u₁u₃
 + 3νγ(γ-1) u^(γ-2) u₂²
 + 6νγ(γ-1)(γ-2) u^(γ-3) u₁²u₂
 + νγ(γ-1)(γ-2)(γ-3) u^(γ-4) u₁⁴.
```

Here `u_j = ∂ₓʲu`. Bounding each `u_j` by `G_j(c)` and each power of `u` by a range constant gives a pointwise bound

```text
|∂ₓ⁴(ν u^γ)| ≤ C₄(c, p, M∞, δ₀, M₀).
```

Since the interval has length `1`, this also bounds the `L¹` integral:

```text
∫₀¹ |∂ₓ⁴(ν u^γ)| ≤ C₄(c, p, M∞, δ₀, M₀).
```

So the desired `B₀(c)` exists.

## Repo lemmas/building blocks already present

### 1. Spatial derivative mode bound and Gaussian tail summability

File:

```text
ShenWork/Paper2/IntervalCD6CosineModeBounds.lean
```

Useful lemmas:

```lean
theorem unitIntervalCosineMode_iteratedFDeriv_bound
    (k n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (unitIntervalCosineMode n) x‖ ≤
      |(n : ℝ) * Real.pi| ^ k
```

and

```lean
theorem frequency_pow_mul_exp_summable
    (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      |(n : ℝ) * Real.pi| ^ k *
        Real.exp (-τ * unitIntervalCosineEigenvalue n))
```

This is the main tail lemma for the bound

```text
Σ |nπ|^r exp(-(c/2)λₙ) < ∞.
```

### 2. Heat smoothness from bounded coefficients

File:

```text
ShenWork/Paper2/IntervalCD6HeatSmoothness.lean
```

Existing theorem:

```lean
theorem unitIntervalCosineHeatValue_contDiff_seven
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    ContDiff ℝ 7 (fun x => unitIntervalCosineHeatValue t a x)
```

This confirms the repo already has the proof pattern for high-order heat smoothing. For `m = 2` quartic bounds, however, a C8/general-order extension would be needed.

### 3. Positive-time C⁴ theorem already used

File:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

Existing theorem:

```lean
theorem heatSemigroup_contDiff_four
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 4 (fun x => ∑' k,
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x)
```

Also in this file:

```lean
theorem eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m *
        Real.exp (-τ * unitIntervalCosineEigenvalue n))
```

and private lemmas around the cutoff proof:

```lean
one_add_eigenvalue_pow_mul_exp_summable
heatTerm_iteratedFDeriv_global_bound
```

These private lemmas show exactly the desired proof style, but they are private and only for joint derivatives up to order 2. For the direct source-bound route, make a public one-dimensional version for arbitrary spatial derivative order.

### 4. Uniform upper and lower bounds for the heat semigroup

Files:

```text
ShenWork/PDE/IntervalFullKernelSupBound.lean
ShenWork/PDE/IntervalFullKernelLowerBound.lean
```

Useful upper bound:

```lean
theorem intervalFullSemigroupOperator_Linfty_bound {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalFullSemigroupOperator t f x| ≤ M
```

Useful lower bound:

```lean
theorem intervalFullSemigroupOperator_lower_bound {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {c B : ℝ} (hc : 0 ≤ c) (hcB : c ≤ B)
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_lower : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → c ≤ f y)
    (hf_bound : ∀ y, |f y| ≤ B) (x : ℝ) :
    c ≤ intervalFullSemigroupOperator t f x
```

`heatSemigroup_pos_of_pos` currently only exposes positivity, but its proof internally constructs exactly the quantitative compact minimum. For bounding real powers uniformly, expose that lower constant as a quantitative lemma rather than using only positivity.

### 5. Chain-rule quantitative source-bound style

File:

```text
ShenWork/PDE/IntervalLogisticSourceQuantBound.lean
```

This is not the same nonlinear function, but it is the right style: define an explicit derivative formula and a bound constant, then prove a pointwise bound and integrate it. For `ν z^γ`, add the fourth-derivative analogue of this file.

## The key lemma to add

The missing single key lemma should be something like this:

```lean
import ShenWork.Paper2.IntervalCD6CosineModeBounds
import ShenWork.Paper2.IntervalCD6HeatSmoothness
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelLowerBound
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.Paper2.CD6CosineModeBounds

noncomputable section

namespace ShenWork.Paper2.HeatSourceH4HalfLineBound

/-- Uniform spatial derivative bound for the heat trace on the half-line
`t ≥ τ`.  This is the primitive spectral estimate needed for every later
nonlinear source bound. -/
theorem heatTrace_spatialDeriv_bound_on_Ici
    {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ}
    (hτ : 0 < τ)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (r : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ t : ℝ, τ ≤ t → ∀ x : ℝ,
        ‖iteratedFDeriv ℝ r
          (fun y : ℝ => unitIntervalCosineHeatValue t
            (cosineCoeffs (intervalDomainLift u₀)) y) x‖ ≤ G := by
  -- Expected construction:
  --   G := |M₀| * ∑' n, |nπ|^r * exp(-τ λ_n)
  -- Use:
  --   frequency_pow_mul_exp_summable r hτ
  --   unitIntervalCosineMode_iteratedFDeriv_bound r n x
  --   exp(-tλ) ≤ exp(-τλ) for t ≥ τ.
  sorry

/-- Quantitative lower/upper range bound for the heat trace.
Expose the constants used implicitly in `heatSemigroup_pos_of_pos`. -/
theorem heatTrace_range_bound_on_pos_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ δ ≤ M ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
        δ ≤ intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ∧
        |intervalDomainLift (conjugatePicardIter p u₀ 0 t) x| ≤ M := by
  -- Proof outline:
  --   compact min/max of continuous u₀ on intervalDomainPoint;
  --   lower: intervalFullSemigroupOperator_lower_bound;
  --   upper: intervalFullSemigroupOperator_Linfty_bound;
  --   bridge by unfolding conjugatePicardIter 0 and intervalDomainLift on Icc.
  sorry

/-- Fourth-derivative chain-rule bound for `x ↦ ν * g x ^ γ` from range and
spatial derivative bounds on `g`.  This is the `ν z^γ` analogue of the style in
`IntervalLogisticSourceQuantBound`. -/
def B_pow4 (ν γ δ M G1 G2 G3 G4 : ℝ) : ℝ :=
  |ν * γ| * max (δ ^ (γ - 1)) (M ^ (γ - 1)) * G4
  + |4 * ν * γ * (γ - 1)| * max (δ ^ (γ - 2)) (M ^ (γ - 2)) * G1 * G3
  + |3 * ν * γ * (γ - 1)| * max (δ ^ (γ - 2)) (M ^ (γ - 2)) * G2 ^ 2
  + |6 * ν * γ * (γ - 1) * (γ - 2)| * max (δ ^ (γ - 3)) (M ^ (γ - 3)) * G1 ^ 2 * G2
  + |ν * γ * (γ - 1) * (γ - 2) * (γ - 3)| * max (δ ^ (γ - 4)) (M ^ (γ - 4)) * G1 ^ 4

/-- Main desired `m = 0` half-line H4 bound. -/
theorem heatSource_pow_H4_L1_bound_on_Ici
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, c / 2 ≤ t →
        ∫ x in (0 : ℝ)..1,
          |iteratedDeriv 4
            (fun y : ℝ => p.ν *
              (intervalDomainLift (conjugatePicardIter p u₀ 0 t) y) ^ p.γ) x| ≤ B := by
  -- 1. get δ,M range bounds from `heatTrace_range_bound_on_pos_time`.
  -- 2. get G1..G4 from `heatTrace_spatialDeriv_bound_on_Ici` with τ = c/2.
  -- 3. prove pointwise `|D⁴(νu^γ)| ≤ B_pow4 ...` by the chain rule.
  -- 4. integrate pointwise bound over interval length 1.
  sorry

end ShenWork.Paper2.HeatSourceH4HalfLineBound
```

The constants in `B_pow4` are schematic: in Lean, the `max (δ^a) (M^a)` terms for real exponents need a small helper saying `z ↦ z^a` is bounded on `[δ,M]` when `0 < δ ≤ z ≤ M`. It may be cleaner to choose the power-bound constants existentially:

```lean
∃ Cpow : Fin 4 → ℝ, ...
```

rather than make `max` work for all signs of `γ-j` immediately.

## Why this is better than compact-plus-tail in Lean

The proposed proof avoids selecting a large `T`. For all `t ≥ c/2`, use the monotone exponential comparison:

```text
exp(-tλₙ) ≤ exp(-(c/2)λₙ).
```

Then all estimates are uniform on the whole half-line from the start. No `tendsto`, no “eventually decays,” no supremum-attainment theorem, no compact `[c/2,T]` split.

## Relation to IBP coefficient decay

Once the half-line H4 bound is available:

```text
∫₀¹ |∂ₓ⁴(νu^γ)| ≤ B₀(c),
```

combine it with the existing quartic-decay lemma:

```lean
ShenWork.IntervalSourceDecayQuantitative
  .intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
```

or a direct classical C4 IBP version, to get

```text
|cosineCoeffs (νu(t)^γ) k| ≤ 2 * B₀(c) / ((kπ)^4),   k ≥ 1, t ≥ c/2.
```

This gives exactly the quartic envelope needed for the `m = 0` source coefficient majorant on the direct route.

## Important caveat for `m = 1,2`

For the direct route you originally want

```text
sup_{t ≥ c/2} |D_t^m srcTimeCoeff_k(t)|,   m = 0,1,2.
```

For `m = 1,2`, do not reuse only `B₀(c)`. You need analogous half-line H4 bounds for `s₁` and `s₂`:

```text
B₁(c) ≥ sup_{t≥c/2} ∫ |∂ₓ⁴ s₁(t)|,
B₂(c) ≥ sup_{t≥c/2} ∫ |∂ₓ⁴ s₂(t)|.
```

Because

```text
s₁ contains Δu,
s₂ contains Δ²u,
```

these require heat derivative bounds up to spatial orders `6` and `8` respectively. The existing `unitIntervalCosineHeatValue_contDiff_seven` is close but not enough for `m = 2`; a public arbitrary-order version of the heat derivative majorant would be the clean final tool.

Suggested general lemma:

```lean
theorem heatTrace_spatialDeriv_bound_on_Ici_any_order
    {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ}
    (hτ : 0 < τ)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (r : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ t : ℝ, τ ≤ t → ∀ x : ℝ,
        ‖iteratedFDeriv ℝ r
          (fun y : ℝ => unitIntervalCosineHeatValue t
            (cosineCoeffs (intervalDomainLift u₀)) y) x‖ ≤ G
```

This single lemma is the real engine. It uses `frequency_pow_mul_exp_summable` and handles every order, including the C8 needed for `m = 2`.

## Answer to the question

Yes, the half-line bound exists, but the key lemma is not currently a single named theorem in the repo. It should be added as a public half-line heat-derivative majorant, then combined with a fourth-derivative chain-rule bound for `ν z^γ` under uniform positive lower and upper bounds.

The closest existing building blocks are:

```text
CD6CosineModeBounds.frequency_pow_mul_exp_summable
CD6CosineModeBounds.unitIntervalCosineMode_iteratedFDeriv_bound
CD6HeatSmoothness.unitIntervalCosineHeatValue_contDiff_seven
IntervalFullKernelSupBound.intervalFullSemigroupOperator_Linfty_bound
IntervalFullKernelLowerBound.intervalFullSemigroupOperator_lower_bound
IntervalLogisticSourceQuantBound   -- proof style for quantitative chain-rule bounds
```

Do not rely on a compact-attainment argument. Use the direct spectral majorant with `exp(-(c/2)λ_n)`.
