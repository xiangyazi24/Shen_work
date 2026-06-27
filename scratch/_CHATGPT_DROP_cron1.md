# Q1034 / cron1 — `DuhamelSourceTimeC2Coeff` for the heat Level0 restart source

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Verdict

For heat Level0, the `srcC2 : DuhamelSourceTimeC2Coeff a` obligation is **mechanical only after** proving a positive-time high-order coefficient-tail package for the nonlinear source and its first two time derivatives.

It is not a hard variation-of-constants problem. The variation-of-constants identity solves the restart algebra. The load-bearing part is the λ-weighted summability required by `DuhamelSourceTimeC2Coeff`.

It is also not automatic from the already-committed physical C2/quadratic-decay lane. The current physical resolver route intentionally bypasses `DuhamelSourceTimeC2Coeff`; that route gives enough bounded-weight data for physical joint C2, but not the spectral λ² envelope package.

## 1. Exact fields

`DuhamelSourceTimeC2Coeff` is in:

```text
ShenWork/PDE/IntervalResolverSpectralTimeC2.lean
```

Its fields are:

```lean
import ShenWork.PDE.IntervalResolverSpectralTimeC2

open ShenWork.IntervalResolverSpectralTimeC2

-- Structure fields, summarized from the repo:
-- structure DuhamelSourceTimeC2Coeff (a : ℝ → ℕ → ℝ) where
--   toTimeC1 : DuhamelSourceTimeC1 a
--   sourceEigenEnvelope : ℕ → ℝ
--   sourceEigen_nonneg : ∀ n, 0 ≤ sourceEigenEnvelope n
--   sourceEigen_summable : Summable sourceEigenEnvelope
--   sourceEigen_bound : ∀ s, 0 ≤ s → ∀ n,
--     λ n * |a s n| ≤ sourceEigenEnvelope n
--   sourceEigenSqEnvelope : ℕ → ℝ
--   sourceEigenSq_nonneg : ∀ n, 0 ≤ sourceEigenSqEnvelope n
--   sourceEigenSq_summable : Summable sourceEigenSqEnvelope
--   sourceEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
--     λ n * (λ n * |a s n|) ≤ sourceEigenSqEnvelope n
--   adotEigenEnvelope : ℕ → ℝ
--   adotEigen_nonneg : ∀ n, 0 ≤ adotEigenEnvelope n
--   adotEigen_summable : Summable adotEigenEnvelope
--   adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
--     λ n * |toTimeC1.adot s n| ≤ adotEigenEnvelope n
--   adotEigenSqEnvelope : ℕ → ℝ
--   adotEigenSq_nonneg : ∀ n, 0 ≤ adotEigenSqEnvelope n
--   adotEigenSq_summable : Summable adotEigenSqEnvelope
--   adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
--     λ n * (λ n * |toTimeC1.adot s n|) ≤ adotEigenSqEnvelope n
-- where λ n = unitIntervalCosineEigenvalue n.
```

The nested `toTimeC1 : DuhamelSourceTimeC1 a` contributes:

```lean
import ShenWork.PDE.IntervalDuhamelClosedC2

-- structure DuhamelSourceTimeC1 (a : ℝ → ℕ → ℝ) where
--   adot : ℝ → ℕ → ℝ
--   hderiv : ∀ s n, HasDerivAt (fun r => a r n) (adot s n) s
--   hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n)
--   envelope : ℕ → ℝ
--   henv_summable : Summable envelope
--   henv_bound : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n
--   derivBound : ℝ
--   hderivBound : ∀ s, 0 ≤ s → ∀ n, |adot s n| ≤ derivBound
```

Important correction: `DuhamelSourceTimeC2Coeff` does **not** explicitly require an `addot` field or `HasDerivAt` of `adot`. It requires `a` to be C1 through `toTimeC1`, then λ/λ² summable envelopes for `a` and for `toTimeC1.adot`.

## 2. How to get the fields for `a_k = c_k' + λ_k c_k`

Let

```text
η      = t₀ / 2,
λ_k    = unitIntervalCosineEigenvalue k,
c_k(t) = resolverTimeCoeff p (heatLevel0 p u₀) k t,
a_k(ρ) = c_k'(η + ρ) + λ_k c_k(η + ρ).
```

Use

```text
adot_k(ρ) = c_k''(η + ρ) + λ_k c_k'(η + ρ).
```

Then the C1 fields are routine:

```text
toTimeC1.adot      := adot
toTimeC1.hderiv    := chain rule for c_k' + λ_k c_k
toTimeC1.hadotcont := continuity of c_k'' and c_k'
```

The envelope fields become a bookkeeping exercise once positive-time bounds are available. If, uniformly for `ρ ≥ 0`,

```text
|c_k(η+ρ)|  ≤ C0(k),
|c_k'(η+ρ)| ≤ C1(k),
|c_k''(η+ρ)|≤ C2(k),
```

then define

```text
A(k) := C1(k) + λ_k * C0(k)   -- bounds |a_k|
D(k) := C2(k) + λ_k * C1(k)   -- bounds |adot_k|
```

and use:

```text
toTimeC1.envelope     := A
sourceEigenEnvelope   := λ_k * A(k)
sourceEigenSqEnvelope := λ_k * (λ_k * A(k))
adotEigenEnvelope     := λ_k * D(k)
adotEigenSqEnvelope   := λ_k * (λ_k * D(k))
```

The scalar `toTimeC1.derivBound` is any uniform bound for `D(k)` over all `k`; positive-time polynomial-exponential tails give such a bound.

A resolver-weight optimized version is often cleaner. Write

```text
c_k(t) = w_k * b_k(t),
w_k = 1 / (μ + Λ_k),
b_k(t) = srcTimeCoeff p u k t.
```

If `B0, B1, B2` bound `b_k, b_k', b_k''` on `t ≥ η`, then

```text
|a_k|    ≤ w_k * (B1(k) + λ_k * B0(k)),
|adot_k| ≤ w_k * (B2(k) + λ_k * B1(k)).
```

Using the elliptic estimate `λ_k * w_k ≤ 1` (modulo the repo’s two eigenvalue names), sufficient envelopes are:

```text
sourceEigenEnvelope   ≤ B1 + λ B0
sourceEigenSqEnvelope ≤ λ B1 + λ² B0
adotEigenEnvelope     ≤ B2 + λ B1
adotEigenSqEnvelope   ≤ λ B2 + λ² B1
```

Thus a strong but simple source-side target is:

```text
∀ i ∈ {0,1,2}, Summable (fun k => λ_k^2 * B_i(k)).
```

For heat Level0 this is plausible because positive time gives exponential decay. For a merely C2 source it is false in general.

## 3. Are the λ-weighted envelope fields the hard part?

Yes. The differentiability fields are mechanical from positive-time C2/C∞ coefficient regularity. The λ and λ² summability fields are the real content.

The repo already contains an audit showing the obstruction: committed quadratic source decay

```text
|a_k| ≤ C / (kπ)^2
```

only gives a constant tail after one eigenvalue weight and a growing `C * λ_k` tail after two eigenvalue weights. That is not summable. This is recorded in:

```text
ShenWork/Paper2/IntervalClampedK1SourceC2CoeffEnvelope.lean
ShenWork/Paper2/IntervalClampedK1SourceCubicBootstrap.lean
```

So `DuhamelSourceTimeC2Coeff` is stronger than the physical C2/quadratic-decay data.

For heat Level0, the missing input should be a positive-window exponential tail lemma for the nonlinear source and its time derivatives. Existing useful infrastructure includes:

```text
ShenWork/PDE/IntervalResolverSpectralTimeC2.lean
  eigenvalue_sq_mul_exp_summable
  eigenvalue_cube_mul_exp_summable

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
  heatSemigroup_eigenvalueSq_summable
  heatSemigroup_contDiff_four
  HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
  HeatSemigroupJointRegularity.eigenvalue_pow_mul_coeff_exp_summable

ShenWork/Paper2/IntervalCD6Tail.lean
  eigenvalue_fourth_mul_exp_summable
  eigenvalue_fifth_mul_exp_summable
  eigenvalue_sixth_mul_exp_summable
  eigenvalue_seventh_mul_exp_summable

ShenWork/PDE/IntervalDuhamelSourceTimeC2Coeff.lean
  duhamelSourceTimeC2Coeff_mul_weight
  duhamelSourceTimeC2Coeff_resolver_weight
```

## Recommended next target

Do not try to solve `srcC2` directly from `PhysicalSourceTimeC2`. Prove a positive-window tail package for the heat Level0 resolver coefficients or source coefficients, then instantiate `DuhamelSourceTimeC2Coeff` from those tails.

The clean target is:

```lean
import ShenWork.PDE.IntervalResolverSpectralTimeC2
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

/-
Target lemma shape:
Given η > 0 and u = conjugatePicardIter p u₀ 0, construct envelopes C0 C1 C2 such that
  |c_k(t)|  ≤ C0 k,
  |c_k'(t)| ≤ C1 k,
  |c_k''(t)|≤ C2 k
for all t ≥ η, and all weighted tails needed for
  A = C1 + λ*C0,
  D = C2 + λ*C1
are summable.
Then fill DuhamelSourceTimeC2Coeff for
  a ρ k = c_k'(η+ρ) + λ_k*c_k(η+ρ).
-/
```

Bottom line: `srcC2` is **mechanical packaging after exponential positive-time tails**; the λ² envelope tails are the real missing lemma, and existing repo infrastructure supplies the polynomial-exponential summability backend but not the full nonlinear Level0 source-tail package in one ready-made theorem.
