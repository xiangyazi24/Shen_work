# Q1288 / cron1 — `intervalNeumannResolverWeight` signature and bounds

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

`intervalNeumannResolverWeight` is defined in:

```text
ShenWork/PDE/IntervalNeumannEllipticResolverR.lean
```

namespace:

```lean
namespace ShenWork.PDE
```

Exact definition:

```lean
/-- The real "resolver weight" `wₖ = 1 / (p.μ + λ_k)`.  This is the modulus of
the diagonal resolvent multiplier (all data here are real). -/
def intervalNeumannResolverWeight (p : CM2Params) (k : ℕ) : ℝ :=
  1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
```

So its exact type is:

```lean
intervalNeumannResolverWeight : CM2Params → ℕ → ℝ
```

Fully qualified name:

```lean
ShenWork.PDE.intervalNeumannResolverWeight
```

## Basic local lemmas in the defining file

Same file:

```text
ShenWork/PDE/IntervalNeumannEllipticResolverR.lean
```

### Positive denominator

```lean
/-- The denominator `p.μ + λ_k` is strictly positive. -/
lemma intervalNeumannResolver_denom_pos (p : CM2Params) (k : ℕ) :
    0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by
  have hlam : 0 ≤ unitIntervalNeumannSpectrum.eigenvalue k :=
    unitIntervalNeumannSpectrum_eigenvalue_nonneg k
  linarith [p.hμ]
```

### Nonnegativity of the weight

```lean
/-- The resolver weight is nonnegative. -/
lemma intervalNeumannResolverWeight_nonneg (p : CM2Params) (k : ℕ) :
    0 ≤ intervalNeumannResolverWeight p k :=
  le_of_lt (by
    rw [intervalNeumannResolverWeight]
    exact div_pos one_pos (intervalNeumannResolver_denom_pos p k))
```

### Square summability

```lean
/-- **The squared resolver weight is summable** (decay `~ 1/k⁴`).  This is the
genuine `ℓ²`-convergence of the multiplier sequence that powers the
absolute-convergence embedding; proved by comparison with the convergent
`p`-series `∑ 1/k⁴`. -/
lemma intervalNeumannResolverWeight_sq_summable (p : CM2Params) :
    Summable fun k : ℕ => (intervalNeumannResolverWeight p k) ^ 2 := by
  ...
```

## Bounds found by search

I did not find a theorem literally named `intervalNeumannResolverWeight_le` or `intervalNeumannResolverWeight_bound`.

The main pointwise bound is named differently:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

namespace:

```lean
namespace ShenWork.IntervalResolverJointC2PhysicalConcrete
```

### Bound by `1 / p.μ`

```lean
/-- `valueCosWeight m n · wₙ ≤ valueCosWeight m n / μ`-style: `wₙ ≤ 1/μ`. -/
theorem resolverWeight_le_inv_mu (p : CM2Params) (n : ℕ) :
    intervalNeumannResolverWeight p n ≤ 1 / p.μ := by
  unfold intervalNeumannResolverWeight
  apply div_le_div_of_nonneg_left one_pos.le p.hμ
  linarith [ShenWork.PDE.ResolventEstimate.unitIntervalNeumannSpectrum_eigenvalue_nonneg n]
```

Fully qualified name:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu
```

This is usually the theorem you want when proving a crude uniform multiplier bound.

### Eigenvalue-weighted bound `λₙ wₙ ≤ 1`

Same file:

```lean
/-- **Bounded elliptic multiplier on the eigenvalue weight.** `λ_n · wₙ ≤ 1`. -/
theorem eigenvalue_mul_resolverWeight_le_one (p : CM2Params) (n : ℕ) :
    unitIntervalNeumannSpectrum.eigenvalue n * intervalNeumannResolverWeight p n ≤ 1 := by
  have hpos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue n :=
    ShenWork.PDE.intervalNeumannResolver_denom_pos p n
  have hlam : 0 ≤ unitIntervalNeumannSpectrum.eigenvalue n :=
    ShenWork.PDE.ResolventEstimate.unitIntervalNeumannSpectrum_eigenvalue_nonneg n
  unfold intervalNeumannResolverWeight
  rw [mul_one_div, div_le_one hpos]
  linarith [p.hμ]
```

Fully qualified name:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one
```

This is the sharp bound for canceling one spatial eigenvalue with the elliptic resolvent.

### First spatial weight bound

Same file:

```lean
/-- `valueCosWeight 1 n = |nπ|` and `λ_n = (nπ)²`, so `|nπ| = √λ_n`; the AM–GM
bound `|nπ|·wₙ = |nπ|/(μ+(nπ)²) ≤ 1/(2√μ) ≤ 1/μ + 1` is what we need.  Here we
take the crude majorant `valueCosWeight 1 n · wₙ ≤ |nπ|/μ` (the order-1 envelope
is taken already `(nπ)`-decaying in the hypothesis, so the crude bound suffices). -/
theorem valueCosWeight_one_mul_resolverWeight_le (p : CM2Params) (n : ℕ) :
    valueCosWeight 1 n * intervalNeumannResolverWeight p n ≤
      |(n : ℝ) * Real.pi| / p.μ := by
  have hw : intervalNeumannResolverWeight p n ≤ 1 / p.μ := resolverWeight_le_inv_mu p n
  have hvc : valueCosWeight 1 n = |(n : ℝ) * Real.pi| := rfl
  rw [hvc]
  calc |(n : ℝ) * Real.pi| * intervalNeumannResolverWeight p n
      ≤ |(n : ℝ) * Real.pi| * (1 / p.μ) :=
        mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ = |(n : ℝ) * Real.pi| / p.μ := by rw [mul_one_div]
```

Fully qualified name:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.valueCosWeight_one_mul_resolverWeight_le
```

## Inline use in another file

`ShenWork/PDE/IntervalDuhamelSourceTimeC2Coeff.lean` contains the weighted source package:

```lean
/-- The concrete elliptic resolver multiplier preserves
`DuhamelSourceTimeC2Coeff`. -/
def duhamelSourceTimeC2Coeff_resolver_weight
    (p : CM2Params) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) :
    DuhamelSourceTimeC2Coeff
      (fun s n => intervalNeumannResolverWeight p n * a s n) :=
  duhamelSourceTimeC2Coeff_mul_weight src
    (intervalNeumannResolverWeight p) (div_nonneg zero_le_one p.hμ.le) (fun n => by
      rw [abs_of_nonneg (intervalNeumannResolverWeight_nonneg p n)]
      unfold intervalNeumannResolverWeight
      apply one_div_le_one_div_of_le p.hμ
      linarith [unitIntervalNeumannSpectrum_eigenvalue_nonneg n])
```

This proves the same bound inline:

```lean
|intervalNeumannResolverWeight p n| ≤ 1 / p.μ
```

using nonnegativity plus the definition.  If you already import `IntervalResolverJointC2PhysicalConcrete`, prefer the named theorem:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu p n
```

## Useful import/open block

For direct use:

```lean
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverWeight_nonneg
  intervalNeumannResolverWeight_sq_summable intervalNeumannResolver_denom_pos)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (resolverWeight_le_inv_mu eigenvalue_mul_resolverWeight_le_one
   valueCosWeight_one_mul_resolverWeight_le)
```

## Common proof snippets

### Show the weight is nonnegative

```lean
have hw_nonneg : 0 ≤ ShenWork.PDE.intervalNeumannResolverWeight p n :=
  ShenWork.PDE.intervalNeumannResolverWeight_nonneg p n
```

### Bound the weight by `1 / μ`

```lean
have hw_le : ShenWork.PDE.intervalNeumannResolverWeight p n ≤ 1 / p.μ :=
  ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu p n
```

### Bound the absolute value

```lean
have h_abs_weight : |ShenWork.PDE.intervalNeumannResolverWeight p n| ≤ 1 / p.μ := by
  rw [abs_of_nonneg (ShenWork.PDE.intervalNeumannResolverWeight_nonneg p n)]
  exact ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu p n
```

### Cancel one eigenvalue

```lean
have hλw : unitIntervalNeumannSpectrum.eigenvalue n *
    ShenWork.PDE.intervalNeumannResolverWeight p n ≤ 1 :=
  ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one p n
```

### Summability of squared weights

```lean
have hwsq : Summable fun k : ℕ =>
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2 :=
  ShenWork.PDE.intervalNeumannResolverWeight_sq_summable p
```

## Summary

The exact definition is:

```lean
def intervalNeumannResolverWeight (p : CM2Params) (k : ℕ) : ℝ :=
  1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
```

The most useful named bound is:

```lean
theorem resolverWeight_le_inv_mu (p : CM2Params) (n : ℕ) :
  intervalNeumannResolverWeight p n ≤ 1 / p.μ
```

in namespace:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete
```

The eigenvalue-canceling bound is:

```lean
theorem eigenvalue_mul_resolverWeight_le_one (p : CM2Params) (n : ℕ) :
  unitIntervalNeumannSpectrum.eigenvalue n * intervalNeumannResolverWeight p n ≤ 1
```

No local `lake build` was run; this drop was produced through the GitHub connector only.
