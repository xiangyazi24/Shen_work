# Q2865 (cron1) — Mathlib names for the Moser/Agmon absorption step

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

I checked the repository pin first. `lake-manifest.json` on `chatgpt-scratch` pins Mathlib to `v4.29.1`, commit

```text
5e932f97dd25535344f80f9dd8da3aab83df0fe6
```

The names below are for that Mathlib version.

## First correction: `p₀ > ρ/2` does not imply `ρ < p`

The proposed route says `α = ρ / p` and then wants `α < 1`, i.e. `ρ < p`. But from

```text
p ≥ p₀  and  p₀ > ρ/2
```

you only get

```text
p > ρ/2,
```

not `p > ρ`. So the statement “`ρ < p`, which holds since `p ≥ p₀ > ρ/2`” is not Lean-provable and is mathematically false.

There are two honest options:

1. Strengthen the hypothesis to `ρ < p₀`, hence `ρ < p` for every `p ≥ p₀`; then `α < 1` and the clean concave-power lemma applies directly.
2. Keep the weaker hypothesis `p₀ > ρ/2`; then the useful exponent is usually `α / 2 = ρ / (2*p) < 1`, because the Agmon bound has a `sqrt G` term. In this case you may need a separate sum bound for `1 ≤ α < 2`, not only the concave `α ≤ 1` case.

The exact Mathlib names below cover both regimes.

## Imports

The relevant declarations are available from these imports:

```lean
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Compact
```

`Mathlib.Analysis.MeanInequalities` gives Young/Hölder-conjugate APIs.  
`Mathlib.Analysis.MeanInequalitiesPow` gives the finite-sum/power inequalities.  
`Mathlib.Topology.Order.Compact` gives compact-image `sSup`/maximum APIs.

## 1. Real `rpow` of a sum, `0 ≤ α ≤ 1`

Use:

```lean
Real.rpow_add_le_add_rpow
```

Exact shape in Mathlib `v4.29.1`:

```lean
lemma Real.rpow_add_le_add_rpow
    {p : ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p
```

Typical use:

```lean
have hsum : (A + G) ^ α ≤ A ^ α + G ^ α :=
  Real.rpow_add_le_add_rpow hA_nonneg hG_nonneg hα_nonneg (le_of_lt hα_lt_one)
```

The `NNReal` version has the same name in namespace `NNReal`:

```lean
NNReal.rpow_add_le_add_rpow
```

Exact shape:

```lean
theorem NNReal.rpow_add_le_add_rpow
    {p : ℝ} (a b : ℝ≥0)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p
```

### If only `p₀ > ρ/2` is available

Then `α = ρ/p` may be in `[1,2)`. For the non-concave sum split, use the `NNReal` theorem:

```lean
NNReal.rpow_add_le_mul_rpow_add_rpow
```

Exact shape:

```lean
theorem NNReal.rpow_add_le_mul_rpow_add_rpow
    (z₁ z₂ : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (z₁ + z₂) ^ p ≤ (2 : ℝ≥0) ^ (p - 1) * (z₁ ^ p + z₂ ^ p)
```

There is no equally-named `Real` wrapper in this Mathlib pin. If you want a real-valued version, lift `a` and `b` to `ℝ≥0` and `exact_mod_cast` back. Local wrapper shape:

```lean
import Mathlib.Analysis.MeanInequalitiesPow

noncomputable section

lemma real_rpow_add_le_mul_rpow_add_rpow_of_nonneg
    {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hp
```

This is the right backup when `α < 1` is unavailable but `α < 2` is available, because after Agmon the gradient piece often becomes `G ^ (α/2)`, and `α/2 < 1` follows from `p > ρ/2`.

Useful companion names for simplifying powers:

```lean
Real.rpow_le_rpow
Real.rpow_lt_rpow
Real.rpow_le_rpow_iff
Real.rpow_mul
Real.mul_rpow
Real.rpow_nonneg
Real.rpow_inv_rpow
Real.rpow_rpow_inv
```

## 2. Young inequality / ε-absorption

Use:

```lean
Real.young_inequality_of_nonneg
```

Exact shape:

```lean
theorem Real.young_inequality_of_nonneg
    {a b p q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / p + b ^ q / q
```

There is also the absolute-value version:

```lean
theorem Real.young_inequality
    (a b : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q
```

For nonnegative-valued versions:

```lean
NNReal.young_inequality
NNReal.young_inequality_real
ENNReal.young_inequality
```

### Constructing the conjugate exponents

For `0 < α`, `0 < β`, `α + β = 1`, the most direct constructor is:

```lean
Real.HolderConjugate.inv_inv
```

Exact shape:

```lean
protected lemma Real.HolderConjugate.inv_inv
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a⁻¹.HolderConjugate b⁻¹
```

For the common special case `β = 1 - α`, use:

```lean
Real.HolderConjugate.inv_one_sub_inv
Real.HolderConjugate.one_sub_inv_inv
```

Exact shapes:

```lean
lemma Real.HolderConjugate.inv_one_sub_inv
    (ha₀ : 0 < a) (ha₁ : a < 1) :
    a⁻¹.HolderConjugate (1 - a)⁻¹

lemma Real.HolderConjugate.one_sub_inv_inv
    (ha₀ : 0 < a) (ha₁ : a < 1) :
    (1 - a)⁻¹.HolderConjugate a⁻¹
```

Also useful:

```lean
Real.holderConjugate_iff
Real.HolderConjugate.conjExponent
Real.HolderConjugate.symm
Real.HolderConjugate.inv_add_inv_eq_one
Real.HolderConjugate.pos
Real.HolderConjugate.nonneg
Real.HolderConjugate.ne_zero
```

### ε-form is not a single Mathlib lemma

I did not find a built-in lemma named like `young_inequality_eps` or `young_inequality_with_epsilon`. The expected Lean route is to prove a tiny local helper from `Real.young_inequality_of_nonneg` by scaling.

For product absorption, if `0 < α`, `0 < β`, `α + β = 1`, `ε > 0`, and `K ≥ 0`, prove a local helper of the form

```lean
K * x ^ α * y ^ β ≤ ε * x + Cε * y
```

by applying Young to

```lean
(λ * x ^ α) * ((K / λ) * y ^ β)
```

with

```lean
λ = ((α⁻¹) * ε) ^ (1 / α⁻¹)
```

or any equivalent positive scaling chosen so that the first Young term simplifies to `ε * x`.

Skeleton, not meant as a drop-in theorem without the routine algebra filled in:

```lean
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Real

-- Local helper shape: prove this once and reuse it.
lemma young_scaled_product_route
    {α β ε K x y : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1)
    (hε : 0 < ε) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧ K * x ^ α * y ^ β ≤ ε * x + Cε * y := by
  let P : ℝ := α⁻¹
  let Q : ℝ := β⁻¹
  have hPQ : P.HolderConjugate Q := by
    simpa [P, Q] using Real.HolderConjugate.inv_inv hα hβ hαβ
  -- Apply:
  --   Real.young_inequality_of_nonneg
  -- to
  --   a := λ * x ^ α
  --   b := (K / λ) * y ^ β
  -- with λ chosen positive and λ ^ P / P = ε.
  -- Then simplify with:
  --   Real.mul_rpow, Real.rpow_mul, Real.rpow_inv_rpow,
  --   hPQ.ne_zero, hPQ.symm.ne_zero, field_simp/ring_nf.
  classical
  refine ⟨0, le_rfl, ?_⟩
  -- This file is an audit of exact Mathlib names, not a compiled helper implementation.
  -- Replace this placeholder with the scaled Young algebra in the target repo.
  sorry
```

For the simpler absorption

```lean
K * x ^ γ ≤ ε * x + Cε
```

use the same theorem with `β = 1 - γ` and `y = 1`, or apply `Real.young_inequality_of_nonneg` to

```lean
a := λ * x ^ γ
b := K / λ
```

with conjugates

```lean
γ⁻¹   and   (1 - γ)⁻¹
```

constructed by

```lean
Real.HolderConjugate.inv_one_sub_inv hγ_pos hγ_lt_one
```

This is the cleanest local lemma for absorbing `G ^ θ` into `ε * G + Cε` when `0 < θ < 1`.

## 3. Pulling `sSup` out of a pointwise bound

The core order lemmas are:

```lean
csSup_le
le_csSup
```

Exact useful shapes over `ℝ`/conditionally complete lattices:

```lean
theorem csSup_le
    (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) :
    sSup s ≤ a

theorem le_csSup
    (h₁ : BddAbove s) (h₂ : a ∈ s) :
    a ≤ sSup s
```

For image sets, the key membership lemma is:

```lean
Set.mem_image_of_mem
```

Typical pattern for a compact interval or any nonempty domain `K`:

```lean
import Mathlib.Topology.Order.Compact

noncomputable section

open Set

variable {K : Set ℝ} {φ : ℝ → ℝ} {B : ℝ}

lemma sSup_image_le_of_pointwise
    (hKne : K.Nonempty)
    (hφB : ∀ x ∈ K, φ x ≤ B) :
    sSup (φ '' K) ≤ B := by
  refine csSup_le (hKne.image φ) ?_
  rintro y ⟨x, hxK, rfl⟩
  exact hφB x hxK

lemma pointwise_le_sSup_image_of_bdd
    (hBdd : BddAbove (φ '' K))
    {x : ℝ} (hxK : x ∈ K) :
    φ x ≤ sSup (φ '' K) := by
  exact le_csSup hBdd (mem_image_of_mem φ hxK)
```

If you need boundedness of a continuous image of a compact set, use:

```lean
IsCompact.bddAbove_image
```

Exact shape:

```lean
theorem IsCompact.bddAbove_image
    [ClosedIciTopology α] [Nonempty α]
    {f : β → α} {K : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddAbove (f '' K)
```

For `[0,1]`, compactness is:

```lean
isCompact_Icc
```

If you want the supremum to be attained, use:

```lean
IsCompact.exists_sSup_image_eq_and_ge
IsCompact.exists_sSup_image_eq
IsCompact.exists_isMaxOn
```

The most relevant one is:

```lean
theorem IsCompact.exists_sSup_image_eq_and_ge
    [ClosedIciTopology α]
    {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty)
    {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, sSup (f '' s) = f x ∧ ∀ y ∈ s, f y ≤ f x
```

There is no need to “pull `sSup` through” `rpow` as an equality. Usually the Lean-friendly route is:

1. prove `φ x ≤ sSup (φ '' K)` by `le_csSup`,
2. apply monotonicity of `Real.rpow` using `Real.rpow_le_rpow`,
3. prove `sSup (φ '' K) ≤ B` by `csSup_le`,
4. again apply `Real.rpow_le_rpow` if needed.

## Recommended proof route for the Moser step

Let

```text
G := ∫ |∇(f^(p/2))|²
I := ∫ f^p
S := sSup ((fun x => f x ^ p) '' Set.Icc (0:ℝ) 1)
α := ρ / p
```

From the pointwise Agmon estimate, prove

```lean
S ≤ 2 * I + 2 * Real.sqrt I * Real.sqrt G
```

using `csSup_le` on the image. Then compare pointwise values to `S` using `le_csSup` if needed.

For the power of the sum:

* If you have `ρ < p`, use

```lean
Real.rpow_add_le_add_rpow
```

with exponent `α = ρ/p`.

* If you only have `ρ < 2*p`, use the `NNReal.rpow_add_le_mul_rpow_add_rpow` route for the sum split, then absorb the gradient contribution with exponent `α/2 < 1`.

For the absorption step, prove a local lemma from

```lean
Real.young_inequality_of_nonneg
```

with conjugates made by

```lean
Real.HolderConjugate.inv_one_sub_inv
```

or

```lean
Real.HolderConjugate.inv_inv
```

The local lemma should have one of these two forms:

```lean
lemma absorb_rpow_lt_one
    {θ ε K : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ Cε : ℝ, ∀ G : ℝ, 0 ≤ G → K * G ^ θ ≤ ε * G + Cε
```

or the weighted product version:

```lean
lemma young_scaled_product
    {α β ε K : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1)
    (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ Cε : ℝ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      K * x ^ α * y ^ β ≤ ε * x + Cε * y
```

## Bottom line

Exact names to use:

```lean
-- sum powers
Real.rpow_add_le_add_rpow
NNReal.rpow_add_le_add_rpow
NNReal.rpow_add_le_mul_rpow_add_rpow

-- Young
Real.young_inequality_of_nonneg
Real.young_inequality
NNReal.young_inequality
NNReal.young_inequality_real
ENNReal.young_inequality

-- conjugate exponent constructors/facts
Real.HolderConjugate.inv_inv
Real.HolderConjugate.inv_one_sub_inv
Real.HolderConjugate.one_sub_inv_inv
Real.holderConjugate_iff
Real.HolderConjugate.conjExponent
Real.HolderConjugate.symm
Real.HolderConjugate.inv_add_inv_eq_one

-- sSup/image/compact maximum
csSup_le
le_csSup
Set.mem_image_of_mem
isCompact_Icc
IsCompact.bddAbove_image
IsCompact.exists_sSup_image_eq_and_ge
IsCompact.exists_sSup_image_eq
IsCompact.exists_isMaxOn

-- rpow algebra/monotonicity helpers
Real.rpow_le_rpow
Real.rpow_lt_rpow
Real.rpow_le_rpow_iff
Real.rpow_mul
Real.mul_rpow
Real.rpow_nonneg
Real.rpow_inv_rpow
Real.rpow_rpow_inv
```

The single biggest Lean-side issue is not finding the names; it is choosing the right exponent hypothesis. If the proof really uses `Real.rpow_add_le_add_rpow` at exponent `α = ρ/p`, then the theorem needs `ρ < p`, globally e.g. `ρ < p₀`. If the intended PDE hypothesis is only `p₀ > ρ/2`, then do not insist on `α < 1`; split the Agmon sum with the `NNReal.rpow_add_le_mul_rpow_add_rpow` fallback and absorb the `G ^ (α/2)` term using Young, since `α/2 < 1` is exactly what `p > ρ/2` gives.
