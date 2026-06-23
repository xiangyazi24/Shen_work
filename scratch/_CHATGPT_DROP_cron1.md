# ChatGPT git-drop (cron1)

## Q82 — χ₀<0 divergence-weighted flux regularity: exact weighted-Wiener bookkeeping

### Executive verdict

Yes: the clean sufficient condition for the chemotaxis flux target

```text
Σ_k λ_k^(3/2) |sineCoeff(F)_k| < ∞,
F = W v_x,
W = u (1+v)^(-β),
v = (μ-Δ)^(-1)u,
```

is exactly

```text
u(t) ∈ A^3_cos,
```

where

```text
‖u‖_{A^3_cos} := Σ_k (1+λ_k)^(3/2) |cosineCoeff(u)_k| < ∞.
```

The bookkeeping is:

```text
u ∈ A^3_cos
  ⇒ v = R_μ u ∈ A^5_cos, hence v ∈ A^3_cos
  ⇒ v_x ∈ A^4_sin, hence v_x ∈ A^3_sin
  ⇒ (1+v)^(-β) ∈ A^3_cos               -- weighted Wiener composition/Wiener-Lévy/Moser
  ⇒ W = u(1+v)^(-β) ∈ A^3_cos          -- cosine product
  ⇒ F = W v_x ∈ A^3_sin                -- mixed cosine×sine product
  ⇒ Σ_k λ_k^(3/2)|sineCoeff(F)_k| < ∞.
```

So `u(t) ∈ A^3_cos` is the single clean per-slice sufficient condition.

Caveat: for the full nonlinear mild solution, the linear heat term from `u₀ ∈ L∞` is instantly in every `A^s`, but the Duhamel endpoint is not smoothed at `s=t`. Thus the assertion

```text
u(t) ∈ A^3 for every t>0 from u₀ ∈ L∞
```

is a genuine positive-time parabolic smoothing theorem / bootstrap theorem, not merely the observation that `e^{-tλ_k}` kills polynomial weights. It is true in the standard analytic-parabolic picture, but in Lean it should be a named theorem, not hidden inside the flux bookkeeping.

---

## 1. Definitions and weights

Let

```text
λ_k = (kπ)^2,
w_s(k) = (1+λ_k)^(s/2).
```

For a cosine coefficient sequence `a`, define

```text
‖a‖_{A^s_cos} := Σ_k w_s(k) |a_k|.
```

For a sine coefficient sequence `b`, define

```text
‖b‖_{A^s_sin} := Σ_k w_s(k) |b_k|.
```

In Lean, I would define the predicate first:

```lean
def WeightedL1 (s : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable (fun k => (1 + lam k) ^ (s / 2) * |a k|)
```

and then use separate aliases for cosine/sine only at the API level:

```lean
abbrev CosA (s : ℝ) (f : ℝ → ℝ) : Prop :=
  WeightedL1 s (cosineCoeffs f)

abbrev SinA (s : ℝ) (f : ℝ → ℝ) : Prop :=
  WeightedL1 s (sineCoeffs f)
```

Mode `k=0` is harmless for sine because `sineCoeff _ 0 = 0`, and for the divergence target because `λ_0 = 0`.

Also note:

```text
λ_k^(3/2) ≤ (1+λ_k)^(3/2) = w_3(k),
```

so

```text
F ∈ A^3_sin ⇒ Σ_k λ_k^(3/2)|sineCoeff(F)_k| < ∞.
```

This is the exact target reduction.

---

## 2. Resolver gain: exact constants

Let

```text
u_k := cosineCoeff(u)_k,
v_k := cosineCoeff(v)_k = u_k / (μ + λ_k),
μ > 0.
```

### 2.1 Two-derivative gain for `v`

Compute:

```text
w_{s+2}(k) |v_k|
  = (1+λ_k)^((s+2)/2) |u_k|/(μ+λ_k)
  = w_s(k) |u_k| * (1+λ_k)/(μ+λ_k).
```

The multiplier satisfies

```text
(1+λ)/(μ+λ) ≤ C_R(μ),
C_R(μ) := max 1 (1/μ).
```

Indeed the ratio is monotone in `λ` depending on whether `μ` is above or below `1`, and its endpoint limits are `1/μ` at `λ=0` and `1` at infinity.

Therefore

```text
‖v‖_{A^{s+2}_cos} ≤ C_R(μ) ‖u‖_{A^s_cos}.
```

A Lean-friendly theorem:

```lean
theorem resolver_cosA_gain_two
    (hμ : 0 < μ) (hu : WeightedL1 s uhat) :
    WeightedL1 (s+2) (fun k => uhat k / (μ + lam k))
```

with the proof by `Summable.of_nonneg_of_le` and the pointwise multiplier bound.

### 2.2 Zero-derivative bound for `v`

Sometimes useful:

```text
w_s(k)|v_k| = w_s(k)|u_k|/(μ+λ_k) ≤ (1/μ) w_s(k)|u_k|.
```

Thus

```text
‖v‖_{A^s_cos} ≤ μ^{-1} ‖u‖_{A^s_cos}.
```

### 2.3 One-derivative net gain for `v_x`

The sine coefficients of `v_x` are, up to sign/normalization,

```text
sineCoeff(v_x)_k = sqrt(λ_k) v_k
                 = sqrt(λ_k) u_k/(μ+λ_k).
```

Then

```text
w_{s+1}(k) |sineCoeff(v_x)_k|
  = w_s(k)|u_k| * sqrt(λ_k) sqrt(1+λ_k)/(μ+λ_k).
```

The multiplier satisfies the crude but clean bound

```text
sqrt(λ) sqrt(1+λ)/(μ+λ)
  ≤ (1+λ)/(μ+λ)
  ≤ C_R(μ),
```

because `sqrt(λ) ≤ sqrt(1+λ)`.

Therefore

```text
‖v_x‖_{A^{s+1}_sin} ≤ C_R(μ) ‖u‖_{A^s_cos}.
```

In particular:

```text
u ∈ A^3_cos ⇒ v_x ∈ A^4_sin ⇒ v_x ∈ A^3_sin,
```

and also

```text
u ∈ A^2_cos ⇒ v_x ∈ A^3_sin.
```

Since `A^3 ⊂ A^2`, `u ∈ A^3` is enough.

Lean theorem:

```lean
theorem resolver_vx_sinA_gain_one
    (hμ : 0 < μ) (hu : WeightedL1 s uhat) :
    WeightedL1 (s+1)
      (fun k => Real.sqrt (lam k) * (uhat k / (μ + lam k)))
```

Pointwise multiplier lemma:

```lean
lemma sqrt_lam_mul_sqrt_one_add_div_le
    (hμ : 0 < μ) :
  Real.sqrt (lam k) * Real.sqrt (1 + lam k) / (μ + lam k)
    ≤ max 1 μ⁻¹
```

or avoid the sharp `max` and use any finite constant already convenient in the repo.

---

## 3. Weighted Wiener product estimates

For `s ≥ 0`, the weighted Wiener space `A^s` is an algebra. The user wrote `s>1/2`; that threshold is needed when deriving ℓ¹ from an `H^s`/`MemHSigma` norm, but once the norm is already weighted ℓ¹, the product algebra works for all `s ≥ 0`.

The reason is the Peetre/submultiplicative weight estimate. If a product mode `k` arises from either

```text
k = m+n
```

or

```text
k = |m-n|,
```

then

```text
sqrt(1+λ_k) ≤ sqrt(1+λ_{m+n}) ≤ sqrt(1+λ_m) + sqrt(1+λ_n)
             ≤ 2 sqrt(1+λ_m) sqrt(1+λ_n).
```

Therefore

```text
w_s(k) ≤ 2^s w_s(m) w_s(n),      s ≥ 0.
```

This handles both the additive convolution and the cosine folding/correlation terms.

### 3.1 Cosine × cosine → cosine

There is a constant `Ccos(s)` depending only on `s` and the cosine normalization such that

```text
‖trueCosProd(a,b)‖_{A^s_cos}
  ≤ Ccos(s) ‖a‖_{A^s_cos} ‖b‖_{A^s_cos}.
```

A more useful tame version is

```text
‖trueCosProd(a,b)‖_{A^s}
  ≤ C_s (‖a‖_{A^s} ‖b‖_{A^0} + ‖a‖_{A^0} ‖b‖_{A^s}),
```

and since `A^s ⊂ A^0` for `s ≥ 0`, this implies the algebra estimate.

Lean target:

```lean
theorem weightedL1_trueCosProd
    (hs : 0 ≤ s)
    (ha : WeightedL1 s a) (hb : WeightedL1 s b) :
    WeightedL1 s (trueCosProd a b)
```

or the stronger normed estimate if you have a bundled norm.

### 3.2 Cosine × sine → sine

For the mixed product, the same bookkeeping applies. The product formula has the same additive and folded/correlation indices, with one sign change in the difference term. Absolute values absorb the sign.

Thus

```text
‖trueMixedProd(a,b)‖_{A^s_sin}
  ≤ Cmix(s) ‖a‖_{A^s_cos} ‖b‖_{A^s_sin}.
```

Lean target:

```lean
theorem weightedL1_trueMixedProd
    (hs : 0 ≤ s)
    (ha : WeightedL1 s a) (hb : WeightedL1 s b) :
    WeightedL1 s (trueMixedProd a b)
```

This is the weighted-ℓ¹ analogue of the already-landed mixed `H^σ` product algebra.

---

## 4. Composition: `(1+v)^(-β)`

You need a weighted Wiener Nemytskii/Wiener-Lévy theorem.

Let

```text
ψ(z) = (1+z)^(-β),   β ≥ 0.
```

Since `v ≥ 0`, the range of `v` is contained in `[0,R]` for some `R`, so `ψ` is smooth and in fact real analytic on an open neighborhood of the range, with no singularity near it.

The correct estimate is:

```text
‖ψ(v)‖_{A^s_cos}
  ≤ C_{s,β,R}(1 + ‖v‖_{A^s_cos}),
```

where `R ≥ ‖v‖_∞`.

For `ψ(0)=1`, the constant `1` accounts for the zero/constant mode. If one applies the theorem to `ψ(v)-ψ(0)`, the estimate is linear in `‖v‖_{A^s}`:

```text
‖ψ(v)-ψ(0)‖_{A^s} ≤ C_{s,β,R} ‖v‖_{A^s}.
```

This is a genuine analytic composition lemma. Possible proof routes:

1. **Wiener-Lévy / holomorphic functional calculus** for weighted Wiener algebras.
2. **Besov/Moser composition** for the Fourier ℓ¹ scale.
3. For integer `s=3`, a hand proof via differentiating up to order `3` plus an already-proved inverse/composition closure in `A^0`.

Do not pretend this follows from product closure alone unless `β` is a nonnegative integer and the expression is a polynomial. For real `β`, this is a real Nemytskii/Wiener-Lévy lemma.

Lean target:

```lean
theorem weightedL1_one_add_rpow_neg
    (hs : 0 ≤ s)
    (hβ : 0 ≤ β)
    (hv_nonneg : ∀ x, 0 ≤ v x)
    (hvA : WeightedL1 s (cosineCoeffs v)) :
    WeightedL1 s (cosineCoeffs (fun x => (1 + v x) ^ (-β)))
```

For estimates, expose a normed version:

```text
‖(1+v)^(-β)‖_{A^s} ≤ C(s,β,‖v‖∞) * (1 + ‖v‖_{A^s}).
```

Since the resolver gives `‖v‖∞ ≤ M/μ`, in the chemotaxis application the constant depends only on `s, β, μ, M` and the relevant `A^s` norm of `u`.

---

## 5. Bookkeeping for `W = u(1+v)^(-β)`

Assume

```text
u ∈ A^3_cos.
```

Then by resolver gain:

```text
v ∈ A^5_cos,
```

hence, by monotonicity of the weights,

```text
v ∈ A^3_cos.
```

By the composition theorem:

```text
D := (1+v)^(-β) ∈ A^3_cos,
```

with

```text
‖D‖_{A^3} ≤ C_{β,μ,M}(1 + ‖v‖_{A^3})
          ≤ C_{β,μ,M}(1 + C_R(μ) ‖u‖_{A^1})
          ≤ C_{β,μ,M}(1 + C_R(μ) ‖u‖_{A^3}).
```

Then product closure gives

```text
W = u D ∈ A^3_cos,
```

with

```text
‖W‖_{A^3}
  ≤ Ccos(3) ‖u‖_{A^3} ‖D‖_{A^3}
  ≤ C ‖u‖_{A^3} (1 + ‖u‖_{A^3}).
```

The exact polynomial dependence is not important for summability; for explicit estimates it is typically quadratic in the `A^3` size of `u`.

---

## 6. Bookkeeping for `F = W v_x`

From `u ∈ A^3_cos`, the derivative-resolver gain gives

```text
v_x ∈ A^4_sin,
```

hence

```text
v_x ∈ A^3_sin.
```

More explicitly, using only the minimal input,

```text
u ∈ A^2_cos ⇒ v_x ∈ A^3_sin.
```

Since `A^3 ⊂ A^2`, `u ∈ A^3` is enough.

Now apply the mixed product estimate:

```text
F = W v_x ∈ A^3_sin,
```

with

```text
‖F‖_{A^3_sin}
  ≤ Cmix(3) ‖W‖_{A^3_cos} ‖v_x‖_{A^3_sin}
  ≤ C ‖u‖_{A^3} (1 + ‖u‖_{A^3}) ‖u‖_{A^2}
  ≤ C ‖u‖_{A^3}^2 (1 + ‖u‖_{A^3}).
```

Thus

```text
Σ_k λ_k^(3/2) |sineCoeff(F)_k|
  ≤ Σ_k (1+λ_k)^(3/2) |sineCoeff(F)_k|
  = ‖F‖_{A^3_sin}
  < ∞.
```

This confirms the reduction:

```text
u(t) ∈ A^3_cos  ⇒  W(t)v_x(t) ∈ A^3_sin
                 ⇒  divergence-weighted source ℓ¹.
```

So, yes: **per-slice `u ∈ A^3_cos` is the single clean sufficient condition** for the chemotaxis flux source regularity package.

---

## 7. Relation to Sobolev `MemHSigma`

If you want to produce `A^3` from a Sobolev coefficient square-summability statement, the embedding is:

```text
MemHSigma q a  and  q > s + 1/2  ⇒  WeightedL1 s a.
```

Proof by Cauchy-Schwarz:

```text
Σ w_s |a_k|
  = Σ ((1+λ_k)^(q/2)|a_k|) * (1+λ_k)^((s-q)/2)
  ≤ (Σ (1+λ_k)^q a_k²)^(1/2)
     (Σ (1+λ_k)^(s-q))^(1/2).
```

Since `λ_k ~ k²`,

```text
Σ (1+λ_k)^(s-q)
```

converges iff

```text
2(q-s) > 1,
```

that is

```text
q > s + 1/2.
```

Therefore:

```text
u ∈ H^{3+1/2+ε} = H^{7/2+ε}
  ⇒ u ∈ A^3.
```

This is a sufficient Sobolev route, but for the weighted-Wiener formalization it is cleaner to work directly in `A^3`.

---

## 8. Parabolic smoothing: what is true and what must be proved

### 8.1 Linear heat part

If `u₀ ∈ L∞`, then the raw cosine coefficients satisfy a flat bound

```text
|u₀,k| ≤ C ‖u₀‖∞.
```

For the heat part,

```text
(S(t)u₀)_k = exp(-tλ_k) u₀,k.
```

Thus for every `t>0` and every `s ≥ 0`,

```text
‖S(t)u₀‖_{A^s}
  ≤ C ‖u₀‖∞ Σ_k (1+λ_k)^(s/2) exp(-tλ_k)
  < ∞.
```

The sum behaves like

```text
t^{-(s+1)/2}
```

as `t ↓ 0`. For `s=3`, it behaves like `t^{-2}`.

So the heat term is instantly in `A^3`.

### 8.2 Full nonlinear mild solution

For the full mild solution, do not argue only from the heat factor in the initial term. The Duhamel term has an endpoint `a=t` where the heat kernel has zero elapsed time:

```text
∫_0^t S(t-a) N(u(a)) da.
```

A bounded source alone does not give `A^3` at the endpoint. The smoothing is recovered by a positive-time bootstrap / analytic-semigroup regularity theorem, not by a one-line estimate using `exp(-tλ_k)`.

The clean formal theorem should be named something like:

```lean
theorem mildSolution_cosA_posTime
    (ht : 0 < t) :
    WeightedL1 3 (cosineCoeffs (u t))
```

or uniformly on positive strips:

```lean
theorem mildSolution_cosA_uniform_on_Icc_pos
    (hε : 0 < ε) (hεT : ε ≤ T) :
    ∃ C, ∀ t ∈ Set.Icc ε T,
      weightedL1Norm 3 (cosineCoeffs (u t)) ≤ C
```

This theorem is standard parabolic smoothing, but it is a genuine theorem. It should be proved by one of:

1. analytic semigroup smoothing in a weighted-Wiener scale;
2. local contraction restarted at positive time in `A^3`;
3. classical parabolic regularity strong enough to imply `A^3`, e.g. compatible `H^{7/2+ε}` or weighted Fourier decay.

Once this theorem is available, the flux source regularity follows by the algebraic chain above.

### 8.3 Uniform down to zero

Uniform `A^3` bounds on `[0,T]` require either:

```text
u₀ ∈ A^3
```

or a separate near-zero integrable-singularity statement. From `u₀ ∈ L∞` alone, one expects constants to blow up as `t ↓ 0`, even for the linear heat equation.

For many energy arguments it is enough to have the weighted source package on `[ε,T]` and then handle the initial layer separately by approximation or by local smoothing estimates with integrable singularities.

---

## 9. Lean theorem chain to formalize

I would implement the following lemmas in this order.

### Weighted Wiener infrastructure

```lean
def WeightedL1 (s : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable (fun k => (1 + lam k) ^ (s / 2) * |a k|)

theorem weightedL1_mono
    (hsr : r ≤ s) (ha : WeightedL1 s a) : WeightedL1 r a
```

### Resolver

```lean
theorem weightedL1_resolver_gain_two
    (hμ : 0 < μ) (ha : WeightedL1 s a) :
    WeightedL1 (s+2) (fun k => a k / (μ + lam k))

theorem weightedL1_resolver_deriv_gain_one
    (hμ : 0 < μ) (ha : WeightedL1 s a) :
    WeightedL1 (s+1)
      (fun k => Real.sqrt (lam k) * (a k / (μ + lam k)))
```

### Products

```lean
theorem weightedL1_trueCosProd
    (hs : 0 ≤ s)
    (ha : WeightedL1 s a) (hb : WeightedL1 s b) :
    WeightedL1 s (trueCosProd a b)

theorem weightedL1_trueMixedProd
    (hs : 0 ≤ s)
    (ha : WeightedL1 s a) (hb : WeightedL1 s b) :
    WeightedL1 s (trueMixedProd a b)
```

### Composition

```lean
theorem weightedL1_one_add_resolver_rpow_neg
    (hβ : 0 ≤ β)
    (hv_nonneg : ∀ x, 0 ≤ v x)
    (hvA : WeightedL1 s (cosineCoeffs v)) :
    WeightedL1 s
      (cosineCoeffs (fun x => (1 + v x) ^ (-β)))
```

This is the one genuinely analytic Nemytskii/Wiener-Lévy lemma.

### Flux target

```lean
theorem chemFlux_sinA3_of_u_cosA3
    (hμ : 0 < μ)
    (hβ : 0 ≤ β)
    (huA3 : WeightedL1 3 (cosineCoeffs u))
    (hv_def : cosineCoeffs v = fun k => cosineCoeffs u k / (μ + lam k))
    (hvx_def : sineCoeffs vx = fun k => Real.sqrt (lam k) * cosineCoeffs v k)
    (hden : WeightedL1 3 (cosineCoeffs (fun x => (1 + v x)^(-β))))
    (hWbridge : cosineCoeffs W = trueCosProd (cosineCoeffs u)
        (cosineCoeffs (fun x => (1 + v x)^(-β))))
    (hFbridge : sineCoeffs F = trueMixedProd (cosineCoeffs W) (sineCoeffs vx)) :
    WeightedL1 3 (sineCoeffs F)
```

Then the divergence-weighted source summability is immediate:

```lean
theorem divergence_weighted_source_l1
    (hF_A3 : WeightedL1 3 (sineCoeffs F)) :
    Summable (fun k => (lam k) ^ (3/2 : ℝ) * |sineCoeffs F k|)
```

Use pointwise:

```lean
(lam k) ^ (3/2 : ℝ) ≤ (1 + lam k) ^ (3/2 : ℝ)
```

from `lam_nonneg` and `Real.rpow_le_rpow`.

---

## Final answer

The exact gain/product chain is correct as follows:

```text
Resolver:  A^s_cos(u) → A^{s+2}_cos(v),       constant ≤ max(1,1/μ)
Derivative: A^s_cos(u) → A^{s+1}_sin(v_x),    constant ≤ max(1,1/μ)
Product:   A^s × A^s → A^s,                  for weighted Wiener A^s, s≥0
Composition: v∈A^s, v≥0 ⇒ (1+v)^(-β)∈A^s,   Wiener-Lévy/Moser lemma
Flux:      u∈A^3 ⇒ W∈A^3_cos and v_x∈A^3_sin ⇒ Wv_x∈A^3_sin
Target:    Wv_x∈A^3_sin ⇒ Σ λ_k^(3/2)|sineCoeff(Wv_x)_k| < ∞.
```

Thus **`u(t) ∈ A^3_cos` is the single clean per-slice sufficient condition** for the divergence-weighted chemotaxis source regularity.

For the mild solution, the linear heat part is instantly in `A^3` from `u₀∈L∞`, but the full nonlinear Duhamel term requires a positive-time parabolic smoothing/bootstrap theorem. On `[ε,T]`, this should yield uniform `A^3` bounds; down to `0`, either assume `u₀∈A^3` or allow the expected heat-smoothing singularity.
