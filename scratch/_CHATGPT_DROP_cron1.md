# ChatGPT git-drop (cron1)

## Q77 — χ₀<0 H¹ energy rebuild: divergence-weighted source regularity

### Executive verdict

No: for a classical solution with only spatial `C²` regularity, the divergence-weighted source summability

```text
Σ_k λ_k |sourceCoeff_k| < ∞
```

is **not automatic**. Bare `C²` gives at best coefficient decay `O(λ_k^{-1}) = O(k^{-2})`, and multiplying by `λ_k ~ k²` leaves a non-summable constant tail. One needs a genuine Wiener/weighted-ℓ¹ regularity input, or enough Sobolev/Hölder smoothness to imply it.

The clean sufficient condition is not “flux is `C²`”; it is one of the following coefficient-level conditions:

```text
A₂-cos condition:  Σ_k (1+λ_k) |cosCoeff(F)_k| < ∞,
```

for a cosine source `F`, or, for a divergence source written as `∂x F` with `F = W v_x` and `F(0)=F(1)=0`,

```text
A₃-sin condition:  Σ_k (1+λ_k)^(3/2) |sineCoeff(F)_k| < ∞.
```

Indeed,

```text
cosCoeff(∂x F)_k = ± sqrt(λ_k) * sineCoeff(F)_k
```

so

```text
Σ_k λ_k |cosCoeff(∂x F)_k|
  ≃ Σ_k λ_k^(3/2) |sineCoeff(F)_k|.
```

A Sobolev sufficient condition is:

```text
F ∈ H^{5/2+ε}   ⇒   Σ λ_k |cosCoeff(F)_k| < ∞,
F ∈ H^{7/2+ε}   ⇒   Σ λ_k |cosCoeff(∂xF)_k| < ∞.
```

Equivalently, in weighted Wiener notation, `F ∈ A₂` for the non-divergence source and `F ∈ A₃` for the pre-divergence flux.

For the mild/parabolic solution, the right route is therefore **not** abstract `C²` regularity. It is to exploit parabolic smoothing of the solution coefficients and then use the landed Wiener algebra product machinery to pass weighted-ℓ¹ regularity through

```text
u ↦ v = (μ-Δ)^{-1}u,
u ↦ v_x,
(u,v) ↦ W = u(1+v)^{-β},
(W,v_x) ↦ F = W v_x.
```

For every positive time strip `[ε,T]`, analytic heat smoothing should give the required weighted Wiener bounds. Uniformity down to `t=0` requires corresponding high initial regularity, or else one should settle for time-integrable singular bounds near zero. It is not a consequence of the mere `L∞` order box or `C²` classicality.

---

## 1. First correction: use the right coefficient basis for the chemotaxis flux

Let

```text
F := W v_x,
W := u(1+v)^{-β}.
```

The divergence source in the PDE is

```text
∂x F.
```

Since `v_x=0` at the Neumann endpoints, normally

```text
F(0)=F(1)=0.
```

Thus the natural spectral representation of the divergence is

```text
cosCoeff(∂x F)_k = ± sqrt(λ_k) * sineCoeff(F)_k.
```

So the natural weighted source condition is

```text
Σ_k λ_k |sqrt(λ_k) * sineCoeff(F)_k| < ∞,
```

that is

```text
Σ_k λ_k^(3/2) |sineCoeff(F)_k| < ∞.
```

If instead one literally asks for

```text
Σ_k λ_k |cosCoeff(F)_k| < ∞
```

with `F = W v_x`, this is a different and somewhat unnatural condition. It also has endpoint-compatibility traps: for a cosine expansion, two integrations by parts produce boundary terms involving `F'(0)` and `F'(1)`. Unless the Neumann-type compatibility `F'(0)=F'(1)=0` holds, `λ_k cosCoeff(F)_k` has a non-decaying oscillatory boundary contribution, so absolute summability fails immediately.

So the clean formalization should name the source package in terms of the **sine coefficients of the pre-divergence flux** or the **cosine coefficients of its divergence**, not the cosine coefficients of the pre-divergence flux.

---

## 2. Why bare `C²` is insufficient

For a scalar function `f` on `[0,1]`, a `C²` bound gives at best

```text
|cosCoeff(f)_k| ≲ k^{-2} ≃ λ_k^{-1},
```

assuming the relevant boundary terms are controlled. Then

```text
λ_k |cosCoeff(f)_k| ≲ 1,
```

and

```text
Σ_k 1
```

diverges. Therefore `C²` alone cannot prove

```text
Σ_k λ_k |cosCoeff(f)_k| < ∞.
```

This is not a Lean artifact; it is mathematically false.

A more exact way to phrase the minimal cosine condition is:

```text
f'(0)=f'(1)=0
and
f'' has absolutely summable cosine coefficients.
```

Indeed, modulo normalization constants, integration by parts gives for `k>0`

```text
λ_k cosCoeff(f)_k
  = boundary_terms_from_f'  - cosCoeff(f'')_k.
```

If the boundary terms vanish, then

```text
Σ_k λ_k |cosCoeff(f)_k| < ∞
```

is essentially the statement that `f''` belongs to the cosine Wiener algebra.

In Sobolev notation this is implied by

```text
f ∈ H^s,   s > 5/2.
```

Proof by Cauchy-Schwarz:

```text
Σ_k λ_k |c_k|
  ≤ (Σ_k (1+λ_k)^s c_k²)^{1/2}
     (Σ_k λ_k² (1+λ_k)^{-s})^{1/2}.
```

Since `λ_k ~ k²`, the second sum behaves like

```text
Σ_k k^{4-2s},
```

which converges iff

```text
4 - 2s < -1,   i.e.   s > 5/2.
```

For the divergence source `∂xF`, the corresponding condition is stronger. If

```text
cosCoeff(∂xF)_k = sqrt(λ_k) sineCoeff(F)_k,
```

then

```text
Σ_k λ_k |cosCoeff(∂xF)_k|
  = Σ_k λ_k^(3/2) |sineCoeff(F)_k|.
```

A Sobolev sufficient condition is then

```text
F ∈ H^s,   s > 7/2.
```

Again by Cauchy-Schwarz:

```text
Σ_k λ_k^(3/2) |s_k|
  ≤ (Σ_k (1+λ_k)^s s_k²)^{1/2}
     (Σ_k λ_k^3 (1+λ_k)^{-s})^{1/2},
```

and the second sum behaves like

```text
Σ_k k^{6-2s},
```

which converges iff

```text
6 - 2s < -1,   i.e.   s > 7/2.
```

### Hölder/BV sufficient conditions

For the non-divergence cosine condition, it is enough to have coefficient decay

```text
|cosCoeff(f)_k| ≤ C k^{-3-ε}
```

for some `ε>0`. This follows from, for example, a compatible `C^{3,α}` periodic/even extension with `α>0`, or from a condition like “the relevant third derivative has a little more than bounded variation/Dini control” depending on the exact Fourier theorem you formalize.

For the divergence source, since one needs

```text
|sineCoeff(F)_k| = O(k^{-4-ε}),
```

a compatible `C^{4,α}`-type condition is a safe classical sufficient condition.

Do **not** claim `C^{2,1}` is enough for the non-divergence condition: it gives at best a borderline `k^{-3}` coefficient decay, and

```text
Σ_k k² k^{-3} = Σ_k 1/k
```

still diverges.

---

## 3. Weighted Wiener formulation: the cleanest Lean target

Define weighted ℓ¹ coefficient classes.

For cosine coefficients:

```lean
def CosA (r : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable (fun k => (1 + lam k) ^ (r/2) * |a k|)
```

For sine coefficients, the same definition with `sineCoeffs`.

Then the source hypotheses become clean:

```text
CosA 2 (cosineCoeffs F)
```

for a direct cosine source `F`, and

```text
SinA 3 (sineCoeffs F)
```

for a divergence source `∂xF` represented by the sine coefficients of the flux `F`.

Sobolev-to-Wiener embedding:

```lean
theorem weightedL1_of_memHSigma
    (h : MemHSigma s a) (hrs : r + 1/2 < s) :
    Summable (fun k => (1 + lam k)^(r/2) * |a k|)
```

The proof is just Cauchy-Schwarz with

```text
(1+λ)^(r/2)|a_k|
  = ((1+λ)^(s/2)|a_k|) * (1+λ)^((r-s)/2),
```

and

```text
Σ_k (1+λ_k)^{r-s} < ∞
```

iff `s-r > 1/2`.

Product closure should be formulated as weighted Wiener algebra estimates:

```lean
CosA r a → CosA r b → CosA r (trueCosProd a b)
CosA r a → SinA r b → SinA r (trueMixedProd a b)
```

for `r ≥ 0`, using the same Peetre/submultiplicative weight estimates already used for the `H^σ`, `σ>1/2`, product algebra. This is the correct coefficient-level infrastructure for the source regularity package.

---

## 4. Applying the weighted Wiener route to `F = W v_x`

Let

```text
F = W v_x,
W = u (1+v)^(-β),
v = (μ-Δ)^(-1)u.
```

For the divergence source package, it suffices to prove

```text
F ∈ A₃^sin,
```

that is

```text
Σ_k (1+λ_k)^(3/2) |sineCoeff(F)_k| < ∞.
```

A clean sufficient chain is:

1. `u ∈ A₃^cos`.
2. The resolver gives `v ∈ A₅^cos` and `v_x ∈ A₄^sin`; in particular `v_x ∈ A₃^sin`.

   Modewise,

   ```text
   sineCoeff(v_x)_k ≃ sqrt(λ_k) * u_k / (μ+λ_k),
   ```

   so `v_x` gains one derivative in weighted Wiener scale.

3. Since `v ≥ 0`, the function `z ↦ (1+z)^(-β)` is smooth on the range. A Wiener/Nemytskii composition theorem gives

   ```text
   (1+v)^(-β) ∈ A₃^cos.
   ```

   In a Lean build, this is a real lemma: either prove it as a smooth composition theorem in weighted Wiener algebra, or route through stronger regularity estimates that imply `A₃`.

4. Product closure gives

   ```text
   W = u * (1+v)^(-β) ∈ A₃^cos.
   ```

5. Mixed cosine×sine product closure gives

   ```text
   F = W * v_x ∈ A₃^sin.
   ```

6. Therefore

   ```text
   cosCoeff(∂xF)_k = sqrt(λ_k) sineCoeff(F)_k
   ```

   satisfies

   ```text
   Σ_k λ_k |cosCoeff(∂xF)_k| < ∞.
   ```

This is the cleanest derivation. It uses the solution’s smoothed weighted coefficients and the Wiener algebra, not bare classical `C²` regularity.

For the weaker non-divergence condition

```text
Σ_k λ_k |cosCoeff(F)_k| < ∞,
```

it would suffice to prove `F ∈ A₂^cos`, but again `F = W v_x` is naturally sine-type, so the divergence/sine formulation is preferred.

---

## 5. What parabolic smoothing gives for the mild solution

For the mild solution, parabolic smoothing is the right source of the missing weighted-ℓ¹ regularity.

For the heat part,

```text
u_k^heat(s) = exp(-s λ_k) u₀,k.
```

For every `s > 0`, the exponential factor gives arbitrary weighted ℓ¹ summability even if `u₀` has only low regularity. For each `ε > 0`, the bound is uniform on `[ε,T]`:

```text
sup_{s∈[ε,T]} Σ_k (1+λ_k)^(r/2) |exp(-sλ_k) u₀,k| < ∞.
```

The constant blows up as `ε ↓ 0` unless `u₀` already has the corresponding weighted ℓ¹ regularity.

For the Duhamel terms, the same principle applies, but the endpoint `a=s` in

```text
∫_0^s exp(-(s-a)λ_k) source_k(a) da
```

has no smoothing at the instant `a=s`. Thus one either:

- bootstraps parabolic regularity on positive time strips `[ε,T]`, where the solution is already smoother, or
- proves time-integrable singular estimates near `0`, or
- assumes enough initial regularity to make the bound uniform down to `0`.

Consequently:

```text
For every ε>0:   weighted source ℓ¹ is expected uniformly on [ε,T].
For [0,T]:       uniformity requires compatible high initial regularity, or a separate near-zero argument.
```

So the mild solution does inherit enough smoothing for `s>0`, but this is a parabolic smoothing theorem / coefficient-bootstrap theorem. It is not a consequence of `C²` alone.

---

## 6. Time-C¹ coefficient regularity and derivative bounds

The package you describe also wants time-C¹ cosine coefficients and a uniform/integrable time derivative bound. This is again not automatic from spatial `C²`.

A sufficient coefficient-level hypothesis is:

```text
s ↦ sourceCoeff_k(s) is C¹ for every k,
Σ_k λ_k |sourceCoeff_k(s)| ≤ G(s),
Σ_k λ_k |∂_s sourceCoeff_k(s)| ≤ G₁(s),
```

with `G`, `G₁` bounded or integrable on the relevant time interval.

For a classical parabolic solution, this follows if the solution has enough mixed time-space regularity on the interval in question. For a mild solution, the clean proof is again through positive-time analytic smoothing and differentiating the coefficient ODE/PDE modewise. On `[ε,T]`, this should be obtainable from parabolic regularity. Uniformly down to `0`, it requires correspondingly regular initial data or tolerating an integrable singularity.

Lean-wise, do not hide this under `C²`. State the actual coefficient package or prove it from weighted Wiener smoothing.

---

## 7. Minimal sufficient conditions, summarized

### If the source is a direct cosine source `F`

A precise coefficient condition:

```text
Σ_k λ_k |cosCoeff(F)_k| < ∞.
```

Sufficient function-space conditions:

```text
F ∈ H^{5/2+ε}
```

or

```text
F' endpoint-compatible and F'' in the cosine Wiener algebra.
```

Safe classical condition:

```text
compatible C^{3,α}, α>0.
```

### If the source is a divergence `∂xF`, with `F = W v_x`

Natural coefficient condition:

```text
Σ_k λ_k |cosCoeff(∂xF)_k| < ∞
```

equivalently, using `F(0)=F(1)=0`,

```text
Σ_k λ_k^(3/2) |sineCoeff(F)_k| < ∞.
```

Sufficient function-space condition:

```text
F ∈ H^{7/2+ε}
```

or coefficient-level:

```text
F ∈ A₃^sin.
```

Safe classical condition:

```text
compatible C^{4,α}, α>0.
```

### For `F = W v_x`

Clean weighted-Wiener sufficient condition:

```text
u ∈ A₃^cos,
v = R u,
v_x ∈ A₃^sin,
(1+v)^(-β) ∈ A₃^cos,
W = u(1+v)^(-β) ∈ A₃^cos,
F = W v_x ∈ A₃^sin.
```

Then the divergence-weighted source ℓ¹ follows immediately.

---

## 8. Lean-oriented theorem targets

I would add the following abstract lemmas rather than trying to squeeze this out of `C²`.

### Weighted ℓ¹ scale

```lean
def WeightedL1 (r : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable (fun k => (1 + lam k) ^ (r / 2) * |a k|)
```

### Sobolev to weighted ℓ¹

```lean
theorem weightedL1_of_memHSigma
    (ha : MemHSigma s a) (hrs : r + (1/2 : ℝ) < s) :
    WeightedL1 r a
```

### Divergence transfer

```lean
theorem divergence_weightedL1_of_flux_sine_A3
    (hF : WeightedL1 3 (sineCoeffs F))
    (hboundary : F 0 = 0 ∧ F 1 = 0)
    (hdiv : ∀ k, cosineCoeffs (deriv F) k = Real.sqrt (lam k) * sineCoeffs F k) :
    Summable (fun k => lam k * |cosineCoeffs (deriv F) k|)
```

Mode `k=0` is harmless since `lam 0 = 0`.

### Product closures

```lean
theorem weightedL1_trueCosProd
    (ha : WeightedL1 r a) (hb : WeightedL1 r b) (hr : 0 ≤ r) :
    WeightedL1 r (trueCosProd a b)

theorem weightedL1_trueMixedProd
    (ha : WeightedL1 r a) (hb : WeightedL1 r b) (hr : 0 ≤ r) :
    WeightedL1 r (trueMixedProd a b)
```

These are weighted-ℓ¹ analogues of the existing `H^σ` product algebra. They should be easier than the `H^σ` proof: use submultiplicative/Peetre weights and ℓ¹ convolution estimates.

### Resolver transfer

```lean
theorem weightedL1_vx_of_u
    (hu : WeightedL1 (r - 1) (cosineCoeffs u)) :
    WeightedL1 r (sineCoeffs vx)
```

because the multiplier for `v_x` is `sqrt λ /(μ+λ)`, which gains one derivative.

### Composition theorem

For the denominator:

```lean
theorem weightedL1_one_add_resolver_rpow_neg
    (hv : WeightedL1 r (cosineCoeffs v))
    (hbase : ∀ x, 0 ≤ v x)
    (hβ : 0 ≤ β)
    (hr : suitable, e.g. r is integer or r > 1/2 with a proved Wiener composition theorem) :
    WeightedL1 r (cosineCoeffs (fun x => (1 + v x)^(-β)))
```

This is a genuine analytic lemma. If proving a full Nemytskii theorem is too much, use the stronger positive-time smoothing/classical `C^{m,α}` route as a temporary producer.

---

## Final answer

The carried divergence-weighted source regularity is **not automatic** from a bounded classical `C²` solution. It requires genuinely higher regularity: at least `H^{5/2+ε}` for a direct cosine source, and `H^{7/2+ε}` for a pre-divergence flux whose divergence coefficients are weighted by an extra `sqrt λ`. Equivalently, it requires membership in a weighted Wiener algebra: `A₂` for a direct cosine source, `A₃` for the sine coefficients of the pre-divergence flux.

For the mild solution, the right way to obtain it is through parabolic smoothing of the solution’s coefficients and weighted Wiener product/ composition estimates. On positive time strips `[ε,T]`, this should hold with constants depending on `ε`. Uniformity down to `0` needs high initial regularity or a separate integrable-singularity argument. Bare `C²` and the `L∞` order box are not enough.
