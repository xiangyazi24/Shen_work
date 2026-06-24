# ChatGPT git-drop (cron1)

## Q112 — χ₀<0 chemotaxis divergence source: time-C¹ coefficient package

### Executive verdict

The chemotaxis source time-C¹ theorem is **formally the same opaque/integral-swap pattern** once the pointwise time derivative and a weighted coefficient majorant are available. There is no new `whnf`/`realSlice` obstacle inherent in the divergence.

But there **is** a genuine analytic derivative-loss: because

```text
S_chem = ∂x q,
q := u v_x (1+v)^(-β),
```

one should prove the time derivative at the pre-divergence flux level and then use the sine/cosine divergence identity

```text
cosineCoeff(∂x q)_n = ± sqrt(λ_n) sineCoeff(q)_n.
```

Thus a coefficient package for `S_chem` at weight `r` requires the pre-divergence quantity `q` and its time derivative to be controlled in sine `A^{r+1}`. In particular, for the divergence-weighted source regularity

```text
Σ_n λ_n |cosineCoeff(S_chem)_n| < ∞,
```

a clean sufficient condition is

```text
q_t ∈ A^3_sin.
```

This is not supplied by bare `C²`; it is a weighted Wiener/positive-time smoothing input. The actual Lean trick is the same; the analytic envelope is stronger.

---

## 1. Exact time derivative formula

Set

```text
D      := (1+v)^(-β),
D₁     := (1+v)^(-β-1),
q      := u v_x D,
S_chem := ∂x q.
```

Let

```text
U := u_t,
V := v_t = (μ-Δ_N)^(-1) U,
V_x := ∂x V.
```

Since the resolver is linear and time-independent,

```text
cosineCoeff(V)_n = cosineCoeff(U)_n / (μ + λ_n),
sineCoeff(V_x)_n = ± sqrt(λ_n) cosineCoeff(V)_n.
```

Differentiate `q = u v_x D` in time:

```text
q_t
  = U v_x D
    + u V_x D
    + u v_x D_t.
```

The denominator derivative is

```text
D_t = -β (1+v)^(-β-1) V = -β D₁ V.
```

Therefore the exact pointwise formula is

```text
q_t
  = D * U * v_x
    + D * u * V_x
    - β * D₁ * u * v_x * V.
```

Equivalently,

```text
q_t = D * (U*v_x + u*V_x - β*u*v_x*V/(1+v)).
```

Now use the divergence identity. Since `v_x=0` at the Neumann endpoints and also `V_x=0`, both `q` and `q_t` vanish at the endpoints, so the sine/divergence coefficient identity is the right basis statement.

For every mode `n`, with the sign fixed by your repo’s convention,

```text
d/dt cosineCoeff(S_chem(t))_n
  = cosineCoeff(∂x q_t(t))_n
  = ± sqrt(λ_n) * sineCoeff(q_t(t))_n.
```

Thus the formula to formalize is:

```lean
-- schematic, sign hidden behind the repo's divergence-mode identity
HasDerivAt
  (fun t => cosineCoeffs (Schem t) n)
  (divSign n * Real.sqrt (lam n) * sineCoeffs (qdot t) n)
  t
```

where

```lean
qdot t x =
    (1 + v t x)^(-β) * U t x * vx t x
  + (1 + v t x)^(-β) * u t x * Vx t x
  - β * (1 + v t x)^(-β - 1) * u t x * vx t x * V t x
```

and

```lean
V  t = resolver μ (U t)
Vx t = deriv (V t)
```

in whatever coefficient/function representation the repo uses.

### Do not expand the spatial divergence in Lean

Avoid expanding

```text
∂x q_t
```

as a physical derivative. That expansion introduces terms like `U_x`, `V_xx`, etc. It is algebraically true but formally and analytically more expensive. The divergence identity

```text
cosineCoeff(∂x q_t)_n = ± sqrt(λ_n) sineCoeff(q_t)_n
```

is the clean route: it moves the derivative loss into a single explicit `sqrt(λ_n)` multiplier and avoids asking for pointwise spatial derivatives of `U`.

---

## 2. Coefficient-level form of the derivative

Let the coefficient sequences be:

```text
û      := cosineCoeffs(u),
Û      := cosineCoeffs(U),
v̂      := resolverCoeff μ û,
V̂      := resolverCoeff μ Û,
vx̂_sin := sqrt(λ) * v̂,
Vx̂_sin := sqrt(λ) * V̂,
D̂      := cosineCoeffs(D),
D₁̂     := cosineCoeffs(D₁).
```

Then the sine coefficients of `q_t` are obtained from mixed cosine×sine products:

```text
sineCoeffs(q_t)
  = trueMixedProd( trueCosProd(D̂, Û), vx̂_sin )
    + trueMixedProd( trueCosProd(D̂, û), Vx̂_sin )
    - β * trueMixedProd( trueCosProd(trueCosProd(D₁̂, û), V̂), vx̂_sin ).
```

This is the exact coefficient-level expression, modulo your product-normalization conventions.

So the time derivative of the chem source coefficient is

```text
∂t SchemCoeff_n
  = ± sqrt(λ_n) * [
      trueMixedProd( trueCosProd(D̂, Û), vx̂_sin )_n
    + trueMixedProd( trueCosProd(D̂, û), Vx̂_sin )_n
    - β * trueMixedProd( trueCosProd(trueCosProd(D₁̂, û), V̂), vx̂_sin )_n
    ].
```

For absolute-value/envelope statements, the sign is irrelevant.

---

## 3. Clean sufficient weighted-Wiener majorant

Fix a compact time window

```text
J = [t₀,t₁] ⊂ (0,T).
```

For the divergence-weighted package, use weight `A^3` at the pre-divergence sine level. A clean sufficient envelope package is:

```text
Eu3       ∈ A^3_cos,   |û_n(t)| ≤ Eu3_n
EU3       ∈ A^3_cos,   |Û_n(t)| ≤ EU3_n
D3        ∈ A^3_cos,   |D̂_n(t)| ≤ D3_n
D1_3      ∈ A^3_cos,   |D₁̂_n(t)| ≤ D1_3_n
Evx3      ∈ A^3_sin,   |sineCoeff(v_x(t))_n| ≤ Evx3_n
EV3       ∈ A^3_cos,   |V̂_n(t)| ≤ EV3_n
EVx3      ∈ A^3_sin,   |sineCoeff(V_x(t))_n| ≤ EVx3_n
```

uniformly for `t∈J`.

The resolver gives explicit choices from `Eu3` and `EU3`:

```text
Ev3_n   := Eu3_n  / (μ+λ_n),
Evx3_n  := sqrt(λ_n) * Eu3_n / (μ+λ_n),
EV3_n   := EU3_n  / (μ+λ_n),
EVx3_n  := sqrt(λ_n) * EU3_n / (μ+λ_n).
```

Since

```text
sqrt(λ_n)/(μ+λ_n) ≤ C(μ) / sqrt(1+λ_n),
```

`EVx3 ∈ A^3` follows from `EU3 ∈ A^2`, but for Lean simplicity it is fine to assume/prove `EU3 ∈ A^3`; then all resolver-derived envelopes are immediate by monotonicity/gain lemmas.

### The majorant for `q_t`

Define the pre-divergence time-derivative envelope:

```text
Eqdot3 :=
    trueMixedProd( trueCosProd(D3, EU3), Evx3 )
  + trueMixedProd( trueCosProd(D3, Eu3), EVx3 )
  + β * trueMixedProd( trueCosProd(trueCosProd(D1_3, Eu3), EV3), Evx3 ).
```

Here `+` means pointwise sum of nonnegative envelope sequences.

By weighted Wiener product closure,

```text
Eqdot3 ∈ A^3_sin.
```

For every `t∈J` and every `n`, the coefficient derivative obeys

```text
|∂t cosineCoeff(S_chem(t))_n|
  ≤ sqrt(λ_n) * Eqdot3_n.
```

Therefore, for any target source weight `r`,

```text
(1+λ_n)^(r/2) |∂t SchemCoeff_n(t)|
  ≤ (1+λ_n)^((r+1)/2) Eqdot3_n.
```

So if `Eqdot3 ∈ A^3_sin`, then the derivative source coefficients are summable at source weight `r=2`:

```text
Σ_n (1+λ_n)^1 |∂t SchemCoeff_n(t)| < ∞.
```

This is the natural divergence-weighted source derivative package.

### Minimal versus clean hypotheses on `U = u_t`

The clean same-scale condition is:

```text
U ∈ A^3_cos on J.
```

It is stronger than strictly necessary for some terms, but it is the most Lean-friendly because every product is an `A^3 × A^3 → A^3` product.

A possible refinement is:

```text
U ∈ A^2_cos
```

because the worst term involving `U` through `V_x` gains one derivative by the resolver. But proving mixed tame estimates with different weights is extra infrastructure. For a first Lean formalization, use the same-level `A^3` envelope for `U`.

Important: the resolver smoothing helps `V` and `V_x`; it does **not** eliminate the raw `U` in the term

```text
D * U * v_x.
```

So if your already-proved statement (A) only gives unweighted or low-weight summability of `Û`, it is not enough for the divergence-weighted derivative package. You need the appropriate positive-time weighted Wiener bound for `u_t`, or a sharper tame-product infrastructure.

---

## 4. Sufficient conditions for `HasDerivAt` and continuity

There are two layers.

### Function-level derivative

At each `(t,x)`, prove

```lean
HasDerivAt (fun t => q t x) (qdot t x) t
```

by product and chain rules:

```lean
HasDerivAt.mul
HasDerivAt.add
HasDerivAt.sub
HasDerivAt.const_mul
HasDerivAt.rpow_const
```

For the denominator:

```lean
HasDerivAt (fun t => (1 + v t x)^(-β))
  ((-β) * (1 + v t x)^(-β - 1) * V t x)
  t
```

using `1+v>0`, which follows from `v≥0`.

### Coefficient-level derivative

Use the divergence identity and the bounded linear sine-coefficient functional:

```text
SchemCoeff_n(t) = ± sqrt(λ_n) * sineCoeff(q(t))_n.
```

Then

```lean
HasDerivAt (fun t => sineCoeffs (q t) n) (sineCoeffs (qdot t) n) t
```

follows by applying the bounded linear functional `sineCoeffCLM n` to the function-level derivative, or by the same integral-swap/dominated-differentiation engine you used for the power source.

The diagonal/integral-swap issue is no different from before: once `qdot` is an integrable/dominated time derivative for the coefficient integral, the coefficient derivative follows.

### Continuity in time

For each fixed `n`, continuity of

```text
t ↦ ∂t SchemCoeff_n(t)
```

follows from continuity of the factor coefficient maps and continuity of the product coefficient formulas. If product coefficients are defined by infinite sums, use a dominated-tsum lemma with the envelope `Eqdot3` above.

A standard Lean pattern:

```lean
-- schematic local lemma
theorem continuous_tsum_of_uniform_summable_bound
    (hcont : ∀ n, ContinuousOn (fun t => f n t) J)
    (hbound : ∀ t ∈ J, ∀ n, |f n t| ≤ E n)
    (hE : Summable E) :
    ContinuousOn (fun t => ∑' n, f n t) J
```

If such a lemma is not already in the repo, it is worth adding once. It is the same dominated-convergence argument for `tsum` that the earlier `hasDerivAt_tsum` machinery likely already contains.

---

## 5. Exact Lean-style theorem shape

I would not state the theorem by expanding every product in the goal. State it in three layers.

### Layer 1: pointwise derivative of the flux

```lean
def chemPreFlux (u v vx : ℝ → ℝ) (β : ℝ) : ℝ → ℝ :=
  fun x => u x * vx x * (1 + v x)^(-β)

def chemPreFlux_tdot
    (u U v V vx Vx : ℝ → ℝ) (β : ℝ) : ℝ → ℝ :=
  fun x =>
      (1 + v x)^(-β) * U x * vx x
    + (1 + v x)^(-β) * u x * Vx x
    - β * (1 + v x)^(-β - 1) * u x * vx x * V x

theorem hasDerivAt_chemPreFlux
    (hu : ∀ x, HasDerivAt (fun t => u t x) (U x) t)
    (hv : ∀ x, HasDerivAt (fun t => v t x) (V x) t)
    (hvx : ∀ x, HasDerivAt (fun t => vx t x) (Vx x) t)
    (hv_nonneg : ∀ x, 0 ≤ v t x)
    (hβ : 0 ≤ β) :
    ∀ x, HasDerivAt
      (fun τ => chemPreFlux (u τ) (v τ) (vx τ) β x)
      (chemPreFlux_tdot (u t) U (v t) V (vx t) Vx β x)
      t
```

### Layer 2: coefficient derivative via sine functional and divergence identity

```lean
theorem hasDerivAt_chemSourceCoeff
    (hdiv : ∀ τ n,
      cosineCoeffs (fun x => deriv (chemPreFlux (u τ) (v τ) (vx τ) β) x) n
        = divSign n * Real.sqrt (lam n) * sineCoeffs (chemPreFlux (u τ) (v τ) (vx τ) β) n)
    (hpre : HasDerivAt (fun τ => chemPreFlux (u τ) (v τ) (vx τ) β) qdot t)
    (n : ℕ) :
    HasDerivAt
      (fun τ => cosineCoeffs (Schem τ) n)
      (divSign n * Real.sqrt (lam n) * sineCoeffs qdot n)
      t
```

In practice, `hpre` may be pointwise plus coefficient integral swap rather than a Banach-valued `HasDerivAt`.

### Layer 3: weighted majorant

```lean
def chemPreFluxDotEnv3
    (D3 EU3 Evx3 D1_3 Eu3 EV3 EVx3 : ℕ → ℝ) (β : ℝ) : ℕ → ℝ :=
  trueMixedProd (trueCosProd D3 EU3) Evx3
  + trueMixedProd (trueCosProd D3 Eu3) EVx3
  + |β| • trueMixedProd (trueCosProd (trueCosProd D1_3 Eu3) EV3) Evx3

theorem chemSourceCoeff_tdot_bound
    (hEnv : WeightedL1 3 (chemPreFluxDotEnv3 D3 EU3 Evx3 D1_3 Eu3 EV3 EVx3 β))
    (hdom : ∀ t ∈ J, ∀ n,
      |sineCoeffs (qdot t) n| ≤ chemPreFluxDotEnv3 ... n) :
    ∀ t ∈ J, ∀ n,
      |deriv (fun τ => cosineCoeffs (Schem τ) n) t|
        ≤ Real.sqrt (lam n) * chemPreFluxDotEnv3 ... n
```

Then the weighted summability consequence:

```lean
theorem chemSourceCoeff_tdot_weightedL1
    (hEnv3 : WeightedL1 3 Eqdot) :
    Summable (fun n => (1 + lam n) *
      |deriv (fun τ => cosineCoeffs (Schem τ) n) t|)
```

using

```text
(1+λ_n) * sqrt(λ_n) ≤ (1+λ_n)^(3/2).
```

---

## 6. Answer to the three questions

### Q1

The exact formula is:

```text
q_t
  = (1+v)^(-β) u_t v_x
    + u (1+v)^(-β) (v_t)_x
    - β u v_x v_t (1+v)^(-β-1),
```

where

```text
v_t = (μ-Δ_N)^(-1) u_t,
(v_t)_x has sine coefficients sqrt(λ_n) * (u_t)_n/(μ+λ_n).
```

Then

```text
∂t cosineCoeff(S_chem)_n
  = ± sqrt(λ_n) sineCoeff(q_t)_n.
```

This expression is linear in one of `u_t`, `v_t`, or `(v_t)_x` in each term.

### Q2

A clean sufficient majorant on a compact positive-time window is:

```text
Eqdot3 =
    trueMixedProd( trueCosProd(D3, EU3), Evx3 )
  + trueMixedProd( trueCosProd(D3, Eu3), EVx3 )
  + β * trueMixedProd( trueCosProd(trueCosProd(D1_3, Eu3), EV3), Evx3 )
```

with all factor envelopes in `A^3`, and `EV3`, `EVx3` obtained by resolver smoothing from a weighted envelope for `u_t`.

Then

```text
|∂t cosineCoeff(S_chem)_n| ≤ sqrt(λ_n) Eqdot3_n.
```

Thus

```text
Σ_n (1+λ_n) |∂t cosineCoeff(S_chem)_n| < ∞
```

follows from

```text
Eqdot3 ∈ A^3_sin.
```

This is the exact divergence-weighted derivative-source majorant.

### Q3

The formal method is the same opaque/integral-swap/product-rule method used for the power source: treat `realSlice`/the solution object opaquely, prove the pointwise time derivative by chain/product rules, and pin the goal by `change` as needed. The divergence itself should be handled by the sine/cosine divergence identity, not by expanding an extra spatial derivative.

But analytically the divergence costs one derivative: to control the chem source derivative at source weight `r`, you need the pre-divergence flux derivative `q_t` at sine weight `r+1`. For the divergence-weighted package `r=2`, this is `q_t ∈ A^3_sin`.

So: **no new whnf wall, but yes a genuine higher weighted-Wiener bound.**
