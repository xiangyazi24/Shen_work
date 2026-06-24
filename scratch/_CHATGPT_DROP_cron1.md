# ChatGPT git-drop (cron1)

## Q115 — χ₀<0 chemotaxis: closing `q_t ∈ A³_sin`

### Executive verdict

For the current weighted-Wiener algebra route, the clean sufficient hypothesis is:

```text
u ∈ A³_cos   and   u_t ∈ A³_cos
```

on the positive-time window under consideration. Then

```text
q_t ∈ A³_sin,
q := u v_x (1+v)^(-β),
v = (μ-Δ_N)^(-1)u.
```

This is stronger than some ad hoc cancellations might suggest, but it is the correct Lean-friendly same-scale product budget. The reason is important: in the Fourier/Wiener algebra, an `A⁰` factor is **not** a free multiplier of `A³`. To prove a product lies in `A³` using the standard convolution algebra, each nontrivial factor in the product should be controlled in `A³` unless you have a separate multiplier/tame theorem strong enough to justify lowering one factor. The safe route is same-scale closure:

```text
A³ × A³ → A³,
A³_cos × A³_sin → A³_sin.
```

So yes: `u ∈ A³` plus `u_t ∈ A³` suffices, and it is the minimal clean standing regularity package I would formalize first. If you only have `u,u_t` up to about `A²`, that does not close `q_t ∈ A³_sin` by the standard product algebra.

The `A³` bootstrap for `u_t` is a genuine additional positive-time smoothing theorem. It should be available by differentiating the mild equation and running the same divergence-limited `+1` weighted-Wiener ladder for the linearized equation, but it is not automatic from the already-proved `u ∈ A³` theorem unless you separately prove time-regularity/smoothing for `u_t`.

---

## 1. Notation

Let

```text
A^s_cos(f) := Σ_k (1+λ_k)^(s/2) |cosineCoeff(f)_k| < ∞,
A^s_sin(f) := Σ_k (1+λ_k)^(s/2) |sineCoeff(f)_k| < ∞.
```

Write

```text
U  := u_t,
D  := (1+v)^(-β),
D₁ := (1+v)^(-β-1),
V  := v_t = (μ-Δ_N)^(-1)U,
V_x := ∂x V.
```

Then

```text
q = u v_x D
```

and

```text
q_t
  = U v_x D
    + u V_x D
    - β u v_x V D₁.
```

This is the expression whose sine coefficients must be in `A³_sin`.

---

## 2. Resolver bookkeeping

The resolver multiplier is

```text
v̂_k = û_k / (μ+λ_k).
```

For any `s ≥ 0`,

```text
u ∈ A^s_cos      ⇒ v ∈ A^{s+2}_cos,
u ∈ A^s_cos      ⇒ v_x ∈ A^{s+1}_sin.
```

Constants are controlled by

```text
C_R(μ) := max 1 (1/μ),
```

because

```text
(1+λ)/(μ+λ) ≤ C_R(μ)
```

and

```text
sqrt(λ) sqrt(1+λ)/(μ+λ) ≤ (1+λ)/(μ+λ) ≤ C_R(μ).
```

Therefore:

```text
u ∈ A³_cos ⇒ v ∈ A⁵_cos ⊂ A³_cos,
u ∈ A³_cos ⇒ v_x ∈ A⁴_sin ⊂ A³_sin.
```

For the time derivative:

```text
U ∈ A³_cos ⇒ V ∈ A⁵_cos ⊂ A³_cos,
U ∈ A³_cos ⇒ V_x ∈ A⁴_sin ⊂ A³_sin.
```

So the same `A³` input on `u_t` gives all resolver-time-derivative factors at the needed level.

Lean targets:

```lean
theorem weightedL1_resolver_gain_two
    (hμ : 0 < μ) (ha : WeightedL1 s a) :
    WeightedL1 (s+2) (fun k => a k / (μ + lam k))

theorem weightedL1_resolver_deriv_gain_one
    (hμ : 0 < μ) (ha : WeightedL1 s a) :
    WeightedL1 (s+1)
      (fun k => Real.sqrt (lam k) * (a k / (μ + lam k)))
```

---

## 3. Denominator bookkeeping

Since `v ≥ 0`, the functions

```text
z ↦ (1+z)^(-β),
z ↦ (1+z)^(-β-1)
```

are smooth on a neighborhood of the range of `v`. A weighted-Wiener composition/Wiener-Lévy lemma gives:

```text
v ∈ A³_cos ⇒ D  ∈ A³_cos,
v ∈ A³_cos ⇒ D₁ ∈ A³_cos.
```

Thus from `u ∈ A³_cos`, because `v ∈ A⁵ ⊂ A³`, we get:

```text
D, D₁ ∈ A³_cos.
```

Lean target:

```lean
theorem weightedL1_one_add_rpow_neg
    (hβ : 0 ≤ β)
    (hv_nonneg : ∀ x, 0 ≤ v x)
    (hvA : WeightedL1 3 (cosineCoeffs v)) :
    WeightedL1 3
      (cosineCoeffs (fun x => (1 + v x)^(-β)))
```

and the same theorem with exponent `-β-1`.

This composition theorem is genuine analytic content. Once it exists, the rest is product bookkeeping.

---

## 4. Product budget for each term in `q_t`

Use same-scale weighted-Wiener closure:

```text
A³_cos × A³_cos → A³_cos,
A³_cos × A³_sin → A³_sin.
```

### Term 1: `U v_x D`

Types:

```text
U   ∈ A³_cos,
v_x ∈ A³_sin,
D   ∈ A³_cos.
```

Then:

```text
U * D       ∈ A³_cos,
(U * D)*v_x ∈ A³_sin.
```

So

```text
U v_x D ∈ A³_sin.
```

This term is the main reason a same-scale proof asks for `u_t ∈ A³`: the raw factor `U` is not smoothed by the resolver.

### Term 2: `u V_x D`

Types:

```text
u   ∈ A³_cos,
V_x ∈ A³_sin,
D   ∈ A³_cos.
```

Then:

```text
u * D       ∈ A³_cos,
(u * D)*V_x ∈ A³_sin.
```

So

```text
u V_x D ∈ A³_sin.
```

Here `V_x ∈ A³_sin` follows already from `U ∈ A²_cos`, but the clean hypothesis `U∈A³` covers it.

### Term 3: `β u v_x V D₁`

Types:

```text
u   ∈ A³_cos,
v_x ∈ A³_sin,
V   ∈ A³_cos,
D₁  ∈ A³_cos.
```

Then:

```text
u * V * D₁ ∈ A³_cos,
(u * V * D₁) * v_x ∈ A³_sin.
```

So

```text
β u v_x V D₁ ∈ A³_sin.
```

Therefore:

```text
q_t ∈ A³_sin.
```

---

## 5. Why `A²` is not enough for the same-scale algebra route

If you only know

```text
u ∈ A²,
U ∈ A²,
```

then the resolver gives

```text
v_x ∈ A³_sin,
V_x ∈ A³_sin,
v,D,D₁ ∈ A³-ish from the resolver/composition side,
```

but the raw factors

```text
u, U
```

are only in `A²`. The products

```text
U v_x D,
u V_x D
```

are not automatically in `A³` under the standard algebra theorem. Products do not gain derivatives. The high regularity of one factor is not enough unless you have a specific multiplier theorem saying an `A²` factor acts boundedly on `A³`, which is false in this scale without extra regularity.

A useful warning:

```text
A⁰ is an algebra, but an arbitrary A⁰ function is not a multiplier of A³.
```

For Fourier/Wiener weighted algebras, the safe product theorem is same-scale:

```text
A³ × A³ → A³.
```

There are tame estimates of the schematic form

```text
‖fg‖_{A³} ≤ C(‖f‖_{A³}‖g‖_{A⁰} + ‖f‖_{A⁰}‖g‖_{A³}),
```

but to use this as a finite bound, both terms on the right must be finite. Thus you still need the factor carrying the derivative in each term to be controlled at `A³`, and in a multi-product proof the clean way is to assume every factor is in `A³`.

So `u∈A³` and `U∈A³` is not just harmless overkill; it is the simplest robust API.

---

## 6. Does `u_t` have its own `A³` bootstrap?

Yes, in the standard positive-time parabolic picture. But it is a real theorem and should be named separately.

Let

```text
U := u_t.
```

Differentiate the PDE/mild equation in time. Formally,

```text
U_t = U_xx + a ∂x(q_t) + (1 - 2u)U,
```

where

```text
q_t = D U v_x + D u V_x - β D₁ u v_x V,
V = R_μ U.
```

This is a linearized chemotaxis equation in `U`, with coefficients depending on the already-known solution `u`.

At weighted-Wiener level `r`, if

```text
u ∈ A^r_cos,
U ∈ A^r_cos,
```

then the same bookkeeping gives

```text
q_t ∈ A^r_sin.
```

The divergence Duhamel term for `U` then gains one derivative:

```text
q_t ∈ A^r_sin
  ⇒ ∫ S(t-s) ∂x q_t(s) ds ∈ A^{r+1}_cos.
```

The reaction derivative term

```text
(1-2u)U
```

is non-divergence and gains two derivatives through heat Duhamel, so it is not limiting.

Thus the same ladder applies to `U`:

```text
U ∈ A⁰ → A¹ → A² → A³.
```

But it needs a seed, usually on a positive-time window:

```text
U ∈ A⁰_cos on [ε,T]
```

or some equivalent coefficient summability. Your already-proved per-mode derivative theorem (A) may provide this seed if it includes an `A⁰`/weighted-ℓ¹ envelope for the coefficient derivative sequence on compact positive-time windows.

### Recommended formal structure

Do not hide this inside the `q_t` theorem. Add a named theorem:

```lean
theorem positiveTime_u_t_cosA3
    (hε : 0 < ε) (hεT : ε ≤ T)
    (hU_seed : ∃ E0, WeightedL1 0 E0 ∧
      ∀ t ∈ Set.Icc ε T, ∀ k, |cosineCoeff (u_t t) k| ≤ E0 k)
    (hu_ladder : positive-time A^r bounds for u at r=0,1,2,3) :
    ∃ E3, WeightedL1 3 E3 ∧
      ∀ t ∈ Set.Icc ε T, ∀ k, |cosineCoeff (u_t t) k| ≤ E3 k
```

Then the chem-source time-C¹ theorem consumes `positiveTime_u_cosA3` and `positiveTime_u_t_cosA3`.

### Simultaneous ladder option

A more elegant analytic proof runs a coupled ladder for `(u,U)`:

```text
(u,U) ∈ A^r × A^r  ⇒  (u,U) ∈ A^{r+1} × A^{r+1}.
```

For Lean, however, separate the proof:

1. prove `u ∈ A³` on positive-time windows;
2. prove `U ∈ A³` using the linearized equation and the already-known `u ∈ A³` coefficients;
3. prove `q_t ∈ A³_sin`.

This is less entangled.

---

## 7. Minimal Lean-formalizable hypotheses for `q_t ∈ A³_sin`

Here is the precise standing package I would use.

### Weighted envelopes on a compact positive-time window `J`

Let `J = Set.Icc ε T` with `0 < ε`.

Assume there exist nonnegative coefficient envelopes:

```lean
Eu3 : ℕ → ℝ   -- envelope for cosineCoeffs(u t)
EU3 : ℕ → ℝ   -- envelope for cosineCoeffs(u_t t)
```

with

```lean
hEu3  : WeightedL1 3 Eu3
hEU3  : WeightedL1 3 EU3
hEu3_dom : ∀ t ∈ J, ∀ k,
  |cosineCoeffs (u t) k| ≤ Eu3 k
hEU3_dom : ∀ t ∈ J, ∀ k,
  |cosineCoeffs (U t) k| ≤ EU3 k
```

where `U t = u_t t` or whatever coefficient derivative realization you use.

### Resolver-derived envelopes

Define:

```lean
Ev3 k   := Eu3 k / (μ + lam k)
Evx3 k  := Real.sqrt (lam k) * Eu3 k / (μ + lam k)
EV3 k   := EU3 k / (μ + lam k)
EVx3 k  := Real.sqrt (lam k) * EU3 k / (μ + lam k)
```

Then prove from the resolver gain lemmas:

```lean
hEv3   : WeightedL1 3 Ev3
hEvx3  : WeightedL1 3 Evx3
hEV3   : WeightedL1 3 EV3
hEVx3  : WeightedL1 3 EVx3
```

and the corresponding domination statements for `v`, `v_x`, `V`, `V_x`.

### Denominator envelopes

Assume or derive by composition:

```lean
D3 D1_3 : ℕ → ℝ
hD3    : WeightedL1 3 D3
hD1_3  : WeightedL1 3 D1_3
hD3_dom : ∀ t ∈ J, ∀ k,
  |cosineCoeffs (fun x => (1 + v t x)^(-β)) k| ≤ D3 k
hD1_3_dom : ∀ t ∈ J, ∀ k,
  |cosineCoeffs (fun x => (1 + v t x)^(-β-1)) k| ≤ D1_3 k
```

These can be discharged from `Eu3`, resolver positivity, and a weighted-Wiener composition lemma.

### Product bridge assumptions

You need the coefficient bridge lemmas for products:

```lean
CosineMulBridge
MixedMulBridge
```

for the relevant products, or the already-landed exact coefficient identities:

```text
cosineCoeffs(f*g) = trueCosProd(cosineCoeffs f)(cosineCoeffs g)
sineCoeffs(f*sineFactor) = trueMixedProd(cosineCoeffs f)(sineCoeffs sineFactor)
```

### Envelope for `q_t`

Define:

```lean
def Eqdot3 : ℕ → ℝ :=
    trueMixedProd (trueCosProd EU3 D3) Evx3
  + trueMixedProd (trueCosProd Eu3 D3) EVx3
  + |β| • trueMixedProd (trueCosProd (trueCosProd Eu3 D1_3) EV3) Evx3
```

Then the theorem is:

```lean
theorem chemPreFlux_tdot_sinA3
    (hEu3 : WeightedL1 3 Eu3)
    (hEU3 : WeightedL1 3 EU3)
    (hD3 : WeightedL1 3 D3)
    (hD1_3 : WeightedL1 3 D1_3)
    (hEvx3 : WeightedL1 3 Evx3)
    (hEVx3 : WeightedL1 3 EVx3)
    (hEV3 : WeightedL1 3 EV3)
    (domination hypotheses)
    (product bridge hypotheses) :
    WeightedL1 3 Eqdot3 ∧
    ∀ t ∈ J, ∀ k,
      |sineCoeffs (q_t t) k| ≤ Eqdot3 k
```

This is the exact majorant package.

Then divergence gives:

```lean
theorem chemSource_tdot_weighted
    (hqdot : WeightedL1 3 Eqdot3)
    (hdiv : ∀ t ∈ J, ∀ k,
      |cosineCoeffs (∂x(q_t t)) k|
        = Real.sqrt (lam k) * |sineCoeffs (q_t t) k|) :
    ∃ Esource, WeightedL1 2 Esource ∧
      ∀ t ∈ J, ∀ k,
        |deriv (fun τ => cosineCoeffs (Schem τ) k) t| ≤ Esource k
```

where a natural choice is

```lean
Esource k := Real.sqrt (lam k) * Eqdot3 k.
```

because

```text
WeightedL1 3 Eqdot3 ⇒ WeightedL1 2 (sqrt(λ) Eqdot3).
```

Indeed:

```text
(1+λ)^(2/2) sqrt(λ) ≤ (1+λ)^(3/2).
```

This is the exact source derivative envelope needed for the divergence-weighted time-C¹ package.

---

## 8. Answers to the three questions

### Q1

For a same-scale weighted-Wiener proof of

```text
q_t ∈ A³_sin,
```

the clean budget is:

```text
u   ∈ A³_cos,
U=u_t ∈ A³_cos,
v   ∈ A³_cos      -- follows from u∈A³ by resolver +2 and monotonicity
v_x ∈ A³_sin      -- follows from u∈A³ by resolver +1 and monotonicity
V=v_t ∈ A³_cos    -- follows from U∈A³
V_x ∈ A³_sin      -- follows from U∈A³
D,D₁ ∈ A³_cos     -- follows from v∈A³ plus composition
```

Then each term in

```text
q_t = U v_x D + u V_x D - β u v_x V D₁
```

is in `A³_sin` by cosine/mixed product closure.

So yes:

```text
u ∈ A³ and u_t ∈ A³
```

suffices. With the current standard product API, this is also the clean minimal hypothesis. `u,u_t` only up to `A²` does not close `A³` for `q_t`.

### Q2

The `A³` bootstrap for `u_t` should be available, but it is a separate theorem. Differentiate the PDE/mild equation to get a linearized parabolic equation for `U=u_t`:

```text
U_t = U_xx + a ∂x(q_t) + (1-2u)U.
```

At level `A^r`, if `u∈A^r` and `U∈A^r`, then the same product/resolver bookkeeping gives

```text
q_t ∈ A^r_sin.
```

The divergence Duhamel term then gains one derivative, and the reaction derivative gains two. Hence the same ladder applies:

```text
U ∈ A⁰ → A¹ → A² → A³.
```

This needs a positive-time `A⁰` seed for `U`, supplied by your already-proved coefficient derivative summability if it is a weighted-ℓ¹/window-uniform statement. If it is only per-mode differentiability without an `A⁰` envelope, then it does not seed the ladder.

### Q3

The minimal Lean-formalizable standing input to close `q_t∈A³_sin` is the window-uniform pair of weighted envelopes:

```lean
Eu3 : ℕ → ℝ,   WeightedL1 3 Eu3,
EU3 : ℕ → ℝ,   WeightedL1 3 EU3,

∀ t∈J, ∀ k, |cosineCoeffs (u t) k| ≤ Eu3 k,
∀ t∈J, ∀ k, |cosineCoeffs (u_t t) k| ≤ EU3 k.
```

Together with resolver identities, denominator composition at `A³`, and the cosine/mixed product bridges, this gives the explicit envelope `Eqdot3` above and hence

```text
q_t ∈ A³_sin
```

uniformly on `J`.

This is the precise, satisfiable standing regularity input. You can either discharge it by two positive-time ladders (`u` and `u_t`) or carry exactly these two `A³` trajectory-envelope hypotheses.

---

## Final recommendation

For fastest Lean progress, state and prove the chem-source time-C¹ theorem under the two envelope hypotheses:

```text
u    has a window-uniform A³_cos envelope,
u_t  has a window-uniform A³_cos envelope.
```

Then separately prove/discharge those envelopes by positive-time smoothing. This isolates the hard parabolic regularity from the purely algebraic chem-source derivative calculation.
