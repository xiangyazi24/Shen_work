# ChatGPT git-drop (cron1)

## Q84 — χ₀<0 positive-time `A³_cos` smoothing theorem: exact ladder and endpoint issue

### Executive verdict

The clean weighted-Wiener smoothing statement is **not** a one-pass consequence of the `L∞` order box. The Duhamel endpoint `s=t` blocks arbitrary heat smoothing of the nonlinear source. The correct proof is a bootstrap/ladder in weighted Wiener spaces.

However, the ladder does **not** start from `L∞` or `L²` by simply renaming them `A⁰`. In this notation

```text
A⁰ = { coefficients in ℓ¹ },
```

which is strictly stronger than both `L²` (`ℓ²` coefficients) and `L∞` (only flat coefficient bounds). Thus the clean theorem is:

```text
A⁰ seed on a positive-time interval + nonlinear ladder ⇒ A³ per slice.
```

The ladder gain for the chemotaxis divergence term is exactly **+1 weighted-Wiener derivative per pass**:

```text
u ∈ A^r_cos
  ⇒ flux F = W v_x ∈ A^r_sin
  ⇒ ∂xF ∈ A^{r-1}_cos
  ⇒ ∫ S(t-s)∂xF(s) ds ∈ A^{r+1}_cos.
```

The logistic/non-divergence term gains +2 and is not limiting. Therefore, once an `A⁰` seed is available, three steps give

```text
A⁰ → A¹ → A² → A³.
```

If you need small elapsed-time factors for a contraction/supersolution argument, use gains `< 1` for the divergence term. For pure regularity, the endpoint Duhamel estimate gives the full `+1` gain but without a small factor.

---

## 1. Weighted Wiener spaces and the heat/Duhamel multiplier

Let

```text
λ_k = (kπ)²,
w_r(k) = (1+λ_k)^(r/2),
‖a‖_{A^r} = Σ_k w_r(k) |a_k|.
```

The heat semigroup is diagonal:

```text
(S(t)a)_k = exp(-tλ_k) a_k.
```

For a non-divergence source `G_k(s)`, the Duhamel coefficient is

```text
D_k(t) = ∫_0^t exp(-(t-s)λ_k) G_k(s) ds.
```

If `G ∈ L∞([0,t]; A^r)`, then for `0 ≤ α ≤ 2`,

```text
D ∈ A^{r+α},
```

with the endpoint estimate

```text
w_{r+α}(k) |D_k(t)|
  ≤ C_{α,t} w_r(k) sup_s |G_k(s)|.
```

For `0 ≤ α < 2`, one has the small-time factor

```text
C_α t^{1-α/2}
```

coming from

```text
(1+λ)^{α/2} ∫_0^t exp(-ρλ) dρ ≤ C_α t^{1-α/2}.
```

For `α=2`, the estimate is still finite on a bounded time interval but has no small factor:

```text
(1+λ) ∫_0^t exp(-ρλ) dρ ≤ C_t.
```

The zero mode only contributes `t`; this is harmless for finite `t` and often vanishes for divergence sources.

---

## 2. Divergence source: why the gain is +1, not +2

For the chemotaxis term write

```text
F := W v_x,
source := ∂xF.
```

With the sine/cosine divergence identity,

```text
cosCoeff(∂xF)_k = ± sqrt(λ_k) sineCoeff(F)_k.
```

If

```text
F ∈ A^r_sin,
```

then

```text
∂xF ∈ A^{r-1}_cos,
```

because

```text
w_{r-1}(k) sqrt(λ_k) |F_k|
  ≤ w_r(k) |F_k|.
```

Now the heat Duhamel gains two derivatives from the source scale:

```text
A^{r-1}_cos --Duhamel--> A^{r+1}_cos.
```

Equivalently, directly:

```text
w_{r+1}(k) ∫_0^t exp(-(t-s)λ_k) sqrt(λ_k)|F_k(s)| ds
  ≤ C_t w_r(k) sup_s |F_k(s)|.
```

For `k≥1`, use

```text
sqrt(λ_k) sqrt(1+λ_k) ∫_0^t exp(-ρλ_k) dρ
  ≤ sqrt(λ_k) sqrt(1+λ_k) / λ_k
  = sqrt(1+λ_k)/sqrt(λ_k)
  ≤ C,
```

since `λ_k ≥ π²` for `k≥1`. For `k=0`, the divergence mode is zero.

So the chemotaxis divergence term gives a **net +1** gain from flux regularity to `u` regularity.

### Small-factor version

If you need a shrinking factor in `t`, then use any `0 ≤ α < 1`:

```text
F ∈ A^r_sin
  ⇒ ∫ S(t-s)∂xF(s) ds ∈ A^{r+α}_cos,
```

with

```text
‖Dchem(t)‖_{A^{r+α}}
  ≤ C_α t^{(1-α)/2} sup_s ‖F(s)‖_{A^r_sin}.
```

This is the estimate you quoted. The endpoint `α=1` is the full regularity gain but no small-time margin.

---

## 3. Nonlinearity at level `A^r`

Assume `r ≥ 0` and

```text
u ∈ A^r_cos.
```

Then the same weighted-Wiener product bookkeeping from Q82 gives:

### Resolver

```text
v = (μ-Δ)^(-1)u ∈ A^{r+2}_cos,
v_x ∈ A^{r+1}_sin.
```

In particular, by monotonicity of weights,

```text
v ∈ A^r_cos,
v_x ∈ A^r_sin.
```

### Denominator composition

Using `v ≥ 0` and the weighted Wiener composition/Wiener-Lévy lemma,

```text
(1+v)^(-β) ∈ A^r_cos.
```

This composition lemma is genuine analytic content. It is not a consequence of product closure unless the exponent is a polynomial case.

### Weight factor

By cosine product closure,

```text
W = u(1+v)^(-β) ∈ A^r_cos.
```

### Flux

By mixed cosine×sine product closure,

```text
F = W v_x ∈ A^r_sin.
```

Therefore the chemotaxis source satisfies

```text
∂xF ∈ A^{r-1}_cos,
```

and the Duhamel contribution lies in

```text
A^{r+1}_cos.
```

### Logistic source

For a smooth/logistic Nemytskii term `L(u)`, the same composition/product algebra gives

```text
L(u) ∈ A^r_cos.
```

Its non-divergence Duhamel leg gains two derivatives:

```text
∫ S(t-s)L(u(s)) ds ∈ A^{r+2}_cos.
```

So the logistic leg is never worse than the chemotaxis divergence leg.

---

## 4. The finite ladder

Once an `A⁰` seed is available on the relevant time interval, the ladder is:

### Step 0: seed

```text
u ∈ A⁰_cos.
```

Then:

```text
v ∈ A²,
v_x ∈ A¹,
(1+v)^(-β) ∈ A⁰,
W ∈ A⁰,
F=Wv_x ∈ A⁰_sin,
∂xF ∈ A^{-1}_cos,
Duhamel_chem ∈ A¹_cos,
Duhamel_log ∈ A²_cos,
heat leg ∈ A^∞ for t>0.
```

Conclusion:

```text
u ∈ A¹_cos.
```

### Step 1

```text
u ∈ A¹_cos
  ⇒ F ∈ A¹_sin
  ⇒ ∂xF ∈ A⁰_cos
  ⇒ chem Duhamel ∈ A²_cos
  ⇒ u ∈ A²_cos.
```

### Step 2

```text
u ∈ A²_cos
  ⇒ F ∈ A²_sin
  ⇒ ∂xF ∈ A¹_cos
  ⇒ chem Duhamel ∈ A³_cos
  ⇒ u ∈ A³_cos.
```

Thus:

```text
A⁰ → A¹ → A² → A³.
```

This is the clean three-step ladder.

If you want strict small-time factors at every step, use

```text
A^r → A^{r+α}
```

for any fixed `α<1`, and take `N > 3/α` steps. This is more cumbersome but useful for invariant-ball proofs. For pure positive-time regularity, the exact `+1` ladder is cleaner.

---

## 5. The base `A⁰` seed is the real issue

The statement

```text
u ∈ A⁰ = L²/L∞
```

is false. `A⁰` means

```text
Σ_k |cosCoeff(u)_k| < ∞.
```

Neither `L²` nor `L∞` implies this.

From `u₀ ∈ L∞`, the heat leg

```text
e^{-tλ_k} u₀,k
```

is in every `A^r` for `t>0`. But the Duhamel term has the endpoint `s=t`, where there is no heat smoothing. Therefore the full nonlinear `A⁰` seed is not obtained by simply saying “the heat semigroup smooths.”

### What bounded sources alone give

Suppose only that the pre-divergence flux coefficients are flatly bounded:

```text
|sineCoeff(F(s))_k| ≤ C.
```

Then the divergence Duhamel coefficient is bounded by

```text
∫_0^t exp(-(t-s)λ_k) sqrt(λ_k) C ds
  ≤ C / sqrt(λ_k)
```

for high modes. Therefore the `A^r` summand behaves like

```text
(1+λ_k)^{r/2} / sqrt(λ_k) ~ k^{r-1}.
```

The series

```text
Σ_k k^{r-1}
```

converges only for

```text
r < 0.
```

So a bounded divergence source gives `A^r` only for negative `r`, not `A⁰`. This is exactly the endpoint obstruction.

Since the weighted-Wiener product algebra above is clean for `r ≥ 0`, this negative regularity seed is not enough by itself to start the `A`-algebra ladder.

### How to get the seed

There are three honest options.

#### Option A: use an already-proved `H^σ`, `σ>1/2`, positive-time seed

If you already have per-slice or trajectory

```text
u(t) ∈ H^σ,  σ > 1/2,
```

then Cauchy-Schwarz gives

```text
u(t) ∈ A⁰.
```

Indeed,

```text
Σ |u_k| ≤ (Σ (1+λ_k)^σ u_k²)^{1/2}
          (Σ (1+λ_k)^(-σ))^{1/2},
```

and the second sum converges exactly when `σ > 1/2`.

This is the best bridge if your repo already has a positive-time `MemHSigma σ` result with `σ>1/2`.

#### Option B: prove a separate parabolic seed theorem

Name a theorem such as:

```lean
theorem mildSolution_cosA0_posTime
    (ht : 0 < t) :
    WeightedL1 0 (cosineCoeffs (u t))
```

This is a genuine positive-time smoothing theorem. It cannot be reduced to the heat leg alone.

A standard analytic proof would use parabolic regularity in a scale weaker than `A⁰` first, then bootstrap to `H^σ>1/2`, then embed to `A⁰`, or use time-weighted fixed-point spaces on `(0,t]`.

#### Option C: assume `u₀ ∈ A⁰` and run an `A⁰` local theory

If the initial data already has `A⁰`, then the Duhamel map preserves/improves `A⁰`, and the ladder can start immediately. But this is an extra data regularity assumption.

---

## 6. Answer to question 1: what σ can the Duhamel estimate reach?

For a non-divergence source `G ∈ A^r`, heat Duhamel reaches

```text
A^{r+α} for every α ≤ 2,
```

with a small factor only for `α<2`.

For a divergence source `G = ∂xF` with `F ∈ A^r_sin`, heat Duhamel reaches

```text
A^{r+α} for every α ≤ 1,
```

with a small factor only for `α<1`.

The endpoint `α=1` is exactly the full divergence-limited smoothing gain but has no small-time power.

Therefore the nonlinear chemotaxis bootstrap is:

```text
u ∈ A^r  ⇒  F(u) ∈ A^r_sin  ⇒  chemDuhamel ∈ A^{r+1}_cos.
```

This is not circular as a ladder step: assuming `u ∈ A^r` on a time interval, the product/resolver machinery bounds the source in `A^r`, and the Duhamel operator improves the output to `A^{r+1}`.

It is circular only if you try to prove the initial `A^r` assumption at the same level without a seed or continuation argument.

---

## 7. Answer to question 2: single theorem or ladder?

For Lean, do **not** start with a monolithic theorem

```lean
mildSolution_cosA3_posTime_from_Linf
```

unless all lower-level smoothing infrastructure is already available. It will hide the exact obstruction.

Instead formalize modularly:

```lean
theorem chemDuhamel_gain_one_A
    (hr : 0 ≤ r)
    (hF : ∀ s ∈ Icc t0 t1, SinA r (F s)) :
    CosA (r+1) (fun k => ∫ ... sqrt(lam k) * sineCoeff(F s) k ...)
```

```lean
theorem logisticDuhamel_gain_two_A
    (hr : 0 ≤ r)
    (hG : ∀ s ∈ Icc t0 t1, CosA r (G s)) :
    CosA (r+2) (fun k => ∫ ... cosineCoeff(G s) k ...)
```

```lean
theorem nonlinearity_flux_A
    (hr : 0 ≤ r)
    (hu : CosA r u) :
    SinA r (fun x => W x * vx x)
```

Then combine them into:

```lean
theorem mild_A_step
    (hr : 0 ≤ r)
    (huA : trajectory/slice u in A^r on the interval)
    (hheat : heat leg smooth) :
    u(t) ∈ A^{r+1}_cos
```

Finally iterate:

```lean
theorem mild_A3_of_A0_seed
    (hA0 : positive-time A0 seed) :
    u(t) ∈ A^3_cos
```

This is much less work and much less brittle than a one-pass proof.

A direct one-pass proof from the `L∞` box to `A³` is not available: the divergence endpoint estimate from bounded flux gives only `A^r` for `r<0`.

---

## 8. Answer to question 3: product machinery at each ladder step

Yes. Each step uses the same resolver/flux weighted-Wiener machinery at the current level `r`:

```text
u ∈ A^r
  ⇒ v ∈ A^{r+2}
  ⇒ v_x ∈ A^{r+1} ⊂ A^r
  ⇒ (1+v)^(-β) ∈ A^r
  ⇒ W = u(1+v)^(-β) ∈ A^r
  ⇒ F = W v_x ∈ A^r_sin.
```

Then Duhamel gives the next level:

```text
F ∈ A^r_sin ⇒ Dchem ∈ A^{r+1}_cos.
```

So the product bookkeeping is exactly the Q82 machinery, parameterized by `r`, and applied repeatedly at `r=0,1,2`.

The one extra analytic lemma is the composition theorem

```text
v ∈ A^r, v≥0 ⇒ (1+v)^(-β) ∈ A^r.
```

This is needed at every level. If you only prove it at `r=0,1,2`, that is enough for the three-step ladder.

---

## 9. Suggested Lean theorem names

### Weighted Wiener predicate

```lean
def WeightedL1 (r : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable (fun k => (1 + lam k) ^ (r / 2) * |a k|)
```

### Heat leg

```lean
theorem heat_cosA_all_posTime_of_linf_coeff_bound
    (ht : 0 < t)
    (hcoeff : ∀ k, |u0hat k| ≤ M0)
    (r : ℝ) :
    WeightedL1 r (fun k => Real.exp (-(t * lam k)) * u0hat k)
```

### Duhamel gain, non-divergence

```lean
theorem heatDuhamel_cosA_gain_two
    (hr : 0 ≤ r)
    (hG : ∀ s ∈ Icc 0 t, WeightedL1 r (G s))
    (hG_unif : ∃ Genv, WeightedL1 r Genv ∧ ∀ s ∈ Icc 0 t, ∀ k, |G s k| ≤ Genv k) :
    WeightedL1 (r+2)
      (fun k => ∫ s in 0..t, Real.exp (-((t-s) * lam k)) * G s k)
```

For endpoint `+2`, allow constants depending on `t` and handle mode zero.

### Duhamel gain, divergence

```lean
theorem heatDuhamel_div_sinA_gain_one
    (hr : 0 ≤ r)
    (hFenv : WeightedL1 r Fenv)
    (hFbd : ∀ s ∈ Icc 0 t, ∀ k, |Fsin s k| ≤ Fenv k) :
    WeightedL1 (r+1)
      (fun k => ∫ s in 0..t,
        Real.exp (-((t-s) * lam k)) * Real.sqrt (lam k) * Fsin s k)
```

The proof is the pointwise multiplier bound

```text
(1+λ)^{1/2} sqrt(λ) ∫_0^t exp(-ρλ)dρ ≤ C_t
```

combined with the `A^r` envelope.

### Nonlinearity at level `r`

```lean
theorem chemFlux_sinA_of_u_cosA
    (hr : 0 ≤ r)
    (hu : WeightedL1 r (cosineCoeffs u)) :
    WeightedL1 r (sineCoeffs (fun x => W x * vx x))
```

with assumptions/fields for resolver definition, denominator composition, and product bridges.

### Ladder theorem

```lean
theorem mild_posTime_A3_of_A0_seed
    (hA0 : trajectory/slice A0 seed on the needed interval)
    (hstep : ∀ r ∈ {0,1,2}, A^r step theorem) :
    WeightedL1 3 (cosineCoeffs (u t))
```

If you want a uniform-on-strip version:

```lean
theorem mild_posTime_A3_uniform_on_Icc
    (hε : 0 < ε) (hεT : ε ≤ T)
    (hA0strip : ∃ E0, WeightedL1 0 E0 ∧
      ∀ s ∈ Icc ε T, ∀ k, |cosineCoeffs (u s) k| ≤ E0 k) :
    ∃ E3, WeightedL1 3 E3 ∧
      ∀ s ∈ Icc ε T, ∀ k, |cosineCoeffs (u s) k| ≤ E3 k
```

This uniform-envelope form is usually more useful than per-slice membership.

---

## 10. Final answer

The positive-time `A³` theorem should be named and proved as a **two-stage theorem**:

1. **Seed theorem:** obtain `A⁰` on a positive-time slice/strip. This does not follow from `L∞` by a one-line heat estimate because of the Duhamel endpoint. It must come from an existing `H^σ`, `σ>1/2`, smoothing theorem, a separate parabolic seed theorem, or an `A⁰` local theory.

2. **Weighted-Wiener ladder:** once `A⁰` is available, iterate the divergence-limited gain

```text
A^r → A^{r+1}
```

three times. The logistic leg gains two derivatives, and the chemotaxis divergence leg gains one. The product/resolver/denominator machinery is used at every step at the current level `r`.

So the concrete ladder is:

```text
A⁰ seed
  → flux in A⁰_sin → chem Duhamel in A¹_cos → u in A¹
  → flux in A¹_sin → chem Duhamel in A²_cos → u in A²
  → flux in A²_sin → chem Duhamel in A³_cos → u in A³.
```

This is the Lean-ready structure. A direct one-pass proof from the `L∞` order box to `A³` is not sound; the endpoint source is not smoothed enough. A monolithic `u(t) ∈ A³` theorem is fine as a final wrapper, but the formal proof should expose the `A⁰` seed and the three +1 ladder steps.
