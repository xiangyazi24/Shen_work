# ChatGPT git-drop (cron1)

## Q121 — Lean strategy for the positive-time weighted-Wiener `A³` bootstrap

### Executive verdict

The clean formalization should expose the divergence Duhamel smoothing as a standalone lemma:

```text
SinA^r source envelope for S
  ⇒ CosA^{r+1} envelope for ∫ heat(t-s) ∂x S(s) ds.
```

The exact per-mode bound is, for `k ≥ 1`,

```text
sqrt(λ_k) ∫_a^t exp(-(t-s)λ_k) ds
  = (1 - exp(-(t-a)λ_k)) / sqrt(λ_k)
  ≤ 1 / sqrt(λ_k),
```

and hence

```text
(1+λ_k)^((r+1)/2)
  * sqrt(λ_k) ∫_a^t exp(-(t-s)λ_k) |S_k(s)| ds
≤ Cdiv * (1+λ_k)^(r/2) * Esrc_k,
```

where

```text
Cdiv := sup_{k≥1} sqrt(1+λ_k)/sqrt(λ_k)
      = sqrt(1 + 1/π²)
      = sqrt(1+π²)/π.
```

For `k=0`, the divergence coefficient is zero because `sqrt(λ_0)=0`, so the bound is trivial. This constant is uniform in `t`, `a`, and the window length. No positive-time lower bound is needed for the divergence Duhamel gain itself.

The prior “window-uniform flux envelope” gap is not avoided by merely saying “per-slice `A³`.” For a Duhamel estimate, a fixed target time `t` still integrates over a time interval, so one needs either a local window-uniform source envelope on the integration interval or an integrable-in-time envelope. What can be localized is the window: for an interior time `t₀>0`, work on a small compact positive-time window `[τ₀,T₀]` with `0<τ₀<t₀<T₀`, instead of a global `[0,T]` window. Per-slice membership is enough for algebraic `q_t(t₀)∈A³`; it is not enough for `DuhamelSourceTimeC1`, which asks for continuity/window-uniform derivative control.

The minimal Lean decomposition is:

1. weighted-Wiener infrastructure and the divergence Duhamel gain lemma;
2. weighted Wiener product/resolver/composition lemmas;
3. source-at-level-`r` lemma: `u ∈ A^r ⇒ flux ∈ SinA^r` (and linearized analogue for `u_t`);
4. ladder step: `TrajA r ⇒ TrajA (r+1)`;
5. seed: positive-time `A⁰` envelope;
6. three-step wrapper: `A⁰ → A¹ → A² → A³` for `u`, and similarly for `u_t`.

---

## 1. Definitions to use

Use a coefficient predicate first, independent of cosine/sine packaging:

```lean
def WeightedL1 (r : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable (fun k => (1 + lam k) ^ (r / 2) * |a k|)
```

Then define trajectory/window envelopes:

```lean
def TrajA (r : ℝ) (J : Set ℝ) (coeff : ℝ → ℕ → ℝ) : Prop :=
  ∃ E : ℕ → ℝ,
    WeightedL1 r E ∧
    (∀ k, 0 ≤ E k) ∧
    ∀ t ∈ J, ∀ k, |coeff t k| ≤ E k
```

For cosine/sine, specialize:

```lean
TrajA r J (fun t k => cosineCoeffs (u t) k)
TrajA r J (fun t k => sineCoeffs (F t) k)
```

The explicit nonnegativity field is useful for mode-zero and envelope monotonicity proofs.

---

## 2. The core per-mode divergence smoothing bound

Let the divergence Duhamel coefficient be

```text
D_k(t) := ∫_a^t exp(-(t-s)λ_k) * sqrt(λ_k) * S_k(s) ds.
```

Assume a source envelope on the integration window:

```text
∀ s∈[a,t], |S_k(s)| ≤ Esrc_k.
```

Then:

### Mode `k = 0`

Since

```text
λ_0 = 0,
sqrt(λ_0)=0,
```

we have

```text
D_0(t) = 0.
```

Thus every weighted estimate is trivial at mode zero.

### Modes `k ≥ 1`

For `λ_k>0`,

```text
|D_k(t)|
  ≤ Esrc_k * sqrt(λ_k) ∫_a^t exp(-(t-s)λ_k) ds
  = Esrc_k * (1 - exp(-(t-a)λ_k)) / sqrt(λ_k)
  ≤ Esrc_k / sqrt(λ_k).
```

Multiplying by the target weight gives

```text
(1+λ_k)^((r+1)/2) |D_k(t)|
  ≤ sqrt(1+λ_k)/sqrt(λ_k) * (1+λ_k)^(r/2) Esrc_k
  ≤ Cdiv * (1+λ_k)^(r/2) Esrc_k,
```

where

```text
Cdiv = sqrt(1 + 1/π²)
```

because `λ_k ≥ π²` for `k≥1`.

### Lean lemma shape

```lean
theorem divDuhamel_mode_weighted_bound
    {r a t : ℝ} {Senv : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ Senv k)
    {S : ℝ → ℕ → ℝ}
    (hdom : ∀ s ∈ Set.Icc a t, ∀ k, |S s k| ≤ Senv k)
    (k : ℕ) :
    (1 + lam k) ^ ((r + 1) / 2) *
      |∫ s in a..t,
          Real.exp (-((t - s) * lam k)) * Real.sqrt (lam k) * S s k|
      ≤ Cdiv * ((1 + lam k) ^ (r / 2) * Senv k)
```

For `a≤t`. If the interval orientation is not fixed, state it with `Set.Icc a t` and `intervalIntegral.integral_of_le` or work with a restricted measure to avoid signed interval issues.

The proof splits on `k=0` and `k≠0`; for `k≠0`, use:

```lean
lam k ≥ Real.pi^2
Real.sqrt (lam k) > 0
intervalIntegral.integral_mono_on
intervalIntegral.integral_const_mul
∫_a^t exp(-(t-s)*λ) ds = (1 - exp(-(t-a)*λ)) / λ
Real.exp_pos
Real.exp_nonneg
```

If proving the closed-form exponential integral is annoying, use the simpler bound

```text
∫_a^t exp(-(t-s)λ) ds ≤ ∫_0^∞ exp(-ρλ)dρ = 1/λ.
```

In Lean that may still need a lemma. If no improper-integral lemma exists in the repo, prove the finite closed form once.

### Summability consequence

From the per-mode bound:

```lean
theorem divDuhamel_gain_one_weightedL1
    (hE : WeightedL1 r Senv)
    (hE0 : ∀ k, 0 ≤ Senv k)
    (hdom : ∀ s ∈ Set.Icc a t, ∀ k, |S s k| ≤ Senv k) :
    WeightedL1 (r+1)
      (fun k => ∫ s in a..t,
          Real.exp (-((t - s) * lam k)) * Real.sqrt (lam k) * S s k)
```

Proof:

```lean
exact Summable.of_nonneg_of_le
  (fun k => by positivity)
  (fun k => divDuhamel_mode_weighted_bound ... k)
  (hE.mul_left Cdiv)
```

up to rewriting `(1+λ)^((r+1)/2)` into the `WeightedL1 (r+1)` definition.

This lemma is the formal heart of the `+1` ladder.

---

## 3. Non-divergence Duhamel lemma

For the logistic/non-divergence source, one can prove either the full `+2` gain or only the `+1` gain needed by the ladder.

If

```text
G_k(s) ≤ Genv_k,
```

then for `k≥1`,

```text
∫_a^t exp(-(t-s)λ_k) ds ≤ 1/λ_k.
```

So

```text
(1+λ_k)^((r+2)/2)
  ∫ exp(...) |G_k(s)| ds
≤ ((1+λ_k)/λ_k) * (1+λ_k)^(r/2) Genv_k
≤ C0 * (1+λ_k)^(r/2) Genv_k,
```

where

```text
C0 := (1+π²)/π²
```

for `k≥1`. At `k=0`, the multiplier is just the time length `t-a`; on a finite window it contributes one finite coordinate and can be handled by `Summable.update` or by adding a single-mode envelope.

Lean-friendly form:

```lean
theorem heatDuhamel_gain_two_weightedL1
    (hT : t - a ≤ Tlen)
    (hE : WeightedL1 r Genv)
    (hE0 : ∀ k, 0 ≤ Genv k)
    (hdom : ∀ s ∈ Set.Icc a t, ∀ k, |G s k| ≤ Genv k) :
    WeightedL1 (r+2)
      (fun k => ∫ s in a..t,
          Real.exp (-((t - s) * lam k)) * G s k)
```

For the `A^r → A^{r+1}` ladder, a weaker `+1` non-divergence lemma is enough and slightly easier at low modes; but proving `+2` once is more reusable.

---

## 4. Per-slice versus window-uniform

### What per-slice is enough for

If your only goal at a fixed time `t₀` is the algebraic statement

```text
q_t(t₀) ∈ A³_sin,
```

then per-slice hypotheses suffice:

```text
u(t₀) ∈ A³_cos,
u_t(t₀) ∈ A³_cos,
```

plus resolver, denominator composition, and product bridge lemmas. No time window is needed for this purely algebraic product conclusion.

### What per-slice is not enough for

For a Duhamel smoothing estimate such as

```text
u(t₀) = heat leg + ∫_{a}^{t₀} heat(t₀-s) source(s) ds,
```

per-slice membership of `source(s)` for each `s` is not enough. You need either:

```text
∃ E, WeightedL1 r E ∧ ∀ s∈[a,t₀], ∀ k, |source_k(s)| ≤ E_k
```

or an integrable-in-time majorant:

```text
∀ k, |source_k(s)| ≤ E_k(s),
Σ_k w_r(k) ∫_a^{t₀} E_k(s) ds < ∞.
```

The former is much easier to formalize.

### Correct local way to avoid the old gap

You can avoid a **global** window-uniform flux envelope by localizing around the target time. For an interior time `t₀>0`, choose

```text
0 < a < t₀ < b < T.
```

Prove trajectory envelopes only on `[a,b]`. This is enough for:

- local `A³` membership at `t₀`,
- local time-C¹ / dominated-tsum arguments near `t₀`,
- `DuhamelSourceTimeC1` if it is a clamped-window statement around `t₀`.

So the answer is:

```text
per-slice alone: enough for pointwise algebra, not enough for Duhamel/time-C¹;
local positive-time window: enough and avoids the global campaign gap.
```

If the theorem `DuhamelSourceTimeC1` includes a window-uniform derivative bound, then it necessarily needs at least a local window envelope or an integrable majorant. A fixed-time proof cannot supply continuity/uniformity by itself.

---

## 5. Product and source lemmas at level `r`

The weighted-Wiener product lemmas should be independent of the PDE.

### Product closure

```lean
theorem weightedL1_trueCosProd
    (hr : 0 ≤ r)
    (ha : WeightedL1 r a) (hb : WeightedL1 r b) :
    WeightedL1 r (trueCosProd a b)

theorem weightedL1_trueMixedProd
    (hr : 0 ≤ r)
    (ha : WeightedL1 r a) (hb : WeightedL1 r b) :
    WeightedL1 r (trueMixedProd a b)
```

Need envelope versions too:

```lean
theorem envelopes_trueCosProd_weighted
    (hr : 0 ≤ r)
    (hEa : WeightedL1 r Ea) (hEb : WeightedL1 r Eb)
    (ha : Envelopes Ea a) (hb : Envelopes Eb b) :
    Envelopes (trueCosProd Ea Eb) (trueCosProd a b)

theorem envelopes_trueMixedProd_weighted
    ...
```

The envelope monotonicity can reuse the same `trueCosProd`/`trueMixedProd` monotonicity style already present for `H^σ`, but now with weighted-ℓ¹ membership.

### Resolver gain

```lean
theorem weightedL1_resolver_gain_two
    (hμ : 0 < μ) (ha : WeightedL1 r a) :
    WeightedL1 (r+2) (fun k => a k / (μ + lam k))

theorem weightedL1_resolver_deriv_gain_one
    (hμ : 0 < μ) (ha : WeightedL1 r a) :
    WeightedL1 (r+1)
      (fun k => Real.sqrt (lam k) * (a k / (μ + lam k)))
```

Use monotonicity to downgrade from `A^{r+1}` to `A^r` when building products.

### Denominator composition

This is the one true analytic Nemytskii/Wiener-Lévy lemma:

```lean
theorem weightedL1_one_add_rpow_neg
    (hr : 0 ≤ r)
    (hβ : 0 ≤ β)
    (hv_nonneg : ∀ x, 0 ≤ v x)
    (hvA : WeightedL1 r (cosineCoeffs v)) :
    WeightedL1 r
      (cosineCoeffs (fun x => (1 + v x)^(-β)))
```

and similarly for exponent `-β-1` if needed for `q_t`.

### Chem flux at level `r`

For `u` itself:

```lean
theorem chemFlux_sinA_of_u_cosA
    (hr : 0 ≤ r)
    (huA : TrajA r J (fun t k => cosineCoeffs (u t) k))
    (resolver / denominator / product bridge hypotheses) :
    TrajA r J (fun t k => sineCoeffs (fun x => W t x * vx t x) k)
```

For `u_t` / linearized source:

```lean
theorem chemFluxLin_sinA_of_u_A3_and_U_A-r
    (hr : 0 ≤ r) (hr3 : r ≤ 3)
    (huA3 : TrajA 3 J (fun t k => cosineCoeffs (u t) k))
    (hUA  : TrajA r J (fun t k => cosineCoeffs (U t) k))
    (resolver / denominator / product bridge hypotheses) :
    TrajA r J (fun t k => sineCoeffs (Qlin t) k)
```

where

```text
Qlin = U v_x D + u V_x D - β u v_x V D₁.
```

---

## 6. Ladder step lemmas

### For `u`

Assume the mild coefficient identity on a window with a restart time `a`:

```text
û_k(t) = heat_k(t,a) + chemDuhamel_k(t,a) + logDuhamel_k(t,a).
```

Then:

```lean
theorem u_A_step
    (hr : 0 ≤ r)
    (huA : TrajA r Jbig (fun t k => cosineCoeffs (u t) k))
    (hflux : TrajA r Jbig (fun t k => sineCoeffs (Q t) k))
    (hlog  : TrajA r Jbig (fun t k => cosineCoeffs (Log t) k))
    (hmild : coefficient mild identity on target window J using source on Jbig)
    (hheat : positive-time heat leg is A^{r+1} on J) :
    TrajA (r+1) J (fun t k => cosineCoeffs (u t) k)
```

The proof uses:

- heat leg smoothing for the restart/initial term;
- `divDuhamel_gain_one_weightedL1` for chemotaxis;
- `heatDuhamel_gain_two_weightedL1` or a weaker `+1` lemma for logistic;
- sum closure of `WeightedL1`.

### For `U = u_t`

Same form, with the linearized mild identity:

```lean
theorem u_t_A_step
    (hr : 0 ≤ r) (hr3 : r ≤ 3)
    (huA3 : TrajA 3 Jbig (fun t k => cosineCoeffs (u t) k))
    (hUA  : TrajA r Jbig (fun t k => cosineCoeffs (U t) k))
    (hQlin : TrajA r Jbig (fun t k => sineCoeffs (Qlin t) k))
    (hRlin : TrajA r Jbig (fun t k => cosineCoeffs (Rlin t) k))
    (hUmild : linearized coefficient mild identity) :
    TrajA (r+1) J (fun t k => cosineCoeffs (U t) k)
```

Again the divergence term is limiting; the reaction derivative term gains more.

---

## 7. Seed lemmas

You need a seed before the ladder starts.

### `A⁰` seed for `u`

Options:

1. From a positive-time `MemHSigma σ` theorem with `σ>1/2`:

```lean
theorem weightedL1_zero_of_memHSigma_gt_half
    (hσ : 1/2 < σ)
    (hH : MemHSigma σ a) :
    WeightedL1 0 a
```

by Cauchy-Schwarz.

2. From an already-landed trajectory envelope at `σ>1/2`.

3. From a separate positive-time `A⁰` theorem.

Do not claim `L∞` or `L²` implies `A⁰`; it does not.

### `A⁰` seed for `u_t`

Your per-mode derivative theorem seeds the `U` ladder only if it gives a window-uniform ℓ¹ envelope:

```lean
hU_A0_seed : TrajA 0 Jbig (fun t k => deriv (fun s => cosineCoeffs (u s) k) t)
```

or equivalently for the realized `U` coefficients.

Per-mode differentiability alone does not seed the ladder.

---

## 8. Three-step wrappers

For `u`:

```lean
theorem positiveTime_u_A3_of_A0_seed
    (hA0 : TrajA 0 J0 uCoeff)
    (hstep : ∀ r ∈ {0,1,2}, u_A_step r) :
    TrajA 3 J3 uCoeff
```

For `U`:

```lean
theorem positiveTime_u_t_A3_of_A0_seed
    (huA3 : TrajA 3 Jbig uCoeff)
    (hUA0 : TrajA 0 Jbig UCoeff)
    (hstepU : ∀ r ∈ {0,1,2}, u_t_A_step r) :
    TrajA 3 J UCoeff
```

In Lean, avoid literal finite-set recursion if it becomes annoying. Just apply the step three times with `r=0`, `r=1`, `r=2`, using `norm_num`/`linarith` for side conditions.

---

## 9. Dependency order: minimal formalization plan

Here is the clean dependency order.

### Lemma 1: weighted ℓ¹ infrastructure

```lean
WeightedL1
WeightedL1.mono
WeightedL1.add
WeightedL1.smul
weightedL1_zero_of_memHSigma_gt_half
```

### Lemma 2: heat/Duhamel smoothing

```lean
heat_posTime_weightedL1_of_coeff_bound

divDuhamel_mode_weighted_bound

divDuhamel_gain_one_weightedL1

heatDuhamel_gain_two_weightedL1
```

The exact divergence smoothing constant is:

```text
Cdiv = sqrt(1 + 1/π²) = sqrt(1+π²)/π.
```

### Lemma 3: weighted Wiener algebra and resolver

```lean
weightedL1_trueCosProd
weightedL1_trueMixedProd
weightedL1_resolver_gain_two
weightedL1_resolver_deriv_gain_one
weightedL1_one_add_rpow_neg       -- composition
```

### Lemma 4: source regularity at level `r`

```lean
chemFlux_sinA_of_u_cosA
logistic_cosA_of_u_cosA
chemFluxLin_sinA_of_u_A3_and_U_A-r
reactionLin_cosA_of_u_A3_and_U_A-r
```

### Lemma 5: ladder steps

```lean
u_A_step
u_t_A_step
```

### Lemma 6: three-step wrappers

```lean
positiveTime_u_A3_of_A0_seed
positiveTime_u_t_A3_of_A0_seed
```

### Lemma 7: chem source time-C¹ consumer

Once both wrappers are available:

```lean
chemSource_timeC1_of_u_A3_and_u_t_A3
```

This final theorem should be mostly product/chain-rule/coefficient-swap, not parabolic smoothing.

---

## Final answer

1. The exact divergence Duhamel constant for the `+1` step is

```text
Cdiv = sup_{k≥1} sqrt(1+λ_k)/sqrt(λ_k)
     = sqrt(1 + 1/π²).
```

The per-mode bound is

```text
(1+λ_k)^((r+1)/2)
|∫_a^t e^{-(t-s)λ_k} sqrt(λ_k) S_k(s) ds|
≤ Cdiv (1+λ_k)^(r/2) Esrc_k.
```

Mode zero is killed by `sqrt(λ_0)=0`.

2. Per-slice `A³` is enough for pointwise algebra like `q_t(t)∈A³_sin`, but not enough for Duhamel smoothing or `DuhamelSourceTimeC1` if that theorem needs continuity/window-uniform derivative bounds. Use **local positive-time windows** `[a,b]⊂(0,T)` or integrable-in-time majorants. This sidesteps the global campaign gap but not the need for a local envelope.

3. The clean formalization is the six-lemma ladder above: weighted-ℓ¹ infrastructure, divergence Duhamel gain, Wiener products/resolver/composition, source-at-level-`r`, ladder step, and three-step wrapper. Apply the same pattern to `u` and to `u_t` using the linearized equation.
