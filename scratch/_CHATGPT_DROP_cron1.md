# ChatGPT git-drop (cron1)

## Q125 — Positive-time `A¹_cos` seed for the weighted-Wiener ladder

### Executive verdict

The `A¹` seed on a positive-time window is **not** a consequence of the `L∞` order box alone. The heat leg is easy and gives arbitrary positive-time smoothing. The Duhamel leg is the obstruction because the endpoint `s=t` has no heat smoothing.

The clean seed theorem should be factored as:

```text
positive-time Hilbert/Sobolev smoothing from L²/L∞
  ⇒ u ∈ H^θ on [η,T₀] for some θ>1/2
  ⇒ u ∈ A⁰ on [η,T₀]
  ⇒ flux q and logistic source are A⁰ on [η,T₀]
  ⇒ Duhamel gain gives u ∈ A¹ on [τ₀,T₀], with η<τ₀.
```

Equivalently, if you already have a window-uniform `A⁰` envelope for `u` on a buffered positive-time window `[η,T₀]`, then the `A¹` seed is straightforward. But trying to get the late-time source `A⁰` bound directly from `L∞` is circular/false.

So the minimal Lean seed input is not merely `L∞`; it is either:

```text
TrajA 0 [η,T₀] (cosineCoeffs u)
```

or a positive-time `MemHSigma θ`, `θ>1/2`, from which `TrajA 0` follows by Cauchy-Schwarz.

---

## 1. Heat leg: exact positive-time bound

Let

```text
λ_k = (kπ)²,
w_r(k) = (1+λ_k)^(r/2).
```

For the heat leg,

```text
(S(t)u₀)_k = exp(-tλ_k) û₀_k.
```

For `t ≥ τ₀ > 0`,

```text
Σ_k w_1(k) exp(-tλ_k)|û₀_k|
  ≤ Σ_k w_1(k) exp(-τ₀λ_k)|û₀_k|.
```

### If `u₀ ∈ L∞`

With your cosine normalization, there is a harmless constant `Ccos` such that

```text
|û₀_k| ≤ Ccos ‖u₀‖∞.
```

Then

```text
‖S(t)u₀‖_{A¹}
  ≤ Ccos ‖u₀‖∞ H₁(τ₀),
```

where

```text
H₁(τ₀) := Σ_k (1+λ_k)^(1/2) exp(-τ₀λ_k) < ∞.
```

This series is finite because `λ_k ~ k²`. Asymptotically,

```text
H₁(τ₀) ≲ τ₀^{-1}
```

as `τ₀↓0`.

Lean statement:

```lean
def heatWienerConst (r τ : ℝ) : ℝ :=
  ∑' k : ℕ, (1 + lam k) ^ (r / 2) * Real.exp (-(τ * lam k))

theorem heat_A1_of_linf_coeff_bound
    (hτ : 0 < τ₀)
    (hcoeff : ∀ k, |u0hat k| ≤ C0) :
    WeightedL1 1 (fun k => Real.exp (-(t * lam k)) * u0hat k)
```

with `t≥τ₀`, bounded by `C0 * heatWienerConst 1 τ₀`.

### If `u₀ ∈ L²`

Use Cauchy-Schwarz:

```text
Σ_k w_1(k) exp(-tλ_k)|û₀_k|
  ≤ (Σ_k |û₀_k|²)^(1/2)
     (Σ_k w_1(k)^2 exp(-2τ₀λ_k))^(1/2)
  = ‖u₀‖_{ℓ²} (Σ_k (1+λ_k) exp(-2τ₀λ_k))^(1/2).
```

This is also finite for every `τ₀>0` and behaves like `τ₀^{-3/4}` as `τ₀↓0`.

---

## 2. Duhamel split on `[τ₀,T₀]`

For `t∈[τ₀,T₀]`, split

```text
∫_0^t = ∫_0^η + ∫_η^t,
```

where choose, for example,

```text
η := τ₀/2.
```

Then for the early part `s∈[0,η]`,

```text
t-s ≥ τ₀/2.
```

This gives a genuine heat gap.

### Early Duhamel part: only bounded source is needed

For the logistic source `L(u)=u(1-u)`, the `L∞` box gives a flat coefficient bound

```text
|cosCoeff(L(u(s)))_k| ≤ C_L(M).
```

The early heat gap gives

```text
Σ_k w_1(k) ∫_0^η exp(-(t-s)λ_k)|L_k(s)|ds
  ≤ η C_L(M) Σ_k w_1(k) exp(-(τ₀/2)λ_k) < ∞.
```

For the chemotaxis divergence, write the pre-divergence flux

```text
q = u v_x (1+v)^(-β).
```

The `L∞` box plus resolver bounds give

```text
|q(s,x)| ≤ C_q(M,μ,β),
```

hence a flat bound on sine coefficients:

```text
|sineCoeff(q(s))_k| ≤ C_q'.
```

The divergence Duhamel has the extra `sqrt(λ_k)`, but the early heat gap still kills it:

```text
Σ_k w_1(k) ∫_0^η exp(-(t-s)λ_k) sqrt(λ_k)|q_k(s)|ds
  ≤ η C_q' Σ_k sqrt(1+λ_k) sqrt(λ_k) exp(-(τ₀/2)λ_k) < ∞.
```

So the early interval is harmless with only `L∞` information.

### Late Duhamel part: endpoint needs source regularity

For `s∈[η,t]`, the elapsed time `t-s` may be zero. No exponential gap remains.

For the chemotaxis divergence term, if only

```text
|sineCoeff(q(s))_k| ≤ C
```

is known, then

```text
sqrt(λ_k) ∫_η^t exp(-(t-s)λ_k) C ds
  ≤ C / sqrt(λ_k).
```

Multiplying by the `A¹` target weight gives roughly

```text
sqrt(1+λ_k) / sqrt(λ_k) ≈ 1,
```

which is not summable. Thus `L∞` cannot control the late chemotaxis Duhamel tail in `A¹`.

For the non-divergence logistic term, a flat coefficient bound gives

```text
∫_η^t exp(-(t-s)λ_k) C ds ≤ C/λ_k.
```

Multiplying by `sqrt(1+λ_k)` gives about `1/k`, again not summable. Thus `L∞` is also borderline insufficient for the late logistic tail in `A¹`.

Therefore the late part needs a genuine `A⁰` source envelope:

```text
q ∈ A⁰_sin on [η,T₀],
L(u) ∈ A⁰_cos on [η,T₀].
```

Then the banked Duhamel estimates give:

```text
q ∈ A⁰_sin      ⇒ chem Duhamel ∈ A¹_cos,
L(u) ∈ A⁰_cos   ⇒ logistic Duhamel ∈ A²_cos, hence A¹_cos.
```

---

## 3. How to get the late `A⁰` source without circularity

A direct `A⁰` source bound from `L∞` is false. But it can be seeded from a weaker Hilbert/Sobolev positive-time smoothing result.

### Step 1: get `u ∈ H^θ`, `θ>1/2`, on `[η,T₀]`

From the `L∞` box, the pre-divergence flux `q` and logistic source are bounded in `L²` on the finite interval. For the divergence term, heat smoothing from an `L²` pre-divergence flux gives Sobolev gain up to but not including one derivative:

```text
q ∈ L∞_t L²_x
  ⇒ ∫ S(t-s) ∂x q(s) ds ∈ H^θ_x
```

for every

```text
θ < 1.
```

The semigroup estimate is

```text
‖A^{θ/2} S(ρ) ∂x q‖₂
  ≤ C ρ^{-(θ+1)/2} ‖q‖₂,
```

and the singularity is integrable near `ρ=0` exactly when

```text
(θ+1)/2 < 1,
```

that is `θ<1`.

Choose any

```text
1/2 < θ < 1.
```

Then on `[η,T₀]` one obtains a window-uniform `MemHSigma θ` envelope for `u`, with constants depending on `η,T₀,M,μ,β` and the initial datum norm.

### Step 2: embed `H^θ` into `A⁰`

For `θ>1/2`, Cauchy-Schwarz gives

```text
Σ_k |û_k|
  ≤ (Σ_k (1+λ_k)^θ |û_k|²)^(1/2)
     (Σ_k (1+λ_k)^(-θ))^(1/2)
  < ∞.
```

So:

```text
u ∈ H^θ, θ>1/2 ⇒ u ∈ A⁰_cos.
```

Lean theorem:

```lean
theorem weightedL1_zero_of_memHSigma_gt_half
    (hθ : 1/2 < θ)
    (hH : MemHSigma θ a) :
    WeightedL1 0 a
```

### Step 3: get source `A⁰` from `u∈A⁰`

Weighted Wiener `A⁰` is a Banach algebra. From

```text
u ∈ A⁰_cos
```

we get:

```text
v = R_μ u ∈ A²_cos ⊂ A⁰_cos,
v_x ∈ A¹_sin ⊂ A⁰_sin,
D=(1+v)^(-β) ∈ A⁰_cos,
W=uD ∈ A⁰_cos,
q=Wv_x ∈ A⁰_sin,
L(u)=u(1-u) ∈ A⁰_cos.
```

Thus the late source `A⁰` envelope is obtained non-circularly from the Hilbert positive-time seed.

### Step 4: Duhamel gains `A¹`

Use the banked `+1` divergence ladder:

```text
q ∈ A⁰_sin ⇒ chem Duhamel ∈ A¹_cos.
```

Use non-divergence heat smoothing:

```text
L(u) ∈ A⁰_cos ⇒ logistic Duhamel ∈ A²_cos ⊂ A¹_cos.
```

Together with the heat leg and early Duhamel estimates, this gives:

```text
u ∈ A¹_cos on [τ₀,T₀].
```

This `A¹` seed can then feed the cleaner weighted-Wiener ladder to `A³`.

---

## 4. Minimal Lean-formalizable seed theorem

A good theorem shape is:

```lean
theorem positiveTime_A1_seed_of_Htheta_seed
    {η τ₀ T₀ θ : ℝ}
    (hη : 0 < η) (hητ : η < τ₀) (hτT : τ₀ ≤ T₀)
    (hθ0 : 1/2 < θ) (hθ1 : θ < 1)

    -- mild identity on [0,T₀]
    (hmild : coefficient mild identity for u)

    -- initial heat data; L∞ or L² coefficient bound is enough
    (hheat : heat leg A¹ on [τ₀,T₀])

    -- Hilbert positive-time seed on [η,T₀]
    (hHθ : TrajectoryHSigmaEnvelope θ T₀_on_eta_window
      (fun t => cosineCoeffs (u t)))

    -- product/resolver/composition bridges at A⁰
    (hfluxA0 : from TrajA 0 [η,T₀] u to TrajA 0 [η,T₀] q_sine)
    (hlogA0  : from TrajA 0 [η,T₀] u to TrajA 0 [η,T₀] logistic_cos)

    -- Duhamel gain lemmas
    (hdivGain : q A⁰_sin -> chem Duhamel A¹_cos)
    (hlogGain : logistic A⁰_cos -> logistic Duhamel A¹_cos) :
    TrajA 1 (Set.Icc τ₀ T₀) (fun t k => cosineCoeffs (u t) k)
```

In practice, you can factor this into smaller lemmas:

1. `A0_of_Htheta_gt_half`:

   ```lean
   TrajectoryHSigmaEnvelope θ [η,T₀] uCoeff → TrajA 0 [η,T₀] uCoeff
   ```

2. `source_A0_of_u_A0`:

   ```lean
   TrajA 0 [η,T₀] uCoeff →
     TrajA 0 [η,T₀] qSineCoeff ∧ TrajA 0 [η,T₀] logisticCoeff
   ```

3. `duhamel_A1_of_source_A0_split`:

   Early part from heat gap and `L∞`; late part from source `A⁰`.

4. `positiveTime_u_A1_seed` wrapper.

---

## 5. Answer to the three questions

### Q1

The heat leg is completely fine. For `t≥τ₀>0`,

```text
Σ_k (1+λ_k)^(1/2)e^{-tλ_k}|û₀_k|
  ≤ Ccos ‖u₀‖∞ Σ_k (1+λ_k)^(1/2)e^{-τ₀λ_k},
```

and the last sum is finite. If working from `L²`, use the Cauchy-Schwarz bound

```text
≤ ‖u₀‖₂ (Σ_k (1+λ_k)e^{-2τ₀λ_k})^(1/2).
```

These constants depend on `τ₀` and blow up as `τ₀↓0`, as expected.

### Q2

Split the Duhamel integral at `η=τ₀/2`.

- On `[0,η]`, the gap `t-s≥τ₀/2` gives exponential heat smoothing. Bounded source coefficients are enough, even for the chemotaxis divergence with its `sqrt(λ)` multiplier.
- On `[η,t]`, there is no gap at `s=t`; bounded coefficients are not enough. You need an `A⁰` source envelope for the late source.

That late `A⁰` source envelope is circular if you try to get it directly from the desired `A¹` conclusion, but it is non-circular if obtained from an intermediate positive-time `H^θ`, `θ>1/2`, seed, because `H^θ → A⁰`.

### Q3

The theorem

```text
mild identity + crude A⁰ source bound on [η,T₀] ⇒ u∈A¹ on [τ₀,T₀]
```

is valid and Lean-formalizable. The crude `A⁰` source bound is circular if the only route to it is `u∈A¹`. It is not circular if you first prove:

```text
u∈H^θ on [η,T₀],  θ∈(1/2,1),
```

from the `L∞`/`L²` parabolic smoothing estimate, then embed to `A⁰` and build the source by Wiener products.

So the seed should be built in two layers:

```text
L∞/L² order box → positive-time H^θ, θ>1/2 → A⁰ → source A⁰ → u A¹.
```

This is the clean non-circular starting point for the already-banked `A¹→A²→A³` weighted-Wiener ladder.

---

## Final recommendation

Do not try to prove `A¹` directly from `L∞`. Add a Hilbert seed lemma:

```lean
positiveTime_Htheta_seed_of_L2_sources
  (1/2 < θ) (θ < 1) : TrajectoryHSigmaEnvelope θ [η,T₀] uCoeff
```

then:

```lean
TrajA0_of_Htheta_seed
source_A0_of_u_A0
positiveTime_A1_seed_of_source_A0
```

This gives a non-circular and Lean-friendly seed for the weighted-Wiener ladder.
