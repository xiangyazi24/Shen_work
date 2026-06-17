═══ BRIDGE cron | 82a0e0c1 | 9811 chars 1564 words 347 lines | 415s | prov=network | OK ═══
═══ BRIDGE cron | 82a0e0c1 | 9811 chars 1564 words 347 lines | 415s | prov=network | OK ═══
## (1) Exact σ-power

The bound is

```text
‖∂ₓₓ S(σ) h‖∞ ≤ Cθ · [h]_{C^θ} · σ^{-1 + θ/2}
```

which is the same as

```text
Cθ · [h]_{C^θ} · σ^{(θ-2)/2}.
```

Derivation from the Gaussian Hessian bound:

```text
|∂ₓₓ K_N(σ,x,y)| ≤ C σ^{-3/2} exp(-c |x-y|²/σ)
```

and the Hölder cancellation:

```text
|h(y) - h(x)| ≤ [h]_{C^θ} |x-y|^θ.
```

Then

```text
|∂ₓₓ S(σ)h(x)|
≤ C [h]θ ∫₀¹ σ^{-3/2} exp(-c|x-y|²/σ) |x-y|^θ dy
≤ C [h]θ ∫ℝ σ^{-3/2} exp(-c r²/σ) |r|^θ dr.
```

Set `r = √σ z`. Then `dr = √σ dz`, so

```text
σ^{-3/2} ∫ℝ |r|^θ exp(-c r²/σ) dr
= σ^{-3/2} σ^{θ/2} σ^{1/2} ∫ℝ |z|^θ exp(-c z²) dz
= Cθ σ^{-1 + θ/2}.
```

So the exponent is

```text
-1 + θ/2 = (θ - 2)/2.
```

The endpoint time integral is finite exactly because

```text
∫₀ᵗ σ^{-1+θ/2} dσ = (2/θ) t^{θ/2} < ∞
```

for every `θ > 0`.

This is already the exponent used in the repo: `IntervalFullKernelSecondDerivCtheta.lean` states the cancellation estimate as `‖∂ₓₓ S(σ)h‖∞ ≤ Cθ · σ^{−1+θ/2} · [h]_{C^θ}`, explicitly noting that this is integrable in `σ` for `θ > 0`. fileciteturn97file0L10-L17 The proved theorem `neumannHeatSecondDeriv_Ctheta_to_Linfty` has exactly the Lean exponent

```lean
t ^ (-1 + θ / 2 : ℝ)
```

in its conclusion. fileciteturn102file0L48-L66

---

## (2) Cosine series vs method of images

For this specific lemma, the **method-of-images / Gaussian-kernel route is cleaner** in Lean.

The reason is that the target estimate is a **kernel moment estimate**:

```text
∫ |∂ₓₓ K_N(σ,x,y)| |x-y|^θ dy ≤ Cθ σ^{-1+θ/2}.
```

With the image kernel, the proof reduces to:

```text
Gaussian Hessian bound
+ weighted Gaussian moment scaling
+ summability over reflected image cells.
```

That is local calculus plus summability. The repo already follows this route. It defines the Gaussian absolute moment, proves integrability of `|u|^θ exp(-b u²)`, and proves the scaling law behind the power `σ^{-1+θ/2}`. fileciteturn97file0L86-L143 It also has a dedicated weighted kernel-mass brick for the interval-Neumann full kernel. fileciteturn98file0L56-L60

The cosine-series route is beautiful for cancellation:

```text
K_N(σ,x,y) = 1 + Σ_{n≥1} e^{-(nπ)²σ} φₙ(x)φₙ(y),
```

so the `n = 0` mode vanishes after `∂ₓₓ`, and

```text
∫₀¹ ∂ₓₓK_N(σ,x,y) dy = 0
```

is immediate. But the **Hölder smoothing estimate** becomes a spectral coefficient problem. You would need to prove sharp enough bounds for cosine coefficients of a `C^θ` function and then estimate sums of the form

```text
Σ n² e^{-n²π²σ} |aₙ|.
```

That is formalizable, but it is more infrastructure-heavy than the direct kernel moment. It also risks proving a weaker exponent unless the coefficient-decay lemma is sharp and carefully stated.

The best Lean strategy is a **hybrid**:

1. Use **kernel/images** for the `C^θ → L∞` Hessian estimate:
   ```lean
   neumannHeatSecondDeriv_Ctheta_to_Linfty
   ```
2. Use **spectral/cosine** only where it is genuinely simpler, such as semigroup composition or commutation. The repo’s `ChemMildC1eta.lean` does exactly this: it lists the kernel-side bricks for mean-zero, weighted mass, and `C^θ→L∞`, then uses a Route B semigroup split/commutation to get the stronger `C^θ→C^η` estimate without a third-derivative kernel. fileciteturn96file0L21-L37 fileciteturn96file0L53-L63

Mathlib gives many Gaussian/integrability tools, but it does **not** hand you the interval Neumann heat-kernel derivative estimates as a ready theorem. In this repo, those estimates are custom bricks in `IntervalFullKernelSecondDerivCtheta.lean`; the file explicitly proves the mean-zero cancellation, Gaussian moment scaling, weighted mass, and final `C^θ→L∞` bound. fileciteturn97file0L35-L57 fileciteturn102file0L46-L66

So: **do not try to start with pure cosine estimates for this endpoint lemma.** Use the method-of-images kernel for the hard Hölder cancellation estimate; use cosine only for algebraic semigroup identities if needed.

---

## (3) Clean Lean lemma chain

Here is the exact chain I would mirror.

### Brick 1: constant preservation / mean-zero Hessian

First prove the semigroup preserves constants:

```lean
theorem intervalFullSemigroupOperator_const
    {t : ℝ} (ht : 0 < t) (c : ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t (fun _ => c) x = c
```

The repo has this theorem and proves it from the kernel mass identity. fileciteturn97file0L37-L47

Then differentiate twice in `x` and use derivative-under-integral to get:

```lean
theorem intervalNeumannFullKernel_secondDeriv_integral_zero
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y,
      deriv (fun z => deriv (fun z => intervalNeumannFullKernel t z y) z) x
      ∂(intervalMeasure 1)) = 0
```

This is already present as the “Brick 1 — mean-zero cancellation” theorem. fileciteturn97file0L49-L84

This is conceptually routine, but in Lean it depends on the already-available second-order derivative-under-integral lemma.

---

### Brick 2: cancellation rewrite

For

```lean
K₂ t x y :=
  deriv (fun z => deriv (fun z => intervalNeumannFullKernel t z y) z) x
```

prove

```lean
∂ₓₓ S(t) h x
  = ∫ y, K₂ t x y * (h y - h x) ∂(intervalMeasure 1)
```

The repo does this inside `neumannHeatSecondDeriv_Ctheta_to_Linfty`: it obtains the second-derivative integral representation, uses the mean-zero identity, and rewrites

```lean
∫ K y * h y = ∫ K y * (h y - h x).
```

See the `hmean0` and `hsub` block. fileciteturn102file0L68-L95

This is routine once you have integrability and mean-zero.

---

### Brick 3: weighted Hessian mass

Prove the weighted moment estimate:

```lean
theorem intervalNeumannFullKernel_secondDeriv_weighted_mass
    (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ∫ y in (0:ℝ)..1,
      |K₂ t x y| * |x - y| ^ θ
      ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ)
```

This is the genuine kernel estimate. It is the hard analytic brick because it requires:

```text
Gaussian Hessian pointwise bound,
image/reflection summability,
weighted moment scaling,
period-cell tiling/Tonelli.
```

The file’s header identifies this as Brick 2, and the proof uses the whole-line weighted bound after Tonelli/tiling. fileciteturn97file0L86-L100 fileciteturn102file0L28-L44

This is the main hard lemma.

---

### Brick 4: `C^θ → L∞` Hessian smoothing

Combine the cancellation rewrite with the Hölder bound:

```lean
|h y - h x| ≤ Hh * |x - y| ^ θ
```

to get

```lean
theorem neumannHeatSecondDeriv_Ctheta_to_Linfty
    {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    ...
    :
    |deriv (fun z => deriv (fun w =>
       intervalFullSemigroupOperator t h w) z) x|
      ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) * Hh
```

This theorem is already proved in the repo. fileciteturn102file0L48-L66 Its proof sequence is exactly:

```text
DUI representation
→ mean-zero cancellation
→ Hölder modulus
→ weighted mass estimate
```

as described in its docstring. fileciteturn102file0L48-L58

---

### Brick 5: time-integral convergence

State the time-integrability lemma separately:

```lean
theorem integrable_sigma_neg_one_add_theta_half
    (hθ : 0 < θ) :
    IntervalIntegrable
      (fun σ : ℝ => σ ^ (-1 + θ / 2 : ℝ))
      volume 0 t
```

or in the form you actually need:

```lean
∫ σ in (0)..t, σ ^ (-1 + θ / 2 : ℝ)
  = (2 / θ) * t ^ (θ / 2)
```

under `0 < t`, `0 < θ`.

This part is routine compared with Brick 3. The exponent condition is the whole point:

```text
-1 + θ/2 > -1  ⇔  θ > 0.
```

For a Duhamel term

```text
D(t,x) = ∫₀ᵗ S(t-s) h(s) ds,
```

the endpoint estimate becomes

```text
|∂ₓₓD(t,x)|
≤ ∫₀ᵗ C [h(s)]_{C^θ} (t-s)^(-1+θ/2) ds.
```

If `[h(s)]_{C^θ}` is uniformly bounded near `s = t`, the integral is finite.

---

## What is genuinely hard?

The hard pieces are:

1. **Derivative-under-integral for the second kernel derivative**, if not already available.
2. **Weighted kernel mass**
   ```text
   ∫ |∂ₓₓK| |x-y|^θ ≤ C σ^{-1+θ/2}.
   ```
3. If you need `C^η` of `∂ₓₓS(σ)h`, the corresponding Schauder/Hölder upgrade.

The routine pieces are:

```text
constant preservation,
mean-zero cancellation after DUI,
algebraic subtraction of h(x),
Hölder modulus application,
time-power integrability.
```

The repo’s `ChemMildC1eta.lean` confirms this division: it says the kernel-side mean-zero, weighted-mass, and `C^θ→L∞` bricks are proved in `IntervalFullKernelSecondDerivCtheta.lean`, and then packages the stronger `C^θ→C^η` estimate using a semigroup split/commutation route. fileciteturn96file0L21-L37

---

## Recommended Lean theorem stack

A clean final skeleton would look like:

```lean
-- 1. Mean-zero Hessian kernel
theorem Kxx_integral_zero
    (hσ : 0 < σ) (x : ℝ) :
    ∫ y, Kxx σ x y ∂(intervalMeasure 1) = 0 := ...

-- 2. Cancellation identity
theorem neumannHeatSecondDeriv_cancel
    (hσ : 0 < σ) ... :
    deriv (fun z => deriv (fun w => S σ h w) z) x
      = ∫ y, Kxx σ x y * (h y - h x) ∂(intervalMeasure 1) := ...

-- 3. Weighted Hessian mass
theorem Kxx_weighted_mass
    (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∫ y in 0..1, |Kxx σ x y| * |x-y|^θ
      ≤ Cθ * σ^(-1 + θ/2) := ...

-- 4. Hölder cancellation estimate
theorem neumannHeatSecondDeriv_Ctheta_to_Linfty
    (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hHolder : ∀ a b ∈ [0,1], |h a - h b| ≤ Hh * |a-b|^θ) :
    |∂xx S(σ)h x| ≤ Cθ * σ^(-1 + θ/2) * Hh := ...

-- 5. Endpoint Duhamel integrability
theorem duhamel_secondDeriv_endpoint_bound
    (hθ0 : 0 < θ)
    (hH : ∀ s ∈ [0,t], HolderSeminormθ (h s) ≤ H) :
    ∫ σ in 0..t, Cθ * σ^(-1 + θ/2) * H < ∞ := ...
```

Your current repo already has the core version of (1), (3), and (4), with (2) embedded in (4). The remaining full `C²` Duhamel theorem is mostly a matter of packaging derivative-under-integral/time-continuity assumptions around this kernel estimate.
