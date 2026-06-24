# Q90 (cron2): classical regularity bridges for the EWA Duhamel chemotaxis solution

## Executive answer

For the time-derivative bridge, the clean sufficient condition is a **locally uniform `ℓ¹` majorant for the source coefficients** plus the heat-smoothing majorant for the initial coefficients. The endpoint `r=t` in Duhamel contributes the source value `F_n(t)`; the differentiated kernel contributes an integrated majorant bounded by the same source majorant. The summable bound is therefore `2 S_n`, **not** `λ_n S_n`.

For the resolver bridge, the package is direct: if

```text
v̂_n(t) = û_n(t)/(μ+λ_n),   μ>0,
λ_n=(nπ)^2,
```

then division by `μ+λ_n` gains two Neumann/cosine derivatives. In particular, `u(t)` in weighted Wiener order `0` already gives `v(t)∈C²_x`, because

```text
λ_n |v̂_n| = λ_n |û_n|/(μ+λ_n) ≤ |û_n|.
```

Strict positivity of `v` is not a spectral-summability fact; it comes from the positive Neumann resolvent kernel or the strong maximum principle. From `u≥0` one gets `v≥0`; from `u≥0` and `u` nontrivial one gets `v>0`.

## Notation

Let

```text
λ_n := (nπ)^2,
e_n(x) := cos(nπx).
```

Ignore harmless normalization constants for the cosine basis; in Lean either carry them explicitly or absorb them into the coefficient maps.

For a coefficient sequence `c : ℕ → ℝ`, define the weighted Wiener seminorm

```text
A_s(c) := ∑' n, (1+λ_n)^(s/2) * |c_n|.
```

`A_0(c)<∞` gives absolute/uniform convergence of

```text
∑ c_n cos(nπx),
```

because `|cos(nπx)|≤1`. `A_2(c)<∞` gives uniform convergence of the second spatial derivative series, since `λ_n≤1+λ_n`.

## Part A: time derivative of the Duhamel coefficient series

Write the combined source coefficient as

```text
F_n(t) := a * ChemDiv_n(t) + Logistic_n(t),   a=-χ₀>0.
```

The Duhamel coefficient is

```text
u_n(t)
  = exp(-λ_n t) u0_n
    + ∫_0^t exp(-λ_n*(t-r)) F_n(r) dr.
```

For `n=0`, `λ_0=0`, so

```text
u_0'(t)=F_0(t).
```

For all `n`, the coefficient derivative is

```text
u_n'(t)
  = -λ_n exp(-λ_n t) u0_n
    + F_n(t)
    - ∫_0^t λ_n exp(-λ_n*(t-r)) F_n(r) dr

  = -λ_n u_n(t) + F_n(t).
```

The second form is often the PDE diagonal identity. The first form is the best form for proving the derivative series is uniformly summable.

## The endpoint `r=t` and the correct majorant

Let `I=[τ,T₁]⊂(0,T)` be a compact time subinterval with `0<τ≤T₁<T`. To control the derivative series uniformly on `I`, it is enough to assume:

```text
sourceMajorant_on_[0,T₁]:
  ∃ S : ℕ → ℝ,
    Summable S ∧
    (∀ n, 0 ≤ S n) ∧
    (∀ n, ∀ r∈[0,T₁], |F_n(r)| ≤ S n),

initialHeatDerivativeMajorant_on_I:
  Summable (fun n => λ_n * exp(-λ_n*τ) * |u0_n|).
```

Then, for `t∈I`,

```text
| -λ_n exp(-λ_n t) u0_n |
  ≤ λ_n exp(-λ_n τ) |u0_n|.
```

For the Duhamel part,

```text
|F_n(t)| ≤ S_n,
```

and

```text
|∫_0^t λ_n exp(-λ_n*(t-r)) F_n(r) dr|
  ≤ ∫_0^t λ_n exp(-λ_n*(t-r)) S_n dr
  = (1 - exp(-λ_n t)) S_n
  ≤ S_n.
```

Thus the whole derivative coefficient has the summable majorant

```text
|u_n'(t)|
  ≤ λ_n exp(-λ_n τ) |u0_n| + 2 S_n.          (A-majorant)
```

This is the exact bound to feed to a Weierstrass/M-test style termwise derivative theorem.

Important: the pointwise differentiated kernel satisfies

```text
|∂_t [ exp(-λ_n*(t-r)) F_n(r) ]|
  ≤ λ_n exp(-λ_n*(t-r)) S_n.
```

Do **not** take `sup_{r≤t}` of this bound, because at `r=t` it becomes `λ_n S_n`, which is usually not summable. The correct operation is to integrate the kernel first:

```text
∫_0^t λ_n exp(-λ_n*(t-r)) dr ≤ 1.
```

So the summable derivative majorant is `2S_n`, not `λ_nS_n`.

## Lean-formalizable termwise derivative lemma

A general theorem sufficient for `htimeDeriv/hdiffU` is:

```lean
/-- Termwise time derivative for an absolutely/uniformly summable cosine series. -/
theorem hasDerivAt_tsum_cos_of_uniform_deriv_majorant
    {I : Set ℝ} {c cdot : ℕ → ℝ → ℝ} {t : ℝ}
    (ht : t ∈ I)
    (hI_mem_nhds : I ∈ 𝓝 t)
    (hc_deriv : ∀ n, ∀ s ∈ I, HasDerivAt (fun τ => c n τ) (cdot n s) s)
    (hval_maj : ∃ A : ℕ → ℝ, Summable A ∧
      ∀ n s, s ∈ I → |c n s| ≤ A n)
    (hderiv_maj : ∃ B : ℕ → ℝ, Summable B ∧
      ∀ n s, s ∈ I → |cdot n s| ≤ B n) :
    ∀ x,
      HasDerivAt
        (fun s => ∑' n, c n s * Real.cos (n * Real.pi * x))
        (∑' n, cdot n t * Real.cos (n * Real.pi * x))
        t :=
by
  -- Weierstrass M-test + termwise derivative theorem.
  sorry
```

The Duhamel-specific instantiation uses

```lean
cdot n t = -lambda n * Real.exp (-(lambda n) * t) * u0Coeff n
           + F n t
           - ∫ r in 0..t,
               lambda n * Real.exp (-(lambda n) * (t-r)) * F n r
```

with derivative majorant

```lean
B n = lambda n * Real.exp (-(lambda n) * τ) * |u0Coeff n| + 2 * S n.
```

If your code uses the diagonal PDE form, prove the identity

```lean
cdot n t = -lambda n * uCoeff n t + F n t
```

as a separate lemma after the derivative formula.

## Continuity of the time derivative

For `DifferentiableAt` at a fixed `(t,x)`, the local majorant above is enough. If the target is a classical solution with `u_t` continuous in `(t,x)`, use the stronger but still natural assumption:

```text
t ↦ F(t) is continuous from compact time intervals into A_0,
```

meaning

```text
∀ t₀∈(0,T), ∀ ε>0, ∃ δ>0,
  |t-t₀|<δ → ∑' n |F_n(t)-F_n(t₀)| < ε.
```

Then

```text
t ↦ (u_n'(t))_n
```

is continuous into `ℓ¹`, and hence

```text
(t,x) ↦ ∑ u_n'(t) cos(nπx)
```

is jointly continuous. Time-`C¹` of the source coefficients is stronger than necessary for `u_t`; source continuity in `A_0` suffices.

## Spatial regularity of `u` from EWA data

For classicality in `x`, the clean package is:

```text
uCoeff(t) ∈ A_2 locally uniformly in t.
```

Then

```text
u(t,x)    = ∑ u_n(t) cos(nπx),
u_x(t,x)  = ∑_{n≥1} -nπ u_n(t) sin(nπx),
u_xx(t,x) = ∑_{n≥1} -λ_n u_n(t) cos(nπx),
```

all converge uniformly in `x`, locally uniformly in `t`. Since your EWA solution already controls weighted-Wiener norms per slice, the missing time bridge is exactly the `A_0` control of `u_t` above.

## Part B: direct spectral resolver data for `v`

Define

```text
v_n(t) := u_n(t)/(μ+λ_n),   μ>0.
```

Then coefficientwise

```text
(μ+λ_n) v_n(t) = u_n(t),
```

which is exactly

```text
μ v - v_xx = u
```

in the cosine basis, with Neumann boundary conditions.

## Weighted-Wiener smoothing estimate

For every `s≥0`, there is a constant `C_{μ,s}` such that

```text
A_{s+2}(v(t)) ≤ C_{μ,s} A_s(u(t)).
```

Indeed,

```text
(1+λ_n)^((s+2)/2) |v_n|
  = (1+λ_n)^((s+2)/2) |u_n|/(μ+λ_n)
  ≤ C_{μ,s} (1+λ_n)^(s/2) |u_n|.
```

For most purposes one can take

```text
C_{μ,s} = sup_n (1+λ_n)/(μ+λ_n) ≤ max(1, 1/μ),
```

independent of `s`, because the extra factor is just `(1+λ_n)/(μ+λ_n)`.

## C² spatial resolver package

A minimal direct spectral data lemma is:

```lean
/-- Direct Neumann resolver spectral data from cosine coefficients. -/
theorem resolver_direct_spectral_data_of_coeffs
    (hμ : 0 < μ)
    {uCoeff : ℕ → ℝ} {vCoeff : ℕ → ℝ}
    (hvCoeff : ∀ n, vCoeff n = uCoeff n / (μ + lambda n))
    (hu_A0 : Summable (fun n => |uCoeff n|)) :
    ResolverSpectralC2Data uCoeff vCoeff := by
  -- 1. v series converges absolutely:
  --    |v_n| ≤ (1/μ)|u_n|.
  -- 2. v_x series converges absolutely:
  --    sqrt(λ_n)|v_n| ≤ Cμ |u_n|.
  -- 3. v_xx series converges absolutely:
  --    λ_n|v_n| ≤ |u_n|.
  -- 4. coefficient equation: (μ+λ_n)v_n=u_n.
  -- 5. Neumann BC: sine derivative vanishes at endpoints.
  sorry
```

The estimates used in that proof are:

```text
|v_n| ≤ μ^{-1}|u_n|,
√λ_n |v_n| = √λ_n |u_n|/(μ+λ_n) ≤ C_μ |u_n|,
λ_n |v_n| = λ_n |u_n|/(μ+λ_n) ≤ |u_n|.
```

For example,

```text
sup_{λ≥0} √λ/(μ+λ) = 1/(2√μ),
```

so one may take `C_μ = 1/(2√μ)` for the first derivative bound.

Thus `u∈A_0` already yields `v∈C²_x`. If `u∈A_s`, then `v∈A_{s+2}`.

## Joint time derivative for the resolver

If `u` has time derivative coefficients `dotU_n(t)` with local `A_0` majorants, define

```text
dotV_n(t) := dotU_n(t)/(μ+λ_n).
```

Then the same smoothing estimates give:

```text
∑ |dotV_n(t)| ≤ μ^{-1} ∑ |dotU_n(t)|,
∑ λ_n |dotV_n(t)| ≤ ∑ |dotU_n(t)|.
```

So if `dotU(t)∈A_0` locally uniformly in time, then `v_t(t)∈C²_x` locally uniformly in time and

```text
∂_t v(t,x) = ∑ dotU_n(t)/(μ+λ_n) cos(nπx).
```

Lean-shaped statement:

```lean
theorem resolver_time_deriv_from_u_time_deriv
    (hμ : 0 < μ)
    (hvCoeff : ∀ n t, vCoeff n t = uCoeff n t / (μ + lambda n))
    (hu_time : ∀ x, HasDerivAt
      (fun t => ∑' n, uCoeff n t * cosBasis n x)
      (∑' n, dotU n t * cosBasis n x) t)
    (hdotU_A0_local : ∃ B : ℕ → ℝ, Summable B ∧
      ∀ n s, s ∈ I → |dotU n s| ≤ B n) :
    ∀ x, HasDerivAt
      (fun t => ∑' n, vCoeff n t * cosBasis n x)
      (∑' n, dotU n t / (μ + lambda n) * cosBasis n x) t :=
by
  -- termwise derivative with majorant B_n / μ.
  sorry
```

For a stronger `C¹_t C²_x` package, require `t↦dotU(t)` continuous into `A_0`; then the resolver time derivative is continuous into `A_2`.

## Positivity of `v`

Spectral summability gives regularity, not positivity. Positivity should be a separate resolver-kernel or maximum-principle lemma.

The correct statements are:

```lean
/-- Nonnegative source gives nonnegative Neumann resolvent. -/
theorem resolver_nonneg_of_nonneg
    (hμ : 0 < μ)
    (hu : ∀ x, 0 ≤ u x)
    (hv : μ • v - secondDeriv v = u)
    (hNeumann : deriv v 0 = 0 ∧ deriv v 1 = 0) :
    ∀ x, 0 ≤ v x := by
  -- maximum principle or positive Green kernel
  sorry

/-- Nontrivial nonnegative source gives strictly positive Neumann resolvent. -/
theorem resolver_pos_of_nonneg_nontrivial
    (hμ : 0 < μ)
    (hu : ∀ x, 0 ≤ u x)
    (hnotzero : ∃ x, 0 < u x) -- or 0 < ∫ u
    (hv : μ • v - secondDeriv v = u)
    (hNeumann : deriv v 0 = 0 ∧ deriv v 1 = 0) :
    ∀ x, 0 < v x := by
  -- strong maximum principle, or v(x)=∫ Gμ(x,y)u(y)dy with Gμ>0
  sorry
```

Kernel form is often the easiest analytically:

```text
v(x)=∫_0^1 G_μ(x,y) u(y) dy,
G_μ(x,y)>0.
```

Then `u≥0` implies `v≥0`, and if `u` is nontrivial, the integral is strictly positive for every `x`.

If `u≡0`, then `v≡0`, so the strict claim `0<v` is false. In the chemotaxis/logistic setting, strict positivity follows for positive times from nontrivial nonnegative data by the strong parabolic maximum principle; but for the resolver lemma itself, include the nontriviality or positive-mass hypothesis.

## Source coefficient decay from weighted Wiener control

The generic pointwise decay lemma is:

```lean
theorem coeff_decay_of_weighted_wiener_bound
    {s B : ℝ} (hB : A_s coeff ≤ B) :
    ∀ n, |coeff n| ≤ B / (1 + lambda n)^(s/2) := by
  -- each nonnegative summand is bounded by the total sum
  sorry
```

Thus:

```text
A_2(coeff)≤B  ⇒  |coeff_n| ≤ B/(1+λ_n),
A_4(coeff)≤B  ⇒  |coeff_n| ≤ B/(1+λ_n)^2.
```

If your `hdecay` means **quadratic decay in the mode index `n`**, then `A_2` is enough because `1+λ_n≈1+n²`:

```text
|coeff_n| ≤ C B/(1+n²).
```

If your `hdecay` means **quadratic decay in the spectral parameter `λ_n`**, then require `A_4`:

```text
|coeff_n| ≤ B/(1+λ_n)^2.
```

State the formal lemma in terms of `(1+λ_n)` so there is no ambiguity.

## Recommended package for `HasResolverDirectSpectralData`

A good formal structure should be split into three independent parts:

```lean
structure HasResolverDirectSpectralData
    (μ : ℝ)
    (uCoeff vCoeff dotUCoeff : ℝ → ℕ → ℝ) : Prop where
  hμ : 0 < μ

  -- coefficient identity
  coeff_eq : ∀ t n, vCoeff t n = uCoeff t n / (μ + lambda n)
  resolvent_coeff_eq : ∀ t n, (μ + lambda n) * vCoeff t n = uCoeff t n

  -- spatial C² at each time, preferably locally uniform in t
  u_A0_loc : ∀ K compact, ∃ B, ∀ t∈K, A_0 (uCoeff t) ≤ B
  v_A2_loc : ∀ K compact, ∃ B, ∀ t∈K, A_2 (vCoeff t) ≤ B

  -- concrete series formulas
  v_series : ∀ t x, v t x = ∑' n, vCoeff t n * cosBasis n x
  vx_series : ∀ t x, deriv (v t) x =
      ∑' n, -sqrt(lambda n) * vCoeff t n * sinBasis n x
  vxx_series : ∀ t x, iteratedDeriv 2 (v t) x =
      ∑' n, -lambda n * vCoeff t n * cosBasis n x

  -- elliptic equation and Neumann boundary
  elliptic_eq : ∀ t x, μ * v t x - iteratedDeriv 2 (v t) x = u t x
  neumann_left : ∀ t, deriv (v t) 0 = 0
  neumann_right : ∀ t, deriv (v t) 1 = 0

  -- time derivative, if needed by classicality
  dotV_series : ∀ t x, deriv (fun s => v s x) t =
      ∑' n, dotUCoeff t n / (μ + lambda n) * cosBasis n x
```

But most of these fields should be theorems derived from the smaller assumptions:

```text
uCoeff ∈ A_0 locally uniformly,
dotUCoeff ∈ A_0 locally uniformly,
vCoeff_n = uCoeff_n/(μ+λ_n).
```

Do not make positivity part of the spectral-data structure unless the structure also carries `u≥0` and nontriviality. Prefer a separate field/lemma:

```lean
Hvpos : (∀ t x, 0 ≤ u t x) → (∀ t, ∃ x, 0 < u t x) → ∀ t x, 0 < v t x.
```

## Minimal assumptions to close (A) and (B)

For `(A) htimeDeriv/hdiffU`, use:

```text
For every compact I=[τ,T₁]⊂(0,T):
  ∃ S∈ℓ¹, ∀n r∈[0,T₁], |F_n(r)|≤S_n,
  ∑ λ_n exp(-λ_n τ)|u0_n| <∞.
```

Then

```text
u_t(t,x)=∑ [ -λ_n u_n(t)+F_n(t) ] cos(nπx)
```

with uniform convergence on `I×[0,1]`.

For `(B) Hv/Hvpos/hdecay`, use:

```text
μ>0,
v_n=u_n/(μ+λ_n),
u(t)∈A_0 locally uniformly,
u_t(t)∈A_0 locally uniformly for the time derivative,
u≥0 and nontrivial for strict positivity,
source∈A_2 or A_4 depending on the intended meaning of quadratic decay.
```

Then the resolver fields are direct and should not be carried as a deep analytic hypothesis. The only genuinely non-spectral part is strict positivity, which should be discharged by the positive kernel / maximum principle lemma.
