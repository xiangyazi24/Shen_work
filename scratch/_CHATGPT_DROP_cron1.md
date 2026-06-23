# ChatGPT git-drop (cron1)

## Q72 — Per-mode mild/Duhamel identity: deep representation theorem or Fubini?

### Executive verdict

If you already have the **spatial mild identity** for each `t > 0` as an equality in a function space on `[0,1]` where the cosine-coefficient functional is bounded linear, then the per-mode identity is **not** a new parabolic representation theorem.

It is exactly:

1. apply the bounded linear functional

```text
L_k(f) = cosineCoeffs f k = c_k ∫_0^1 cos(kπx) f(x) dx,
```

2. use linearity of `L_k`,
3. commute `L_k` through the Bochner/interval time integrals by `ContinuousLinearMap.integral_comp_comm`, equivalently scalar Fubini,
4. use the already-known spectral action of the heat semigroup on cosine modes for the initial heat term.

So the carried seam

```lean
cosineCoeffs (∫ time, spatialIntegrand time) k
  = ∫ time, cosineCoeffs (spatialIntegrand time) k
```

is trivial once the mild integral is a legitimate Bochner integral and the coefficient functional is available as a continuous linear map. The diagonal convention `S(0)=0` is harmless because it changes the time integrand on a null set.

The only genuinely nontrivial things that could still be hiding under the name “parabolic representation theorem” are **not** the Fubini/per-mode passage itself. They are:

- proving the spatial mild identity in the right Banach/function space;
- proving the time integrands are Bochner integrable / strongly measurable;
- proving the heat or gradient kernels have the claimed spectral action, e.g. `cosineCoeffs (S(t) f) k = exp(-t λ_k) cosineCoeffs f k`, or the corresponding `B = ∂x S` mode formula;
- handling an a.e.-in-space equality if your mild identity is only an `Lᵖ` equality rather than a continuous-function equality.

But if those pieces are already landed, the per-mode Duhamel identity is immediate.

---

## Precise mathematical statement

Let `X` be a Banach space of spatial functions on `[0,1]`, for example `C([0,1], ℝ)` or a bundled interval-domain continuous-function type. For each `k`, define

```text
L_k : X →L[ℝ] ℝ,
L_k(f) = c_k ∫_0^1 cos(kπx) f(x) dx.
```

For `C([0,1], ℝ)`, boundedness is elementary:

```text
|L_k(f)| ≤ c_k ∫_0^1 |f(x)| dx ≤ c_k ‖f‖∞.
```

Suppose the spatial mild identity is

```text
u(τ)
  = S(τ) u₀
    + (-χ₀) • ∫ s in 0..τ, B(τ-s) (chemFlux (u s))
    +        ∫ s in 0..τ, S(τ-s) (logistic (u s))
```

as an equality in `X`, and suppose the two time integrands are integrable as `X`-valued functions:

```lean
hchem_int : Integrable (fun s => B (τ-s) (chemFlux (u s))) μτ
hlog_int  : Integrable (fun s => S (τ-s) (logistic (u s))) μτ
```

where `μτ` is the restricted Lebesgue measure corresponding to the interval integral `0..τ`.

Then applying `L_k` gives

```text
L_k(u(τ))
  = L_k(S(τ)u₀)
    + (-χ₀) * L_k(∫ s, B(τ-s)(chemFlux(u s)))
    +          L_k(∫ s, S(τ-s)(logistic(u s))).
```

The integral terms commute:

```text
L_k(∫ s, B(τ-s)(chemFlux(u s)))
  = ∫ s, L_k(B(τ-s)(chemFlux(u s))),

L_k(∫ s, S(τ-s)(logistic(u s)))
  = ∫ s, L_k(S(τ-s)(logistic(u s))).
```

The heat initial term is then reduced by the semigroup spectral identity:

```text
L_k(S(τ)u₀) = exp(-τ λ_k) L_k(u₀).
```

Thus

```text
ĉ_k(u(τ))
  = exp(-τ λ_k) û₀_k
    + (-χ₀) ∫_0^τ ĉ_k(B(τ-s)(chemFlux(u(s)))) ds
    +        ∫_0^τ ĉ_k(S(τ-s)(logistic(u(s)))) ds.
```

This is precisely the desired per-mode mild identity.

---

## Lean / Mathlib lemma chain: continuous-linear-map route

This is the cleanest formalization if your Duhamel integrals are already Bochner integrals into a Banach space of spatial functions.

### 1. Bundle the coefficient as a continuous linear map

Define or prove a lemma exposing:

```lean
cosCoeffCLM (k : ℕ) : X →L[ℝ] ℝ
```

with

```lean
cosCoeffCLM_apply : cosCoeffCLM k f = cosineCoeffs f k
```

For continuous functions on `[0,1]`, this is just the integral functional against the bounded continuous test function `cos(kπx)`. The proof is the sup-norm bound:

```text
|∫_0^1 cos(kπx) f(x) dx| ≤ ∫_0^1 |f(x)| dx ≤ ‖f‖∞.
```

If your existing `cosineCoeffs` is defined on raw `ℝ → ℝ`, you can either wrap slices as continuous maps, or prove a bespoke lemma:

```lean
cosineCoeffs_integral_comm
```

from Fubini. The `ContinuousLinearMap` route is cleaner once the spatial mild identity is already in a function space.

### 2. Apply the coefficient functional to the spatial mild identity

Given

```lean
h_mild_spatial :
  u τ = S τ u₀
    + (-χ₀) • (∫ s in 0..τ, B (τ-s) (chemFlux (u s)))
    +        (∫ s in 0..τ, S (τ-s) (logistic (u s)))
```

use, schematically:

```lean
have hmode := congrArg (fun f => cosCoeffCLM k f) h_mild_spatial
```

Then simplify by linearity:

```lean
simp [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] at hmode
```

or just `simp` if the coercions are arranged.

### 3. Commute the functional through the time integrals

Mathlib theorem:

```lean
ContinuousLinearMap.integral_comp_comm
```

has the essential shape:

```lean
(L : E →L[𝕜] F) → Integrable φ μ →
  ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
```

So in the direction you usually want:

```lean
have hchem_comm :
    cosCoeffCLM k (∫ s, B (τ-s) (chemFlux (u s)) ∂μτ)
      = ∫ s, cosCoeffCLM k (B (τ-s) (chemFlux (u s))) ∂μτ := by
  simpa using ((cosCoeffCLM k).integral_comp_comm hchem_int).symm

have hlog_comm :
    cosCoeffCLM k (∫ s, S (τ-s) (logistic (u s)) ∂μτ)
      = ∫ s, cosCoeffCLM k (S (τ-s) (logistic (u s))) ∂μτ := by
  simpa using ((cosCoeffCLM k).integral_comp_comm hlog_int).symm
```

For interval integrals, either phrase the Duhamel integral as a set integral over `volume.restrict (Set.uIoc 0 τ)`, or convert using:

```lean
intervalIntegral.integral_of_le hτ_nonneg
```

when `0 ≤ τ`. In practice the pattern is:

```lean
rw [intervalIntegral.integral_of_le hτ_nonneg]
exact ((cosCoeffCLM k).integral_comp_comm hchem_int).symm
```

where `hchem_int` is stated for the restricted measure on `Set.Ioc 0 τ`.

### 4. Rewrite the heat term spectrally

You still need the standard heat-mode lemma:

```lean
cosineCoeffs_heatSemigroup
  : cosineCoeffs (S τ u₀) k = Real.exp (-(τ * lam k)) * cosineCoeffs u₀ k
```

or whatever name exists in the repo.

This is not Fubini; it is the spectral diagonalization of `S(t)`. But it is a basic heat-kernel/eigenfunction identity. If this lemma is already available, the per-mode initial term is done.

### 5. Final shape

The final theorem should look like:

```lean
theorem perMode_mild_of_spatial_mild
    (hτ : 0 ≤ τ)
    (h_mild_spatial : spatial mild identity at τ)
    (hchem_int : Integrable (fun s => B (τ-s) (chemFlux (u s))) μτ)
    (hlog_int  : Integrable (fun s => S (τ-s) (logistic (u s))) μτ)
    (hheat_mode : cosineCoeffs (S τ u₀) k = Real.exp (-(τ * lam k)) * cosineCoeffs u₀ k) :
    cosineCoeffs (u τ) k
      = Real.exp (-(τ * lam k)) * cosineCoeffs u₀ k
        + (-χ₀) * (∫ s in 0..τ,
            cosineCoeffs (B (τ-s) (chemFlux (u s))) k)
        + (∫ s in 0..τ,
            cosineCoeffs (S (τ-s) (logistic (u s))) k) := by
  -- apply `cosCoeffCLM k` to `h_mild_spatial`
  -- rewrite by `map_add`, `map_smul`
  -- use `ContinuousLinearMap.integral_comp_comm` for both integrals
  -- use `hheat_mode`
  -- ring/simp
```

This is a small lemma, not a deep representation theorem.

---

## Scalar Fubini route, if you do not want to bundle `cosCoeffCLM`

If the mild identity is pointwise in `x` and your spatial integral is represented as a raw function

```lean
fun x => ∫ s in 0..τ, H s x
```

then unfold `cosineCoeffs` and use scalar Fubini.

For fixed `k`, define

```lean
def K (x s : ℝ) : ℝ :=
  Real.cos ((k:ℝ) * Real.pi * x) * H s x
```

Prove

```lean
hK_int : IntegrableOn K.uncurry (Set.uIoc 0 1 ×ˢ Set.uIoc 0 τ)
```

Then Mathlib has:

```lean
MeasureTheory.intervalIntegral_intervalIntegral_swap
```

with shape:

```lean
∫ x in a..b, ∫ y in c..d, F x y
  = ∫ y in c..d, ∫ x in a..b, F x y
```

from an `IntegrableOn F.uncurry (Set.uIoc a b ×ˢ Set.uIoc c d)` hypothesis.

The proof skeleton is:

```lean
have hswap :
  (∫ x in (0:ℝ)..1, ∫ s in (0:ℝ)..τ,
      Real.cos ((k:ℝ) * Real.pi * x) * H s x)
    =
  (∫ s in (0:ℝ)..τ, ∫ x in (0:ℝ)..1,
      Real.cos ((k:ℝ) * Real.pi * x) * H s x) := by
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap hK_int
```

Then fold the spatial integral back into `cosineCoeffs (H s) k` using the coefficient definition.

The relevant Mathlib Fubini lemmas are:

```lean
MeasureTheory.integral_prod
MeasureTheory.integral_prod_symm
MeasureTheory.integral_integral
MeasureTheory.integral_integral_swap
MeasureTheory.intervalIntegral_integral_swap
MeasureTheory.intervalIntegral_intervalIntegral_swap
```

For integrability from boundedness on a finite rectangle, the useful lemma is:

```lean
MeasureTheory.IntegrableOn.of_bound
```

It asks for:

```lean
hs   : volume rectangle < ∞
hasm : AEStronglyMeasurable K (volume.restrict rectangle)
hbd  : ∀ᵐ z ∂volume.restrict rectangle, ‖K z‖ ≤ C
```

In this application:

```text
|K(x,s)| ≤ |H(s,x)| ≤ ‖f(s)‖∞ ≤ C_f,
```

because `|cos| ≤ 1` and the Neumann heat semigroup is sup-norm contractive. The rectangle has finite measure.

---

## The diagonal `s = τ`

The convention

```text
S(0) f = 0
```

while

```text
lim_{s → τ-} S(τ-s) f(s) = f(τ)
```

does **not** obstruct the coefficient/time-integral swap.

For fixed `τ`, the bad time set is the singleton `{τ}`. The interval integral over `0..τ` uses Lebesgue measure, and singletons have measure zero. Therefore any two versions of the integrand that differ only at `s = τ` are a.e. equal, and Bochner/scalar integrals agree.

In Lean, use one of:

```lean
integral_congr_ae
MeasureTheory.IntegrableOn.congr_fun_ae
MeasureTheory.integrableOn_congr_fun_ae
```

after proving the two versions are equal a.e. on the restricted interval measure. The product version is the same: `{τ} × [0,1]` has product measure zero.

Thus the diagonal jump is just a measurability/integrability bookkeeping issue, not a representation-theorem issue.

---

## What exactly could still be genuinely deep?

The phrase “parabolic representation theorem” may refer to something stronger than the Fubini step. Here is the precise separation.

### Trivial-given-Fubini

The following is not deep:

```text
cosineCoeffs (∫ time, spatialIntegrand time) k
  = ∫ time, cosineCoeffs (spatialIntegrand time) k.
```

This is just bounded linear maps commuting with Bochner integrals.

### Potentially nontrivial but separate

The following may be real lemmas, but they are separate from the per-mode passage:

1. **Spatial mild identity.** If the fixed-point construction gives only an abstract fixed point, proving it satisfies the displayed spatial Duhamel identity in the desired function space may require work.

2. **Bochner integrability.** You must know that

```lean
fun s => B (τ-s) (chemFlux (u s))
fun s => S (τ-s) (logistic (u s))
```

are integrable into the chosen spatial Banach space, or prove scalar integrability after unfolding.

3. **Spectral action of kernels.** To replace

```text
cosineCoeffs (S(τ)u₀) k
```

by

```text
exp(-τλ_k) û₀_k
```

requires the heat semigroup cosine-mode identity. To rewrite the `B = ∂xS` term into a specific closed-form Duhamel coefficient may require the corresponding gradient-kernel spectral identity. That is not the same as the Fubini step.

4. **Equality level.** If the spatial mild identity is only a.e. in `x`, then applying a coefficient functional is still fine, but the theorem statement should be phrased in an `L¹`/`L²` compatible way and use `integral_congr_ae`.

If your collaborators' “parabolic representation theorem” means one of these stronger items, then name that item explicitly. But the per-mode Duhamel identity as written is not itself that theorem.

---

## Final answer

Yes: given the spatial mild identity and the needed integrability, the per-mode identity follows immediately by applying the bounded cosine-coefficient functional and commuting it through the time integral. No additional regularity theorem is needed for that passage.

The correct formal seam to discharge is therefore small:

```lean
cosCoeffCLM_integral_comm
```

or, more directly,

```lean
perMode_mild_of_spatial_mild
```

proved by:

```lean
congrArg (fun f => cosCoeffCLM k f) h_mild_spatial
ContinuousLinearMap.integral_comp_comm
map_add / map_smul
heat_semigroup_cosineCoeff
```

If anything remains genuinely hard, it is not “coefficient of time integral equals time integral of coefficient”; it is the prior spatial mild identity, Bochner integrability, or spectral kernel identities for `S`/`B`.
