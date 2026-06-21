# P2: Neumann cosine `HilbertBasis` and H¹/AC representative

## Executive answer

Mathlib v4.29.1 has the **complex exponential Fourier Hilbert basis on the circle**. Import:

```lean
import Mathlib.Analysis.Fourier.AddCircle
```

The key declaration is:

```lean
fourierBasis
```

It is the Hilbert basis of `Lp ℂ 2 AddCircle.haarAddCircle`, indexed by `ℤ`, with basis vectors given by `fourierLp 2 n`. Relevant declarations in the same file include:

```lean
fourier
fourierLp
orthonormal_fourier
fourierBasis
coe_fourierBasis
fourierBasis_repr
hasSum_fourier_series_L2
hasSum_sq_fourierCoeff
tsum_sq_fourierCoeff
hasSum_sq_fourierCoeffOn
tsum_sq_fourierCoeffOn
fourierCoeffOn
fourierCoeffOn_eq_integral
fourierCoeff_liftIoc_eq
fourierCoeff_liftIco_eq
span_fourier_closure_eq_top
span_fourierLp_closure_eq_top
```

Mathlib does **not** appear to provide a ready-made real Neumann cosine basis

\[
\{1\}\cup\{\sqrt2\cos(k\pi x):k\ge1\}
\]

as a `HilbertBasis` of real `L²(0,1)`. The direct object should be built locally, using the circle Fourier basis for completeness.

---

## 1. Local cosine basis to construct

Use a local real interval `L²` type, for example

```lean
abbrev μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
abbrev L2I := MeasureTheory.Lp ℝ 2 μI
```

Define normalized representatives:

```lean
def cosNeumannFun : ℕ → ℝ → ℝ
| 0     => fun _ => 1
| n + 1 => fun x => Real.sqrt 2 * Real.cos (((n + 1 : ℕ) : ℝ) * Real.pi * x)
```

Lift these to `L2I` as `cosNeumannLp : ℕ → L2I`. The target is:

```lean
noncomputable def cosNeumannHilbertBasis : HilbertBasis ℕ ℝ L2I :=
  HilbertBasis.mkOfOrthogonalEqBot
    cosNeumann_orthonormal
    cosNeumann_span_orthogonal_eq_bot
```

or `HilbertBasis.mk` if you prove dense span directly.

Important Hilbert-basis API names:

```lean
HilbertBasis.mk
HilbertBasis.mkOfOrthogonalEqBot
HilbertBasis.hasSum_repr
HilbertBasis.repr_apply_apply
HilbertBasis.tsum_inner_mul_inner
HilbertBasis.summable_inner_mul_inner
HilbertBasis.hasSum_inner_mul_inner
```

---

## 2. Orthonormality

Prove:

```lean
lemma cosNeumann_orthonormal : Orthonormal ℝ cosNeumannLp
```

The needed scalar interval integrals are:

\[
\int_0^1 1\,dx=1,
\]

\[
\int_0^1\cos(j\pi x)\cos(k\pi x)\,dx=0\quad(j\ne k),
\]

\[
\int_0^1\cos(k\pi x)^2\,dx=\frac12\quad(k\ge1).
\]

Lean route: use product-to-sum and integrate `cos (m*pi*x)` over `[0,1]`. The useful interval FTC lemma is:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
```

with antiderivative `sin (m*pi*x)/(m*pi)` for nonzero `m`.

---

## 3. Completeness: even reflection to `AddCircle 2`

This is the hard part. Prove:

```lean
lemma cosNeumann_span_orthogonal_eq_bot :
  (Submodule.span ℝ (Set.range cosNeumannLp)).orthogonal = ⊥
```

Proof skeleton:

1. Let `f : L2I` be orthogonal to every cosine mode.
2. Build its even period-2 extension `F : AddCircle 2 → ℂ`, morally `F(x)=f(|x|)` on `[-1,1]`.
3. Show every complex Fourier coefficient of `F` vanishes. For `n : ℤ`, use `fourierCoeffOn_eq_integral` and evenness to reduce
   \[
   \widehat F(n)=0
   \]
   to orthogonality of `f` against `cos(n*pi*x)` on `(0,1)`. The sine part cancels by evenness.
4. Apply Parseval/completeness on the circle via

```lean
tsum_sq_fourierCoeffOn
-- or
hasSum_sq_fourierCoeffOn
```

5. Conclude `F = 0` a.e.; restrict back to `(0,1)` to get `f = 0` a.e.

Useful declarations for this route:

```lean
fourierCoeffOn_eq_integral
fourierCoeff_liftIoc_eq
fourierCoeff_liftIco_eq
tsum_sq_fourierCoeffOn
hasSum_sq_fourierCoeffOn
hasSum_fourier_series_L2
span_fourierLp_closure_eq_top
```

This is preferable to proving a new Stone-Weierstrass density theorem on `[0,1]`.

Alternative route: Stone-Weierstrass. Imports/declarations include:

```lean
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense

fourierSubalgebra
fourierSubalgebra_separatesPoints
fourierSubalgebra_closure_eq_top
span_fourier_closure_eq_top
span_fourierLp_closure_eq_top
```

But the even-reflection route reuses more existing Fourier-series machinery.

---

## 4. Cosine reconstruction: `S_N → u` in `L²`

Once `cosNeumannHilbertBasis` exists, the coefficient is:

```lean
noncomputable def c (u : L2I) (k : ℕ) : ℝ :=
  cosNeumannHilbertBasis.repr u k
```

The reconstruction is:

```lean
have hrepr :
  HasSum
    (fun k : ℕ => (cosNeumannHilbertBasis.repr u k) • cosNeumannHilbertBasis k)
    u :=
  cosNeumannHilbertBasis.hasSum_repr u
```

Then finite partial sums converge by the usual `HasSum` API, e.g. `HasSum.tendsto_sum_nat` or the finite-set version already used in the project.

Parseval uses:

```lean
HilbertBasis.tsum_inner_mul_inner
```

and the coefficient-inner-product identification uses:

```lean
HilbertBasis.repr_apply_apply
```

---

## 5. Derivative sine series: `T_N → g` in `L²`

Define normalized sine modes for positive modes:

```lean
def sinDirichletFun (k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (((k + 1 : ℕ) : ℝ) * Real.pi * x)
```

Lift to `L2I` as `sinDirichletLp`. Prove only:

```lean
lemma sinDirichlet_orthonormal : Orthonormal ℝ sinDirichletLp
```

Sine completeness is not needed. Weighted `ℓ²` gives convergence of the derivative series because finite differences have norm equal to the tail of

\[
\sum_{k\ge1}(k\pi)^2c_k^2.
\]

The target lemma is:

```lean
lemma sine_series_L2_converges_of_weighted_l2
    (hweight : Summable fun k : ℕ =>
      ((((k+1 : ℕ) : ℝ) * Real.pi)^2) * (c (k+1))^2) :
    ∃ g : L2I, Tendsto (fun N => T N) atTop (𝓝 g)
```

where

\[
T_N=-\sum_{1\le k\le N} k\pi c_k\sqrt2\sin(k\pi x).
\]

---

## 6. Finite partial-sum IBP

For partial sums

\[
S_N=c_0+\sum_{1\le k\le N}c_k\sqrt2\cos(k\pi x),
\]

\[
T_N=-\sum_{1\le k\le N}k\pi c_k\sqrt2\sin(k\pi x),
\]

prove for zero-trace or compact-support `C¹` tests:

```lean
lemma partial_sum_ibp
    (N : ℕ) (φ : ℝ → ℝ)
    (hφ : TestC1ZeroTrace01 φ) :
    ∫ x in (0 : ℝ)..1, S N x * deriv φ x
      = - ∫ x in (0 : ℝ)..1, T N x * φ x
```

Use:

```lean
intervalIntegral.integral_mul_deriv_eq_deriv_mul
```

or the explicit hypothesis variant:

```lean
intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
```

The boundary term vanishes because `φ 0 = 0` and `φ 1 = 0`.

---

## 7. Pass to the `L²` limit: weak derivative

Define:

```lean
def HasWeakDeriv01 (u g : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ,
    TestC1ZeroTrace01 φ →
      ∫ x in (0 : ℝ)..1, u x * deriv φ x
        = - ∫ x in (0 : ℝ)..1, g x * φ x
```

Use the pairing-continuity lemma:

```lean
lemma L2_pairing_tendsto
    {hN : ℕ → ℝ → ℝ} {h ψ : ℝ → ℝ}
    (hL2 : Tendsto
      (fun N => eLpNorm (fun x => hN N x - h x) 2 μI)
      atTop (𝓝 0))
    (hψ : MemLp ψ 2 μI) :
    Tendsto
      (fun N => ∫ x in (0 : ℝ)..1, hN N x * ψ x)
      atTop
      (𝓝 (∫ x in (0 : ℝ)..1, h x * ψ x))
```

This is just Cauchy-Schwarz:

\[
\left|\int(h_N-h)\psi\right|\le\|h_N-h\|_2\|\psi\|_2.
\]

Useful Mathlib estimates include:

```lean
MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
MeasureTheory.norm_integral_le_integral_norm
MeasureTheory.abs_integral_le_integral_abs
```

Then:

```lean
lemma HasWeakDeriv01.of_L2_limits
    (hS_L2 : Tendsto (fun N => toLp2 (S N)) atTop (𝓝 (toLp2 u)))
    (hT_L2 : Tendsto (fun N => toLp2 (T N)) atTop (𝓝 (toLp2 g)))
    (hIBP : ∀ N φ, TestC1ZeroTrace01 φ →
      ∫ x in (0 : ℝ)..1, S N x * deriv φ x
        = - ∫ x in (0 : ℝ)..1, T N x * φ x) :
    HasWeakDeriv01 u g
```

This avoids differentiating the infinite series pointwise.

---

## 8. AC representative

Since `g ∈ L²`, also `g ∈ L¹` on a finite interval. Define:

```lean
def H (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, g y

def A : ℝ :=
  (∫ x in (0 : ℝ)..1, u x) - (∫ x in (0 : ℝ)..1, H x)

def U (x : ℝ) : ℝ := A + H x
```

Do **not** use `u 0`; `u` is only an `L²` representative.

For AC, use:

```lean
IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
```

Then add the constant using:

```lean
AbsolutelyContinuousOnInterval.add
AbsolutelyContinuousOnInterval.fun_add
ContDiffOn.absolutelyContinuousOnInterval
```

To prove `U =ᵐ u`, use uniqueness of the `L²` limit. Build partial primitives:

\[
H_N(x)=\int_0^x T_N,
\quad
A_N=\int_0^1S_N-\int_0^1H_N,
\quad
U_N=A_N+H_N.
\]

Finite FTC gives `U_N = S_N`. Since `T_N → g` in `L²`, also `T_N → g` in `L¹`, hence `H_N → H` uniformly:

\[
\sup_x |H_N(x)-H(x)|\le\int_0^1|T_N-g|.
\]

Then `A_N → A`, so `S_N = U_N → U` in `L²`. Since also `S_N → u` in `L²`, conclude `U =ᵐ u` using:

```lean
MeasureTheory.MemLp.toLp_eq_toLp_iff
```

---

## 9. Final theorem shape

A clean theorem is:

```lean
theorem weighted_cosine_coeffs_to_intervalH1Weak
    (B : NeumannCosineSpectralBank)
    (u : L2I)
    (hweight : Summable fun k : ℕ =>
      ((((k+1 : ℕ) : ℝ) * Real.pi)^2) *
        (B.coeff u (k+1))^2) :
    ∃ U g : ℝ → ℝ,
      U =ᵐ[μI] B.rep u ∧
      AbsolutelyContinuousOnInterval U 0 1 ∧
      HasWeakDeriv01 U g
```

where `NeumannCosineSpectralBank` contains the locally built cosine Hilbert basis and sine orthonormal family.

---

## Final implementation summary

Mathlib provides the circle Fourier Hilbert basis:

```lean
Mathlib.Analysis.Fourier.AddCircle.fourierBasis
```

but not a ready-made real Neumann cosine Hilbert basis on `L²(0,1)`. The minimal self-contained construction is:

1. define `1, sqrt 2 * cos(k*pi*x)` as `Lp` functions;
2. prove orthonormality by interval trig integrals;
3. prove completeness by even reflection to `AddCircle 2` and `tsum_sq_fourierCoeffOn` / `fourierBasis` completeness;
4. construct `HilbertBasis ℕ ℝ L2I` using `HilbertBasis.mkOfOrthogonalEqBot`;
5. use `HilbertBasis.hasSum_repr` for cosine reconstruction;
6. use sine orthonormality plus weighted `ℓ²` for the derivative series;
7. prove finite IBP with `intervalIntegral.integral_mul_deriv_eq_deriv_mul`;
8. pass to the `L²` limit for `HasWeakDeriv01`;
9. define `U=A+∫g`, prove AC by `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`, and prove `U=ᵐu` by `MeasureTheory.MemLp.toLp_eq_toLp_iff`.
