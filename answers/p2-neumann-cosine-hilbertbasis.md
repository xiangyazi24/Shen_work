# P2: Neumann cosine Hilbert basis of L2(0,L)

## Executive answer

Mathlib v4.29.1 has the complex exponential Fourier Hilbert basis on the circle:

```lean
import Mathlib.Analysis.Fourier.AddCircle
```

The relevant declaration is:

```lean
fourierBasis
```

This is the Hilbert basis of `Lp C 2 AddCircle.haarAddCircle`, indexed by `Z`, with vectors `fourierLp 2 n`.

Mathlib does not appear to provide a ready-made real Neumann cosine Hilbert basis on an interval, i.e.

```text
{1 / sqrt L} union {sqrt (2 / L) * cos (k*pi*x/L) : k >= 1}
```

as a declaration like `neumannCosineBasis` or `cosineHilbertBasis`. Therefore the clean Lean route is to build the basis locally. There are two honest approaches:

1. Even-reflection route using `fourierBasis` on `AddCircle (2*L)`.
2. Direct route using `HilbertBasis.mk` or `HilbertBasis.mkOfOrthogonalEqBot`, proving orthonormality by trig integrals and completeness by Stone-Weierstrass density.

For this project, the recommended route is:

```text
prove orthonormality directly, prove completeness by even reflection to AddCircle (2L), then build a HilbertBasis by HilbertBasis.mkOfOrthogonalEqBot.
```

This reuses Mathlib's Fourier completeness and keeps the interval-specific work small.

---

## 1. Desired local object

Assume `0 < L`. Define the interval measure and L2 space, preferably using the same endpoint convention throughout the repository:

```lean
abbrev muI (L : R) : Measure R := volume.restrict (Set.Icc (0 : R) L)
abbrev L2I (L : R) := MeasureTheory.Lp R 2 (muI L)
```

The normalized Neumann modes are:

```lean
def neumannCosFun (L : R) : Nat -> R -> R
| 0     => fun _ => (Real.sqrt L)^(-1)
| k + 1 => fun x => Real.sqrt (2 / L) *
    Real.cos (((k + 1 : Nat) : R) * Real.pi * x / L)
```

Lift to `Lp`:

```lean
noncomputable def neumannCosLp (L : R) (k : Nat) : L2I L :=
  MeasureTheory.MemLp.toLp (neumannCosFun L k) 2 (muI L) <proof_of_MemLp>
```

Target:

```lean
noncomputable def neumannCosHilbertBasis (hL : 0 < L) :
    HilbertBasis Nat R (L2I L) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (neumannCos_orthonormal hL)
    (neumannCos_span_orthogonal_eq_bot hL)
```

Useful Hilbert-basis API names:

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
lemma neumannCos_orthonormal (hL : 0 < L) :
  Orthonormal R (neumannCosLp L)
```

The scalar facts are:

```text
int_0^L (1/sqrt L)^2 dx = 1
int_0^L cos(j*pi*x/L) dx = 0 for j >= 1
int_0^L cos(j*pi*x/L) cos(k*pi*x/L) dx = 0 for j != k, j,k >= 1
int_0^L cos(k*pi*x/L)^2 dx = L/2 for k >= 1
```

The product identity is:

```text
2*cos(a*x)*cos(b*x) = cos((a-b)*x) + cos((a+b)*x)
```

and the antiderivative is:

```text
int cos(m*pi*x/L) dx = (L/(m*pi))*sin(m*pi*x/L)
```

Use Mathlib interval integral FTC:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
```

plus standard derivative lemmas:

```lean
HasDerivAt.sin
HasDerivAt.cos
HasDerivAt.const_mul
HasDerivAt.mul_const
HasDerivAt.div_const
```

You may want local helper lemmas:

```lean
lemma integral_cos_nat_pi_div_L
    (hL : 0 < L) (m : Nat) (hm : m != 0) :
    (int x in (0:R)..L, Real.cos ((m:R) * Real.pi * x / L)) = 0
```

and

```lean
lemma integral_cos_mul_cos_nat_pi_div_L
    (hL : 0 < L) (j k : Nat) :
    (int x in (0:R)..L,
      Real.cos ((j:R)*Real.pi*x/L) * Real.cos ((k:R)*Real.pi*x/L))
      = if j = 0 then ... else if j = k then L/2 else 0
```

The exact endpoint trigonometric simplifications use the usual `sin (n*pi) = 0` lemmas in Mathlib's real trig API. If the exact declaration name is inconvenient in your branch, isolate it in a local lemma:

```lean
lemma sin_nat_mul_pi_zero (n : Nat) : Real.sin ((n:R) * Real.pi) = 0
```

---

## 3. Completeness by even reflection to AddCircle

This is the recommended completeness proof.

### Idea

Suppose `f : L2I L` is orthogonal to every Neumann cosine mode. Build the even extension of `f` to the period `2*L` circle:

```text
F(x) = f(abs x) on [-L,L]
```

viewed as an element of `Lp C 2 AddCircle.haarAddCircle` after complexification.

For every integer mode n, the Fourier coefficient of F is the cosine coefficient of f. The sine part cancels by evenness. Therefore all Fourier coefficients of F vanish. Mathlib's circle Fourier Parseval/completeness theorem then gives F = 0 in L2 on the circle. Restricting to `(0,L)` gives f = 0. Thus the orthogonal complement of the cosine span is zero.

### Lean statement

```lean
lemma neumannCos_span_orthogonal_eq_bot (hL : 0 < L) :
  (Submodule.span R (Set.range (neumannCosLp L))).orthogonal = bot
```

Then:

```lean
noncomputable def neumannCosHilbertBasis (hL : 0 < L) :
    HilbertBasis Nat R (L2I L) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (neumannCos_orthonormal hL)
    (neumannCos_span_orthogonal_eq_bot hL)
```

### Mathlib Fourier declarations

Use:

```lean
import Mathlib.Analysis.Fourier.AddCircle
```

Relevant names:

```lean
fourierBasis
fourierLp
orthonormal_fourier
hasSum_fourier_series_L2
fourierCoeffOn
fourierCoeffOn_eq_integral
fourierCoeff_liftIoc_eq
fourierCoeff_liftIco_eq
tsum_sq_fourierCoeffOn
hasSum_sq_fourierCoeffOn
span_fourierLp_closure_eq_top
```

A key local lemma is:

```lean
lemma fourierCoeff_evenExtension_eq_cosCoeff
    (hL : 0 < L) (f : L2I L) (n : Z) :
    fourierCoeffOn <interval_of_length_2L> (evenExtension f) n
      = <normalization> *
        int x in (0:R)..L,
          (fRep x : C) * (Real.cos ((n:R) * Real.pi * x / L) : R)
```

The normalization depends on Mathlib's `fourierCoeffOn` convention and the chosen interval of length `2*L`. Prove this once and hide it behind a theorem.

After this lemma, orthogonality of f to all cosines implies all circle Fourier coefficients of `evenExtension f` vanish. Then `tsum_sq_fourierCoeffOn` or `hasSum_sq_fourierCoeffOn` gives zero L2 norm for the even extension.

### Isometry note

The even extension map is an isometry up to the factor `sqrt 2`:

```text
norm_L2(-L,L)^2 of evenExtension(f) = 2 * norm_L2(0,L)^2 of f.
```

If you use an explicitly normalized map

```text
E f = (1/sqrt 2) * evenExtension(f)
```

then E is an isometry from `L2(0,L)` into the even subspace of `L2(AddCircle (2L))`. You do not need to formalize a full `LinearIsometryEquiv` unless you want to transport the Hilbert basis abstractly. For the completeness proof, the norm identity plus Parseval is enough.

---

## 4. Direct Stone-Weierstrass route

The direct route is also sound:

1. Prove orthonormality by trig integrals.
2. Prove the algebra generated by `x |-> cos(pi*x/L)` is dense in `C([0,L],R)`.
3. Use density of continuous functions in L2.
4. Conclude the closed span of the cosine modes is all of L2.

Relevant imports/declarations:

```lean
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense
```

The AddCircle Fourier file itself uses and exposes analogous density results:

```lean
fourierSubalgebra
fourierSubalgebra_separatesPoints
fourierSubalgebra_closure_eq_top
span_fourier_closure_eq_top
span_fourierLp_closure_eq_top
```

For the interval, you would need to show `x |-> cos(pi*x/L)` separates points on `[0,L]`, because it is strictly decreasing there. This route is real-only but requires more Stone-Weierstrass infrastructure. The even-reflection route is usually cleaner for this project.

---

## 5. Coefficient formula

With normalized basis:

```text
e_0(x) = 1/sqrt L
e_k(x) = sqrt(2/L) * cos(k*pi*x/L), k >= 1
```

Mathlib's coordinate is:

```lean
cosBasis.repr u k
```

and by `HilbertBasis.repr_apply_apply`, it is the inner product against the basis vector, up to the inner product convention:

```lean
cosBasis.repr u k = <cosBasis k, u>
```

Therefore, for representatives:

```text
cosBasis.repr u 0 = (1/sqrt L) * int_0^L u(x) dx
```

and for k >= 1:

```text
cosBasis.repr u k = sqrt(2/L) * int_0^L u(x) cos(k*pi*x/L) dx
```

if the inner product is linear in the second variable as in Mathlib's convention for real Hilbert spaces. If a rewrite produces the inner product in the opposite order, use symmetry of the real inner product.

Recommended local lemmas:

```lean
lemma cosBasis_repr_zero_eq_integral
    (u : L2I L) :
    cosBasis.repr u 0 = (Real.sqrt L)^(-1) * int x in (0:R)..L, uRep x
```

```lean
lemma cosBasis_repr_succ_eq_integral
    (u : L2I L) (k : Nat) :
    cosBasis.repr u (k+1)
      = Real.sqrt (2/L) *
        int x in (0:R)..L, uRep x * Real.cos (((k+1:Nat):R)*Real.pi*x/L)
```

These are just `HilbertBasis.repr_apply_apply` plus the definition of the lifted basis vector.

---

## 6. Reconstruction for every L2 function

Once the basis is built, Mathlib gives for every `u : L2I L`:

```lean
have hsum :
  HasSum
    (fun k => (cosBasis.repr u k) • cosBasis k)
    u :=
  cosBasis.hasSum_repr u
```

This is the load-bearing theorem. It needs no H1 regularity and no PDE input. It is pure Hilbert-space completeness.

Parseval is obtained by:

```lean
HilbertBasis.tsum_inner_mul_inner
```

or related lemmas:

```lean
HilbertBasis.summable_inner_mul_inner
HilbertBasis.hasSum_inner_mul_inner
```

---

## 7. No ready Neumann basis found

The ready basis in Mathlib is the complex circle basis:

```lean
fourierBasis
```

from

```lean
Mathlib.Analysis.Fourier.AddCircle
```

I do not know of a Mathlib v4.29.1 declaration providing the real Neumann cosine basis on `L2(0,L)` directly. Searches to try in a local checkout:

```bash
rg "fourierBasis" Mathlib/Analysis/Fourier
rg "HilbertBasis" Mathlib/Analysis/Fourier
rg "orthonormal.*cos|cos.*orthonormal" Mathlib
rg "Neumann" Mathlib
rg "cosine" Mathlib
```

Expected result: `fourierBasis` exists on `AddCircle`; no interval Neumann cosine `HilbertBasis` exists as a ready declaration.

---

## 8. Recommended implementation package

Create a local spectral bank:

```lean
structure NeumannCosineBasisData (L : R) (hL : 0 < L) where
  L2I : Type
  muI : Measure R
  cosBasis : HilbertBasis Nat R L2I
  repr_zero_eq_integral : ...
  repr_succ_eq_integral : ...
  hasSum_repr : forall u : L2I,
    HasSum (fun k => (cosBasis.repr u k) • cosBasis k) u
  parseval : ...
```

Downstream proofs should consume only this interface. They should not depend on whether completeness was proved by even reflection or Stone-Weierstrass.

---

## Final recommendation

Build the Neumann cosine `HilbertBasis` locally.

Use direct trig integrals for orthonormality. Use even reflection into `AddCircle (2*L)` and Mathlib's `fourierBasis` / `tsum_sq_fourierCoeffOn` for completeness. Then expose only the local `HilbertBasis` and coordinate formulas to the boundedness proof.

The main downstream theorem then becomes immediate:

```lean
cosBasis.hasSum_repr u
```

for every `u : L2(0,L)`, giving the cosine expansion in L2 without any H1 regularity or PDE argument.
