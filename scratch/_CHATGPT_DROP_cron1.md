# Q2800 (cron1) — 1D Moser iteration and the natural Agmon gradient

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Executive answer

There are two separate issues here.

1. **The desired linear `RelativeMoserInterpolationBefore` inequality is false as stated** if `rho > 0` and the constant is required to be independent of the function:

   ```text
   ∫ u^(p+rho) ≤ eps * ∫ |∇(u^(p/2))|² + Ceps * ∫ u^p.
   ```

   Constant functions already disprove it.  On `[0,1]`, take `u ≡ K > 0`.  Then the gradient term is zero and the inequality becomes

   ```text
   K^(p+rho) ≤ Ceps * K^p,
   ```

   i.e.

   ```text
   K^rho ≤ Ceps,
   ```

   for all `K`, impossible when `rho > 0`.

2. **There is a standard 1D way to run the iteration without an a priori `L∞` bound**, but the interpolation term is not linear in `∫u^p`.  One uses the natural diffusion variable

   ```text
   g = u^(p/2)
   ```

   and a 1D Gagliardo--Nirenberg/Sobolev estimate for `g`.  This gives a valid inequality of the form

   ```text
   ∫ u^(p+rho)
     ≤ eps * ∫ |∇(u^(p/2))|²
       + Ceps,p,rho * (∫ u^p)^gamma
       + lower-order terms,
   ```

   where `gamma > 1`, for example one convenient exponent is

   ```text
   gamma = (2*p + rho) / (2*p - rho)
   ```

   assuming `2*p > rho`.  A simpler but slightly weaker derivation from `H¹ -> L∞` gives a superlinear exponent such as `p/(p-rho)` assuming `p > rho`.  Either way, **the price of avoiding the `L∞` circularity is a superlinear lower-norm term**, not a linear `C * ∫u^p` term.

So: yes, the 1D Sobolev embedding can be used, and it is the right non-circular tool, but it does **not** prove the exact linear interpolation interface currently demanded by `RelativeMoserInterpolationBefore`.

## Why the current target inequality cannot be true

The proposed target is:

```text
∀ p ≥ p0, ∀ eps > 0, ∃ Ceps,
  ∫ u^(p+rho)
    ≤ eps * ∫ |∇(u^(p/2))|² + Ceps * ∫ u^p.
```

Assume `rho > 0`.  Put `u(x) = K`, a positive constant on `[0,1]`.  Then

```text
∇(u^(p/2)) = 0,
∫ u^(p+rho) = K^(p+rho),
∫ u^p = K^p.
```

Thus the inequality implies

```text
K^(p+rho) ≤ Ceps K^p,
```

or

```text
K^rho ≤ Ceps
```

for all `K > 0`.  This is impossible.  Therefore no Lean proof should exist for this statement without some extra hypothesis, such as an a priori `L∞` bound, an a priori `L^p` bound with constants allowed to depend on it, or a mass normalization plus a different lower-order term.

This is not a technical Lean gap; it is mathematically false.

## Why the already-proved Agmon inequality does not directly give the existing interface

The proved Agmon interpolation is:

```text
∫ f^q ≤ eps * ∫ f^(q-2) |f'|² + Ceps * (∫ f)^q.
```

If one applies it directly with `f = u` and `q = p + rho`, then the gradient term is

```text
∫ u^(p+rho-2) |u'|².
```

But the diffusion term available from testing the PDE at exponent `p` is usually

```text
∫ u^(p-2) |u'|²
```

or equivalently

```text
∫ |∇(u^(p/2))|² = (p/2)² ∫ u^(p-2) |u'|².
```

The Agmon gradient at exponent `p+rho` contains the extra factor `u^rho`:

```text
u^(p+rho-2) |u'|² = u^rho * u^(p-2) |u'|².
```

Removing that factor requires an `L∞` bound on `u`, which is exactly the circular step.

Applying the proved Agmon inequality to `f = u^(p/2)` is also not the desired fix.  If

```text
g = u^(p/2),
q = 2 + 2*rho/p,
```

then

```text
∫ g^q = ∫ u^(p+rho),
```

but the Agmon gradient becomes

```text
∫ g^(q-2) |g'|²
  = ∫ u^rho |∇(u^(p/2))|²,
```

again with the unwanted `u^rho` factor.

Therefore the existing Agmon statement is not the right lemma to produce the old `RelativeMoserInterpolationBefore` interface.

## Standard 1D non-circular replacement

Set

```text
A_p = ∫ u^p,
Y_p = ∫ |∇(u^(p/2))|²,
g = u^(p/2).
```

Then

```text
∫ u^(p+rho) = ∫ g^(2 + 2*rho/p).
```

Let

```text
r = 2 + 2*rho/p.
```

In one dimension, the Gagliardo--Nirenberg inequality gives, for `r ≥ 2`,

```text
||g||_r ≤ C ||g'||_2^a ||g||_2^(1-a) + C ||g||_2,
```

with

```text
a = 1/2 - 1/r.
```

Raising to the `r`-th power gives the schematic bound

```text
∫ g^r
  ≤ C * ||g'||_2^(a*r) * ||g||_2^((1-a)*r)
    + C * ||g||_2^r.
```

For

```text
r = 2 + 2*rho/p,
```

one has

```text
a*r = rho/p.
```

Since

```text
||g'||_2² = Y_p,
||g||_2² = A_p,
```

this becomes schematically

```text
∫ u^(p+rho)
  ≤ C * Y_p^(rho/(2*p)) * A_p^(1 + rho/(2*p))
    + C * A_p^(1 + rho/p).
```

Young's inequality then yields, for `2*p > rho`,

```text
∫ u^(p+rho)
  ≤ eps * Y_p
    + Ceps,p,rho * A_p^((2*p + rho)/(2*p - rho))
    + C * A_p^(1 + rho/p).
```

Since

```text
(2*p + rho)/(2*p - rho) > 1,
```

this is superlinear in `A_p`.  This superlinear term is expected.  It is exactly what avoids using an a priori `L∞` bound.

A clean Lean-facing replacement interface would therefore be closer to:

```lean
import Mathlib

open MeasureTheory

/-- Schematic replacement, not intended as already compiling code.
The important point is the superlinear power of `∫ u^p`. -/
def RelativeMoserInterpolationBefore1D_GN_Schematic : Prop :=
  ∀ p : ℝ,
    0 < p →
    ∀ eps : ℝ,
      0 < eps →
      ∃ Ceps : ℝ,
        0 < Ceps ∧
        ∀ u, True
```

Mathematically, the intended conclusion should be shaped like:

```text
∫ u^(p+rho)
  ≤ eps * ∫ |∇(u^(p/2))|²
    + Ceps * (∫ u^p)^gamma
    + Ceps * (∫ u^p)^(1 + rho/p),
```

with

```text
gamma = (2*p + rho) / (2*p - rho).
```

In a formalization, it may be easier to keep both powers rather than forcing them into one exponent.

## What the elementary `H¹ -> L∞` estimate gives

The user-suggested route is:

```text
||g||_∞² ≤ C (||g||_2² + ||g'||_2²),
```

with

```text
g = u^(p/2).
```

This gives

```text
||u||_∞^p = ||g||_∞²
  ≤ C (A_p + Y_p).
```

Since

```text
∫ u^(p+rho) ≤ ||u||_∞^rho ∫ u^p,
```

we get

```text
∫ u^(p+rho)
  ≤ C (A_p + Y_p)^(rho/p) * A_p.
```

Splitting the sum and applying Young gives, for `p > rho`,

```text
∫ u^(p+rho)
  ≤ eps * Y_p
    + Ceps,p,rho * A_p^(p/(p-rho))
    + C * A_p^(1 + rho/p).
```

This is valid and non-circular, but again the lower term is superlinear in `A_p`, not linear.

So the answer to the specific question

```text
Can this be used to derive the needed interpolation?
```

is:

```text
It derives a valid Moser interpolation, but not the old linear one.
```

It can support a 1D Moser iteration if the iteration machinery is modified to accept the superlinear `A_p` term.

## How to run the Moser iteration naturally in 1D

The standard way is to avoid converting the proved Agmon gradient with a missing `u^rho` factor.  Instead, at exponent `p`, use the diffusion term exactly as it appears:

```text
Y_p = ∫ |∇(u^(p/2))|².
```

Then estimate the higher power by a 1D Gagliardo--Nirenberg inequality for

```text
g = u^(p/2).
```

The schematic iteration step is then:

```text
d/dt A_p + c_p Y_p
  ≤ lower-order terms involving ∫ u^(p+rho)
  ≤ eps Y_p + Ceps * A_p^gamma + ...
```

Choose `eps` small relative to `c_p` and absorb `eps Y_p` into the left-hand side.  The resulting differential inequality is of the form

```text
d/dt A_p ≤ C_p * A_p^gamma + lower-order terms.
```

or, after integrating on a time interval and using the usual Moser exponent ladder, a recursive bound for `A_p` or `A_p^(1/p)`.

This is a standard 1D route.  It is not circular because no `L∞` hypothesis is used; the Sobolev embedding is applied to `g = u^(p/2)` and the gradient term is exactly the diffusion gradient.

## Consequence for the current Lean architecture

The current interface

```text
RelativeMoserInterpolationBefore:
  ∫ u^(p+rho)
    ≤ eps * ∫ |nabla(u^(p/2))|² + Ceps * ∫ u^p
```

should not be treated as an assumption-cleanup target unless extra hypotheses are added.  As written, it is false for `rho > 0`.

There are three honest options.

### Option A: Change the interpolation interface to the true 1D GN form

Replace the linear lower term by a superlinear term:

```text
∫ u^(p+rho)
  ≤ eps * ∫ |∇(u^(p/2))|²
    + Ceps * (∫u^p)^gamma
    + Ceps * (∫u^p)^(1 + rho/p).
```

This is the mathematically natural non-circular interface.

### Option B: Allow dependence on an existing `L^p` bound

If the iteration state already has

```text
∫ u^p ≤ B_p,
```

then the superlinear term can be linearized as

```text
(∫u^p)^gamma ≤ B_p^(gamma-1) * ∫u^p.
```

But then the constant depends on `B_p`.  This is not the original function-independent interpolation lemma; it is an interpolation lemma relative to an existing finite-horizon `L^p` control.

### Option C: Keep the old interface but add an `L∞` hypothesis

With

```text
||u||∞ ≤ M,
```

one trivially has

```text
∫u^(p+rho) ≤ M^rho ∫u^p.
```

But this is circular if used to prove the first `L∞` bound.

## Recommended next proof target

The highest-signal non-circular Lean target is not the old `RelativeMoserInterpolationBefore`, but a 1D GN replacement around the variable

```text
g = u^(p/2).
```

A useful theorem shape is:

```text
For p > rho/2 and eps > 0, there exists Ceps such that

  ∫ u^(p+rho)
    ≤ eps * ∫ |∇(u^(p/2))|²
      + Ceps * (∫u^p)^((2*p+rho)/(2*p-rho))
      + Ceps * (∫u^p)^(1+rho/p).
```

A slightly easier first Lean target, using only `H¹ -> L∞`, is:

```text
For p > rho and eps > 0, there exists Ceps such that

  ∫ u^(p+rho)
    ≤ eps * ∫ |∇(u^(p/2))|²
      + Ceps * (∫u^p)^(p/(p-rho))
      + Ceps * (∫u^p)^(1+rho/p).
```

This version is weaker but likely easier to formalize, because it follows directly from:

```text
∫ u^(p+rho)
  ≤ ||u||∞^rho ∫u^p
```

and

```text
||u||∞^p ≤ C (∫u^p + ∫|∇(u^(p/2))|²).
```

## Bottom line

* The natural Agmon gradient form can be used in a Moser iteration only if the iteration is formulated at the matching exponent or through the variable `g = u^(p/2)`.
* The old linear interpolation interface is false without an `L∞` bound or another prior amplitude control.
* The standard 1D Sobolev/Gagliardo--Nirenberg route is valid and non-circular, but it yields a superlinear lower term in `∫u^p`.
* Therefore the honest Lean cleanup is to introduce a new 1D relative Moser interpolation interface with a superlinear `A_p` term, then adapt the finite-horizon Moser wrappers to consume that interface.
