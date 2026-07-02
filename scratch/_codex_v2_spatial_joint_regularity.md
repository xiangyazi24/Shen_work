# Codex Spec: v2 Spatial Joint Regularity (L1ContOn)

## Goal

Create ONE new file `ShenWork/Wiener/EWA/SourceSpatialJointRegularityL1.lean`
that provides L1ContOn-compatible versions of the gradient and second-gradient
joint continuity theorems. These replace the DuhamelSourceTimeC1-based versions
in `SourceSpatialJointRegularity.lean`.

## Key mathematical insight

The DuhamelSourceTimeC1 version uses `derivBound` in the Weierstrass M-test
dominator. The L1ContOn version does NOT need derivBound because the Duhamel
integral's exponential kernel absorbs one eigenvalue factor:

```
λ_n · |∫₀ᵗ a(s,n) exp(-λ_n(t-s)) ds|
≤ λ_n · envelope(n) · ∫₀ᵗ exp(-λ_n(t-s)) ds
= envelope(n) · (1 - exp(-λ_n·t))
≤ envelope(n)
```

So λ_n · |duhamelSpectralCoeff a t n| ≤ envelope(n), which is summable.
This replaces `2·envelope + derivBound·recipSquareTerm` with just `envelope`.

## What to produce

### 1. `eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn`

```lean
private theorem eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff a t n| ≤ src.envelope n
```

Proof sketch:
```
λ_n * |∫₀ᵗ a(s,n) exp(-λ_n(t-s)) ds|
≤ λ_n * envelope(n) * ∫₀ᵗ exp(-λ_n(t-s)) ds
= λ_n * envelope(n) * (1 - exp(-λ_n t)) / λ_n    [for λ_n > 0]
= envelope(n) * (1 - exp(-λ_n t))
≤ envelope(n)
```

For n = 0: λ_0 = 0, so LHS = 0 ≤ envelope(0). Handle separately.

The integral ∫₀ᵗ exp(-λ_n(t-s)) ds can be computed as:
∫₀ᵗ exp(-λ_n t + λ_n s) ds = exp(-λ_n t) * ∫₀ᵗ exp(λ_n s) ds

For λ_n > 0: = exp(-λ_n t) * (exp(λ_n t) - 1) / λ_n = (1 - exp(-λ_n t)) / λ_n

For the proof in Lean, instead of computing the integral explicitly, use:

```
λ_n * |duhamelSpectralCoeff a t n|
= λ_n * |∫₀ᵗ exp(-λ_n(t-s)) * a(s,n) ds|           (unfold duhamelSpectralCoeff)
≤ λ_n * ∫₀ᵗ |exp(-λ_n(t-s))| * |a(s,n)| ds         (abs of integral ≤ integral of abs)
≤ λ_n * envelope(n) * ∫₀ᵗ exp(-λ_n(t-s)) ds         (henv_bound)
= envelope(n) * λ_n * ∫₀ᵗ exp(-λ_n(t-s)) ds
```

Then we need λ_n * ∫₀ᵗ exp(-λ_n(t-s)) ds ≤ 1.

This equals 1 - exp(-λ_n t) ≤ 1 (for λ_n ≥ 0).

ALTERNATIVE SIMPLER APPROACH (no integrals needed):

Use the existing `abs_duhamelSpectralCoeff_le_weak`:
```
|duhamelSpectralCoeff a t n| ≤ t * envelope(n)
```

But we need λ_n * t * envelope(n), which is NOT ≤ envelope(n) for large n.

So the integral approach IS needed. Let me check what's available.

Actually, let me look at the structure more carefully. `duhamelSpectralCoeff`
is defined as an interval integral:

```lean
def duhamelSpectralCoeff (a : ℝ → ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * λ_ n) * a s n
```

We need: λ_n * |∫₀ᵗ exp(-(t-s)·λ_n) * a(s,n) ds| ≤ envelope(n)

Proof strategy:
1. |∫₀ᵗ f| ≤ ∫₀ᵗ |f| (by `intervalIntegral.norm_integral_le_integral_norm`)
2. |exp(-(t-s)·λ_n) * a(s,n)| = exp(-(t-s)·λ_n) * |a(s,n)| ≤ exp(-(t-s)·λ_n) * envelope(n)
3. λ_n * ∫₀ᵗ exp(-(t-s)·λ_n) ds = 1 - exp(-t·λ_n) ≤ 1
4. Combine: λ_n * |integral| ≤ λ_n * envelope(n) * ∫₀ᵗ exp(...) ds ≤ envelope(n)

For step 3: use `intervalIntegral.integral_exp_neg_mul_left` or compute manually.

Actually, a much simpler approach: the existing proof of `abs_duhamelSpectralCoeff_le`
shows that for each s ∈ [0,t]: exp(-(t-s)·λ_n) * |a(s,n)| ≤ envelope(n).
So the integral ≤ t · envelope(n).

But we need a TIGHTER bound. The point is that multiplying by λ_n:
  λ_n · ∫₀ᵗ exp(-(t-s)λ_n) ds = 1 - exp(-t λ_n) ≤ 1

The key new lemma is just: λ_n ∫₀ᵗ exp(-(t-s)λ_n) ds ≤ 1.

Use change of variables u = t - s:
∫₀ᵗ exp(-u λ_n) du = (1 - exp(-t λ_n))/λ_n for λ_n > 0.
So λ_n * this = 1 - exp(-t λ_n) ≤ 1.

In Lean, to avoid explicit integral computation, use the EXISTING bound differently.
Let me look at what's available in the codebase for bounding this integral.

ACTUALLY, the cleanest proof uses NO integral computation at all. Instead:

For n ≥ 1 (so λ_n > 0):
  λ_n * |duhamelCoeff(t,n)| 
  = |λ_n * duhamelCoeff(t,n)|
  = |a(t,n) - (a(t,n) - λ_n * duhamelCoeff(t,n))|   [rearrange]

Now, a(t,n) - λ_n * duhamelCoeff(t,n) = d'(t,n) (the time derivative of the
Duhamel coefficient). But we DON'T have this with L1ContOn!

So we DO need the integral approach.

SIMPLEST PROOF: Factor out the constant.

```
λ_n * |∫₀ᵗ exp(-(t-s)λ_n) a(s,n) ds|
≤ λ_n * ∫₀ᵗ exp(-(t-s)λ_n) |a(s,n)| ds       -- triangle
≤ λ_n * ∫₀ᵗ exp(-(t-s)λ_n) * envelope(n) ds    -- henv_bound
= envelope(n) * (λ_n * ∫₀ᵗ exp(-(t-s)λ_n) ds)  -- factor constant
```

Now we need `λ_n * ∫₀ᵗ exp(-(t-s)λ_n) ds ≤ 1`.

Let me check if this integral is computed somewhere in the repo.

SEARCH: grep for `integral.*exp.*eigenvalue` in the repo.

If not available, we need to compute it. Here's an approach that avoids 
explicitly computing the antiderivative:

**Approach using FTC:** The function F(s) = -(1/λ_n) exp(-(t-s)λ_n) has 
derivative exp(-(t-s)λ_n). So:
  ∫₀ᵗ exp(-(t-s)λ_n) ds = F(t) - F(0) = -1/λ_n + (1/λ_n)exp(-tλ_n)
Wait, F(s) = (1/λ_n)exp(-(t-s)λ_n), F'(s) = exp(-(t-s)λ_n).
F(t) = 1/λ_n, F(0) = (1/λ_n)exp(-tλ_n).
So integral = 1/λ_n - (1/λ_n)exp(-tλ_n) = (1 - exp(-tλ_n))/λ_n.
Times λ_n = 1 - exp(-tλ_n) ≤ 1.

In Lean this is a hasDerivAt + FTC computation. Fairly standard.

### 2. `fullSourceCoeff_continuous_of_L1ContOn`

Same as `fullSourceCoeff_continuous` but using L1ContOn:

```lean
private theorem fullSourceCoeff_continuous_of_L1ContOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p u) T)
    (n : ℕ) : ContinuousOn
      (fun t : ℝ => fullSourceCoeff p u u₀cos t n) (Icc 0 T)
```

Uses `duhamelSpectralCoeff_hasDerivAt_of_L1ContOn` from SourceSynthesisL1.lean.
Note: it's ContinuousOn (Icc 0 T), not Continuous globally. The proofs in
gradJC need this only on Ioo c Tb ⊂ Icc 0 T (for appropriate T).

### 3. `fullSourceCoeff_gradJC_of_L1ContOn`

Retype of `fullSourceCoeff_gradJC`. The dominator changes from:

OLD:
```
Mu0 * (exp(-c·λ) + λ·exp(-c·λ)) +
(|χ₀|+1) * ((Tb+2)·(envC+envL) + (dBC+dBL)·recipSquare)
```

NEW:
```
Mu0 * (exp(-c·λ) + λ·exp(-c·λ)) +
(|χ₀|+1) * (envC + envL)
```

Much simpler! The derivBound·recipSquare term is gone.

The bound per summand is:
```
|coeff(t,n)| · |mode(x,n)|
≤ (|H| + |χ₀|·|Bc| + |Bl|) · nπ
≤ (|H| + |χ₀|·|Bc| + |Bl|) · (1 + λ_n)
```

Now:
- (1+λ)|H| ≤ Mu0·(exp(-c·λ) + λ·exp(-c·λ))  [same as before]
- (1+λ)|Bc| = |Bc| + λ|Bc| ≤ T·envC + envC = (T+1)·envC
  But T is variable... actually let's use a cruder bound:
  |Bc| ≤ t·envC ≤ Tb·envC  (from abs_duhamelSpectralCoeff_le_weak)
  λ|Bc| ≤ envC  (from eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn)
  So (1+λ)|Bc| ≤ Tb·envC + envC = (Tb+1)·envC

Wait, the dominator needs to be a function of n only (not t), and it needs 
to dominate for ALL (t,x) in Ioo(c,Tb) × univ. We have:
- |Bc| ≤ t · envC(n) ≤ Tb · envC(n)   [since t < Tb]
- λ·|Bc| ≤ envC(n)                      [new bound, t-independent!]
- (1+λ)|Bc| = |Bc| + λ|Bc| ≤ Tb·envC(n) + envC(n) = (Tb+1)·envC(n)

So the dominator becomes:
```
Mu0 * (exp(-c·λ) + λ·exp(-c·λ))
+ (|χ₀|+1) * ((Tb+1) * (envC(n) + envL(n)))
```

Summability: 
- First term: `unitIntervalCosineHeatTrace_single_exp_summable` + 
  `unitIntervalCosineEigenvalue_mul_exp_summable` (both already exist)
- Second term: `hchem.henv_summable.add hlog.henv_summable` (summable by L1ContOn)

### 4. `fullSourceCoeff_grad2JC_of_L1ContOn`

Same pattern. The dominator for the second gradient uses λ_n instead of (1+λ_n):

```
Mu0 * λ·exp(-c·λ) + (|χ₀|+1) * (envC + envL)
```

Bound per summand:
```
|coeff(t,n)| · |mode2(x,n)| ≤ (|H| + |χ₀|·|Bc| + |Bl|) · λ
```

- λ|H| ≤ Mu0·λ·exp(-c·λ)
- λ|Bc| ≤ envC   [direct kernel estimate]
- λ|Bl| ≤ envL

So: total ≤ Mu0·λ·exp(-c·λ) + (|χ₀|+1)·(envC + envL)

### 5. `fullSourceCoeff_jointGradClosed_of_L1ContOn`

```lean
theorem fullSourceCoeff_jointGradClosed_of_L1ContOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p u) T)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |fullSourceCoeff p u u₀cos t n|)) :
    ContinuousOn (Function.uncurry (fun t x =>
      deriv (fun y => ∑' n,
        fullSourceCoeff p u u₀cos t n *
          cosineMode n y) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1)
```

Proof: apply gradJC_of_L1ContOn, mono, congr with gradSeries_eq_deriv.

### 6. `fullSourceCoeff_jointGrad2Closed_of_L1ContOn`

Same pattern for second gradient.

## Imports

```lean
import ShenWork.Wiener.EWA.SourceSpatialJointRegularity
import ShenWork.Wiener.EWA.SourceSynthesisL1
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
```

## Reference files (READ these to understand the retypes)

1. `ShenWork/Wiener/EWA/SourceSpatialJointRegularity.lean` (TEMPLATE — full file)
2. `ShenWork/Wiener/EWA/SourceSynthesisL1.lean` (provides v2 theorems — read only the open/import/theorem statements)
3. `ShenWork/Paper2/IntervalPicardLimitRestartWeak.lean` lines 127-140 (DuhamelSourceL1ContOn structure definition + abs_duhamelSpectralCoeff_le_weak)

## DuhamelSourceL1ContOn structure (for reference)

```lean
structure DuhamelSourceL1ContOn (a : ℝ → ℕ → ℝ) (T : ℝ) where
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s, 0 ≤ s → s ≤ T → ∀ n, |a s n| ≤ envelope n
  hcont : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 T)
```

## Key differences from the DuhamelSourceTimeC1 version

1. `henv_bound` takes `(s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T)` separately,
   NOT `s ∈ Set.Icc 0 T`
2. No `derivBound`, `hderivBound`, `adot`, `hderiv` fields
3. `hcont` gives ContinuousOn on Icc 0 T (not global Continuous)
4. `fullSourceCoeff_continuous` must become `fullSourceCoeff_continuousOn`
   restricted to a sub-interval of Icc 0 T

## Available existing lemmas (from SourceSynthesisL1.lean)

```lean
theorem duhamelSpectralCoeff_hasDerivAt_of_L1ContOn
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    HasDerivAt (fun s => duhamelSpectralCoeff a s n)
      (a t n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t n) t
```

This can be used for `continuousAt` of duhamelSpectralCoeff.

## Available existing lemmas (from IntervalPicardLimitRestartWeak.lean)

```lean
theorem abs_duhamelSpectralCoeff_le_weak
    {a : ℝ → ℕ → ℝ} {T : ℝ} (src : DuhamelSourceL1ContOn a T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (k : ℕ) :
    |duhamelSpectralCoeff a t k| ≤ t * src.envelope k
```

## Available existing lemmas (from SourceSpatialJointRegularity.lean)

```lean
-- Can be reused directly (no DuhamelSourceTimeC1 dependency):
theorem npi_le_one_add_eigenvalue (n : ℕ) : ...
theorem fullSource_triangle (H χ₀ Bc Bl : ℝ) : ...
theorem gradSeries_eq_deriv {b : ℕ → ℝ} (hb : ...) (x : ℝ) : ...
theorem grad2Series_eq_deriv2 {b : ℕ → ℝ} (hb : ...) (x : ℝ) : ...
```

These are `private` in the original file. You'll need to either:
- Copy them into the new file, OR
- Use `ShenWork.EWA.` namespace prefix if they're accessible

## How to prove eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn

Approach: bound the absolute value of the integral, then multiply by λ_n.

Step 1: |duhamelSpectralCoeff a t n| ≤ envelope(n) / λ_n · (1 - exp(-t·λ_n))

This requires computing ∫₀ᵗ exp(-(t-s)·λ_n) ds = (1 - exp(-t·λ_n))/λ_n.

For n = 0 (λ_0 = 0): |duhamelSpectralCoeff a t 0| ≤ t · envelope(0) 
[use abs_duhamelSpectralCoeff_le_weak], and λ_0 = 0, so λ_0 · anything = 0 ≤ envelope(0). Done.

For n ≥ 1 (λ_n > 0):

The integral computation uses FTC. Let g(s) = -(1/λ_n) · exp(-(t-s)·λ_n).
Then g'(s) = exp(-(t-s)·λ_n).
So ∫₀ᵗ exp(-(t-s)·λ_n) ds = g(t) - g(0) = -1/λ_n + exp(-t·λ_n)/λ_n 
Wait: g(t) = -1/λ_n · exp(0) = -1/λ_n
      g(0) = -1/λ_n · exp(-t·λ_n)
      g(t) - g(0) = -1/λ_n + 1/λ_n · exp(-t·λ_n) = (exp(-t·λ_n) - 1)/λ_n

Hmm, sign. Let me redo:
g(s) = (1/λ_n) · exp(-(t-s)·λ_n)
g'(s) = (1/λ_n) · λ_n · exp(-(t-s)·λ_n) = exp(-(t-s)·λ_n)  ✓
g(t) = 1/λ_n
g(0) = (1/λ_n) · exp(-t·λ_n)
∫₀ᵗ exp(-(t-s)·λ_n) ds = g(t) - g(0) = (1 - exp(-t·λ_n))/λ_n

So λ_n · ∫ = 1 - exp(-t·λ_n) ≤ 1. ✓

ALTERNATIVE simpler proof without integral computation:

Use the ODE: d/dt [exp(-tλ_n) * duhamelCoeff(t,n)] is bounded.
Actually this just adds complexity.

SIMPLEST proof using Lean tools:

```lean
-- For n ≥ 1: λ_n > 0
-- Use: |duhamelCoeff(t,n)| = |∫₀ᵗ exp(-(t-s)λ) a(s,n) ds|
-- Key bound: each integrand term has
--   |exp(-(t-s)λ) * a(s,n)| ≤ exp(-(t-s)λ) * envelope(n)
-- So: |duhamelCoeff| ≤ envelope(n) * ∫₀ᵗ exp(-(t-s)λ) ds
-- And: λ * ∫₀ᵗ exp(-(t-s)λ) ds = 1 - exp(-tλ) ≤ 1
-- Therefore: λ * |duhamelCoeff| ≤ envelope(n)
```

For the FTC step, HasDerivAt for s ↦ (1/λ)·exp(-(t-s)·λ) can be proved
with Real.hasDerivAt_exp composed with affine maps.

Then use `intervalIntegral.integral_eq_sub_of_hasDerivAt` to compute the integral.

## File structure

```lean
import ShenWork.Wiener.EWA.SourceSpatialJointRegularity
import ShenWork.Wiener.EWA.SourceSynthesisL1
import ShenWork.Paper2.IntervalPicardLimitRestartWeak

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalPicardIterateRestart
  (abs_duhamelSpectralCoeff_le)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn abs_duhamelSpectralCoeff_le_weak)
open ShenWork.CosineSpectrum
  (cosineMode cosineMode_deriv cosineMode_second_deriv)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeffSeries_grad_hasDerivAt
   cosineCoeffSeries_grad2_hasDerivAt)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalCosineHeatTrace_single_exp_summable)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)
open Set Filter Topology

variable {T : ℝ}

-- 1. eigenvalue bound (KEY NEW LEMMA)
private theorem eigenvalue_mul_abs_duhamelCoeff_le_of_L1ContOn ...

-- 2. fullSourceCoeff continuity on Ioo
private theorem fullSourceCoeff_continuousOn_Ioo_of_L1ContOn ...

-- 3. gradient JC (inner)
set_option maxHeartbeats 1200000 in
private theorem fullSourceCoeff_gradJC_of_L1ContOn ...

-- 4. second gradient JC (inner)
set_option maxHeartbeats 1200000 in
private theorem fullSourceCoeff_grad2JC_of_L1ContOn ...

-- 5. PUBLIC: gradient closed
theorem fullSourceCoeff_jointGradClosed_of_L1ContOn ...

-- 6. PUBLIC: second gradient closed
theorem fullSourceCoeff_jointGrad2Closed_of_L1ContOn ...

end ShenWork.EWA

#print axioms ShenWork.EWA.fullSourceCoeff_jointGradClosed_of_L1ContOn
#print axioms ShenWork.EWA.fullSourceCoeff_jointGrad2Closed_of_L1ContOn
```

## CRITICAL constraints

- NO sorry, NO axiom, NO native_decide, NO admit
- Line length ≤ 100 characters
- Do NOT modify any existing files
- File must compile: `lake env lean ShenWork/Wiener/EWA/SourceSpatialJointRegularityL1.lean` exit 0
- axiom print must show ONLY [propext, Classical.choice, Quot.sound]
- maxHeartbeats 1200000 for the JC proofs (they're big)
- USE `set_option maxHeartbeats 0` for the eigenvalue bound proof if needed

## What NOT to do

- Do NOT import `SourceSynthesisL1` if you don't use any theorem from it
  (you might only need duhamelSpectralCoeff_hasDerivAt_of_L1ContOn for
  fullSourceCoeff_continuousOn)
- Do NOT redefine any existing definition (fullSourceCoeff, duhamelSpectralCoeff, etc.)
- Do NOT use `duhamelSpectralCoeff_deriv_summable_uniform_bound` — that's TimeC1-only
