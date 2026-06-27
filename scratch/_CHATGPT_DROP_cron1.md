# Q1052 / cron3 — applying `cosineCoeffs_decay` at depth 3 to `ν · u^γ`, `u = S(t)u₀`

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

Yes, `cosineCoeffs_decay` at depth `j = 3` can be applied to the nonlinear source

```text
f(x) = ν · u(x)^γ
```

for a positive-time heat cosine representative `u = S(t)u₀`, **provided** the source is packaged as a global smooth cosine/Neumann representative and the depth-3 Neumann boundary chain is supplied.

The important correction is:

```text
Depth 3 does NOT require f''(0)=f''(1)=0 or f⁽⁴⁾(0)=f⁽⁴⁾(1)=0.
```

It requires the Neumann conditions on the tower levels:

```text
(g₀)' = f'      vanishes at 0 and 1,
(g₁)' = f'''    vanishes at 0 and 1,
(g₂)' = f'''''  vanishes at 0 and 1,
```

where

```text
g₀ = f,
g₁ = f'',
g₂ = f⁽⁴⁾,
g₃ = f⁽⁶⁾.
```

For heat cosine representatives, the clean proof is by **double-even parity**: a Neumann cosine series is even about `0` and even about `1`; post-composition `x ↦ ν · x^γ` preserves that parity on the positive range; all odd spatial derivatives of a doubly-even function vanish at the endpoints. The repo already has the abstract parity lemma for this.

## 1. Hypotheses of `cosineCoeffs_decay`

File:

```text
ShenWork/Paper2/IntervalIBPCoeffExtraction.lean
```

The structure is:

```lean
structure NeumannTower (g : ℕ → ℝ → ℝ) (j : ℕ) : Prop where
  step : ∀ i, i < j → g (i + 1) = deriv (deriv (g i))
  contDiff : ∀ i, i < j → ContDiffOn ℝ 2 (g i) (Set.Icc (0 : ℝ) 1)
  tend0 : ∀ i, i < j →
    Filter.Tendsto (deriv (g i)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
  tend1 : ∀ i, i < j →
    Filter.Tendsto (deriv (g i)) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  bc0 : ∀ i, i < j → deriv (g i) 0 = 0
  bc1 : ∀ i, i < j → deriv (g i) 1 = 0
```

The coefficient decay theorem is:

```lean
theorem cosineCoeffs_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |cosineCoeffs (g 0) n| ≤ 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

So `cosineCoeffs_decay` itself does **not** directly ask for `C^{2j}`. It asks for:

1. a tower `g` of depth `j`;
2. `g (i+1) = deriv (deriv (g i))` for each `i < j`;
3. `ContDiffOn ℝ 2 (g i)` on `[0,1]` for each `i < j`;
4. Neumann endpoint tendsto and endpoint equalities for `deriv (g i)` for each `i < j`;
5. a top raw coefficient bound `|rawCoeff n (g j)| ≤ M`.

A separate producer turns global `C^{2j}` plus odd-derivative boundary conditions into such a tower.

For depth 3, the relevant producer is:

```text
ShenWork/Paper2/IntervalNeumannTowerOfC6.lean
```

```lean
def gTower (f : ℝ → ℝ) (i : ℕ) : ℝ → ℝ := deriv^[2 * i] f

theorem neumannTower_three_of_contDiff_six
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    ∃ g, g 0 = f ∧ NeumannTower g 3
```

This is the exact depth-3 constructor to use for a global source representative `f`.

## 2. Can we build a depth-3 tower for `ν · u^γ`?

Yes, if `u` is represented by the global heat cosine representative and is positive on the global representative range.

Take:

```lean
import ShenWork.Paper2.IntervalIBPCoeffExtraction
import ShenWork.Paper2.IntervalNeumannTowerOfC6
import ShenWork.Paper2.IntervalSourceRepresentative

open ShenWork.Paper2.NeumannTowerOfC6 (gTower neumannTower_three_of_contDiff_six)
open ShenWork.Paper2.SourceRepresentative (DoublyEven higherNeumannCompatibility_of_doublyEven)

noncomputable section

namespace ShenWork.Paper2.PowerSourceDepth3Route

/-- The global source representative.  In the concrete heat Level0 use case,
`U` is the global Neumann heat cosine series representative. -/
def powerSourceRep (ν γ : ℝ) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ν * U x ^ γ

/-- Exact inputs needed to build the depth-3 tower for `ν · U^γ`. -/
theorem powerSource_neumannTower_three_inputs
    {ν γ : ℝ} {U : ℝ → ℝ}
    (hC6 : ContDiff ℝ (6 : ℕ) (powerSourceRep ν γ U))
    (hDE : DoublyEven (powerSourceRep ν γ U)) :
    ∃ g, g 0 = powerSourceRep ν γ U ∧
      ShenWork.IntervalIBPCoeffExtraction.NeumannTower g 3 := by
  rcases higherNeumannCompatibility_of_doublyEven hDE with ⟨hN0, hN1⟩
  exact neumannTower_three_of_contDiff_six hC6 hN0 hN1

end ShenWork.Paper2.PowerSourceDepth3Route
```

For the actual heat Level0 source, the remaining facts to instantiate the theorem are:

```text
hC6 : ContDiff ℝ 6 (fun x => ν * U(x)^γ)
hDE : DoublyEven (fun x => ν * U(x)^γ)
```

The first is analytic smoothness; the second is parity.

### Does `u^γ` inherit Neumann BCs?

For the first Neumann condition, yes:

```text
(u^γ)' = γ · u^(γ-1) · u'
```

so at an endpoint `u' = 0` implies `(u^γ)' = 0`, assuming the usual positivity/smoothness hypotheses for real powers.

But depth 3 needs more than the first derivative. It needs:

```text
(ν·u^γ)'     = 0,
(ν·u^γ)'''   = 0,
(ν·u^γ)''''' = 0
```

at `x = 0` and `x = 1`.

You do **not** need `(ν·u^γ)''` or `(ν·u^γ)⁽⁴⁾` to vanish. Those are the even tower levels, not the Neumann boundary data. The `NeumannTower` asks for `deriv (g i)` to vanish, and since `g i = f^(2i)`, those are odd derivatives of `f`.

The easiest way to prove all of them is not to expand Faà di Bruno formulas. Use parity:

```text
U is a Neumann cosine series
  ⟹ U is DoublyEven
  ⟹ ν · U^γ is DoublyEven
  ⟹ all odd derivatives vanish at 0 and 1
  ⟹ hN0/hN1 for depth 3.
```

Repo support is in:

```text
ShenWork/Paper2/IntervalSourceRepresentative.lean
```

Relevant names:

```lean
ShenWork.Paper2.SourceRepresentative.DoublyEven
ShenWork.Paper2.SourceRepresentative.DoublyEven.comp
ShenWork.Paper2.SourceRepresentative.gTower_deriv_zero_of_doublyEven
ShenWork.Paper2.SourceRepresentative.gTower_deriv_one_of_doublyEven
ShenWork.Paper2.SourceRepresentative.higherNeumannCompatibility_of_doublyEven
```

`higherNeumannCompatibility_of_doublyEven` gives exactly:

```lean
(∀ i, i < 3 → deriv (gTower f i) 0 = 0) ∧
(∀ i, i < 3 → deriv (gTower f i) 1 = 0)
```

for any doubly-even `f`.

## 3. Does heat semigroup Neumann imply source Neumann?

At the level of the first endpoint derivative, yes. But the robust depth-3 statement is:

```text
The global heat cosine representative U is doubly even.
The source f = ν · U^γ is doubly even because DoublyEven is closed under post-composition
and scalar multiplication/product-style constructions.
Therefore f', f''', and f''''' vanish at both endpoints.
```

The repo proves the key abstract fact:

```lean
theorem higherNeumannCompatibility_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) :
    (∀ i, i < 3 → deriv (gTower f i) 0 = 0) ∧
      (∀ i, i < 3 → deriv (gTower f i) 1 = 0)
```

This avoids doing individual chain-rule endpoint computations.

For `u = S(t)u₀`, the global heat representative is the cosine series, so it is even about `0` and `1`. If it is positive on `[0,1]`, the symmetry/periodicity of the cosine representative extends positivity globally. Then real-power composition is smooth and parity-preserving.

## 4. Exact depth-3 NeumannTower inputs for `ν · u^γ`

Let:

```lean
U : ℝ → ℝ          -- global heat cosine representative at fixed positive time
f : ℝ → ℝ := fun x => p.ν * U x ^ p.γ
```

To build a depth-3 tower using the committed producer, you need exactly:

```lean
-- File: ShenWork/Paper2/IntervalNeumannTowerOfC6.lean
hfC6 : ContDiff ℝ (6 : ℕ) f

hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0
hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0
```

Then:

```lean
obtain ⟨g, hg0, Htower⟩ :=
  ShenWork.Paper2.NeumannTowerOfC6.neumannTower_three_of_contDiff_six
    hfC6 hN0 hN1
```

To apply `cosineCoeffs_decay` at depth 3 for a mode `n`, additionally need:

```lean
hn : 1 ≤ n
hTop : |ShenWork.IntervalIBPCoeffExtraction.rawCoeff n (g 3)| ≤ M
```

Then:

```lean
have hdecay :
    |ShenWork.IntervalNeumannFullKernel.cosineCoeffs f n| ≤
      2 * M / ((n : ℝ) * Real.pi) ^ (2 * 3) :=
  ShenWork.IntervalIBPCoeffExtraction.cosineCoeffs_decay
    n hn Htower hTop
```

For a uniform envelope over all modes, you need a uniform top coefficient bound, usually from a uniform bound on the sixth derivative:

```text
∀ n, 1 ≤ n → |rawCoeff n (g 3)| ≤ M.
```

Since `g 3 = f⁽⁶⁾`, this follows from a bound on `f⁽⁶⁾` on `[0,1]`:

```text
|rawCoeff n (f⁽⁶⁾)| ≤ ∫₀¹ |f⁽⁶⁾(x)| dx ≤ M.
```

For positive-time heat, `M` should come from compactness/joint continuity on a positive time slab if a uniform-in-time envelope is needed.

## Existing repo bridge for this exact shape

The repo already uses this pattern in:

```text
ShenWork/Paper2/IntervalEigenCubeTailFromTower.lean
```

The per-mode bridge is:

```lean
ShenWork.Paper2.EigenCubeTailFromTower.eigenCube_bound_of_tower
```

and the packaged bridge is:

```lean
ShenWork.Paper2.EigenCubeTailFromTower.SourceEigenCubeTailFields_of_neumannTower
```

These use a depth-3 tower to get λ³ pointwise control:

```text
λ_n^3 · |cosineCoeffs f n| ≤ 2M.
```

For `DuhamelSourceTimeC2Coeff`, λ²-summability is weaker: depth 3 gives

```text
|cosineCoeffs f n| ≤ C/(nπ)^6,
λ_n² |cosineCoeffs f n| ≤ C/(nπ)^2,
```

which is summable.

## Bottom line

1. `cosineCoeffs_decay` needs a `NeumannTower g j` and a top raw-coefficient bound. The tower encodes the `C^{2j}`-Neumann chain, but the theorem itself consumes the tower, not raw `C^{2j}` assumptions.
2. For depth 3, use `neumannTower_three_of_contDiff_six`. It needs global `ContDiff ℝ 6 f` and vanishing of `f'`, `f'''`, `f'''''` at both endpoints.
3. For `f = ν · (S(t)u₀)^γ`, first derivative Neumann follows by chain rule from `u' = 0`, but depth 3 needs all odd derivatives through 5. The repo’s intended proof is parity: the heat cosine representative is doubly even, `ν · u^γ` is doubly even, and `higherNeumannCompatibility_of_doublyEven` gives all required endpoint vanishings.
4. The exact extra input after the tower is a top bound on `rawCoeff n (g 3)`, equivalently a uniform L1/sup bound for the sixth derivative representative.
