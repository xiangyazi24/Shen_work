# Q704 / cron1: `DoublyEven` closure under constants and cosine series

Repo inspected: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

## Verdict

There is **no named** theorem:

```lean
DoublyEven.const_mul
DoublyEven.smul
DoublyEven.tsum
```

in the repo.

But for the concrete target `ν * f x ^ γ`, you usually do **not** need a separate constant-multiplication lemma.  The existing theorem

```lean
DoublyEven.comp
```

already covers the whole expression in one step:

```lean
have hsrc_de : DoublyEven (fun x => ν * f x ^ γ) :=
  DoublyEven.comp (fun y : ℝ => ν * y ^ γ) hf
```

where:

```lean
hf : DoublyEven f
```

This avoids constructing `DoublyEven (fun x => f x ^ γ)` and then multiplying by a constant.  Positivity of `f` is needed for differentiability/`ContDiff` of the real power, but **not** for the parity equality itself.

If you do want a local constant-multiplication closure lemma, it is a one-liner from `DoublyEven.comp`:

```lean
theorem DoublyEven.const_mul {c : ℝ} {f : ℝ → ℝ} (hf : DoublyEven f) :
    DoublyEven (fun x => c * f x) :=
  DoublyEven.comp (fun y : ℝ => c * y) hf
```

or, using the existing product closure:

```lean
have hconst : DoublyEven (fun _ : ℝ => c) where
  about0 := by intro x; rfl
  about1 := by intro x; rfl

have hcf : DoublyEven (fun x => c * f x) :=
  hconst.mul hf
```

## 1. Search for `DoublyEven.const_mul` / `DoublyEven.smul`

Searches run:

```text
DoublyEven.const_mul
DoublyEven.smul
DoublyEven constant
```

Result: **no hits**.

The available exported closure lemmas are in:

```text
ShenWork/Paper2/IntervalSourceRepresentative.lean
```

The relevant API is:

```lean
theorem DoublyEven.add {f g : ℝ → ℝ} (hf : DoublyEven f) (hg : DoublyEven g) :
    DoublyEven (fun x => f x + g x)
```

```lean
theorem DoublyEven.mul {f g : ℝ → ℝ} (hf : DoublyEven f) (hg : DoublyEven g) :
    DoublyEven (fun x => f x * g x)
```

```lean
theorem DoublyEven.comp {f : ℝ → ℝ} (g : ℝ → ℝ) (hf : DoublyEven f) :
    DoublyEven (fun x => g (f x))
```

For `ν * f(x)^γ`, use:

```lean
DoublyEven.comp (fun y : ℝ => ν * y ^ γ) hf
```

For just constant multiplication, use:

```lean
DoublyEven.comp (fun y : ℝ => ν * y) hf
```

## 2. Search for `DoublyEven.tsum` / infinite-series closure

Searches run:

```text
DoublyEven.tsum
tsum_congr DoublyEven
doublyEven_cosineSeries
DoublyEven
```

Result: there is **no generic** theorem of the form:

```lean
DoublyEven.tsum
```

or:

```lean
(∀ n, DoublyEven (F n)) → DoublyEven (fun x => ∑' n, F n x)
```

But there is a **specific cosine-series theorem**, which is exactly what is needed for Neumann cosine representatives:

```text
ShenWork/Paper2/IntervalSourceC6Representative.lean
```

```lean
theorem doublyEven_cosineSeries (c : ℕ → ℝ) :
    DoublyEven (fun x => ∑' n, c n * cosineMode n x) where
  about0 := fun x => by
    refine tsum_congr (fun n => ?_)
    have := (doublyEven_cos n).about0 x
    simp only [cosineMode]; rw [this]
  about1 := fun x => by
    refine tsum_congr (fun n => ?_)
    have := (doublyEven_cos n).about1 x
    simp only [cosineMode]; rw [this]
```

This theorem uses:

```lean
theorem doublyEven_cos (n : ℕ) :
    DoublyEven (fun x : ℝ => Real.cos (n * Real.pi * x))
```

from `IntervalSourceRepresentative.lean`.

So for a cosine representative:

```lean
Ucos := fun x => ∑' n, c n * cosineMode n x
```

you can write:

```lean
have hUcos_de : DoublyEven (fun x => ∑' n, c n * cosineMode n x) :=
  ShenWork.Paper2.SourceC6Representative.doublyEven_cosineSeries c
```

Then:

```lean
have hsource_de : DoublyEven (fun x => ν * (∑' n, c n * cosineMode n x) ^ γ) :=
  DoublyEven.comp (fun y : ℝ => ν * y ^ γ) hUcos_de
```

## 3. Heat-semigroup cosine series and `DoublyEven`

Searches run:

```text
heatSemigroup DoublyEven
heatEWA DoublyEven
conjugatePicardIter DoublyEven
intervalFullSemigroupOperator DoublyEven
heatCoeff cosineMode doublyEven
heatCoeff cosineMode hU_even
```

Result: I found **no direct theorem** named or shaped like:

```lean
DoublyEven (fun x => intervalFullSemigroupOperator t ... x)
```

or:

```lean
DoublyEven (fun x => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
```

However, there are two usable pieces.

### A. Direct cosine-series parity theorem

`doublyEven_cosineSeries` applies to **any** coefficient family.  For the heat semigroup cosine representative:

```lean
U_cos := fun x => ∑' k,
  (Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) * cosineMode k x
```

use:

```lean
have hUcos_de : DoublyEven U_cos := by
  simpa [U_cos] using
    ShenWork.Paper2.SourceC6Representative.doublyEven_cosineSeries
      (fun k => Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k)
```

Then the nonlinear source representative is immediate:

```lean
have hsrc_de : DoublyEven (fun x => p.ν * U_cos x ^ p.γ) :=
  DoublyEven.comp (fun y : ℝ => p.ν * y ^ p.γ) hUcos_de
```

### B. Heat-slice agreement with the cosine series

For the level-0 heat trajectory, the repo has:

```text
ShenWork/Paper2/IntervalPicardIterateRepresentation.lean
```

```lean
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
```

This gives agreement on `[0,1]` between the interval-domain heat slice and its global cosine representative.  The global representative is `DoublyEven` by `doublyEven_cosineSeries`.

Important nuance: `intervalDomainLift` is the zero-extension outside `[0,1]`, so it is generally **not** the global doubly-even object.  The **cosine-series representative** is the global doubly-even object, and `hagree_zero` transfers facts back to the interval slice on `[0,1]`.

### C. Local manual heat parity already appears in `IntervalConjugateLevel0BFormSourceOn.lean`

Inside the level-0 heat-semigroup construction, the file sets:

```lean
set U_cos := fun x => ∑' k,
  (Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) *
    cosineMode k x
```

and locally proves:

```lean
have hU_even : ∀ x, U_cos (-x) = U_cos x := by
  intro x; simp only [hU_cos_def]
  exact tsum_congr (fun k => by congr 1; exact cosineMode_neg' k x)
```

```lean
have hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x := by
  intro x
  rw [show (2 : ℝ) - x = (-x) + 2 from by ring]
  simp only [hU_cos_def]
  rw [show (fun k => (Real.exp (-s * unitIntervalCosineEigenvalue k) *
        heatCoeff u₀ k) * cosineMode k ((-x) + 2)) =
      (fun k => (Real.exp (-s * unitIntervalCosineEigenvalue k) *
        heatCoeff u₀ k) * cosineMode k (-x)) from
    funext (fun k => by congr 1; exact cosineMode_add_two' k (-x))]
  exact hU_even x
```

This is effectively the `DoublyEven` proof for the heat cosine representative, but it is local/manual and not packaged as a theorem.

## Recommended tiny additions, if you want them

The repo already has enough to proceed, but these wrappers would make later proofs cleaner.

```lean
namespace ShenWork.Paper2.SourceRepresentative

noncomputable section

/-- Constant multiplication preserves double-even parity. -/
theorem DoublyEven.const_mul {c : ℝ} {f : ℝ → ℝ} (hf : DoublyEven f) :
    DoublyEven (fun x => c * f x) :=
  DoublyEven.comp (fun y : ℝ => c * y) hf

/-- Constant-right multiplication preserves double-even parity. -/
theorem DoublyEven.mul_const {c : ℝ} {f : ℝ → ℝ} (hf : DoublyEven f) :
    DoublyEven (fun x => f x * c) := by
  simpa [mul_comm] using hf.const_mul (c := c)

/-- Power followed by constant multiplication preserves double-even parity. -/
theorem DoublyEven.const_mul_rpow {ν γ : ℝ} {f : ℝ → ℝ} (hf : DoublyEven f) :
    DoublyEven (fun x => ν * f x ^ γ) :=
  DoublyEven.comp (fun y : ℝ => ν * y ^ γ) hf

end

end ShenWork.Paper2.SourceRepresentative
```

For a heat representative wrapper:

```lean
open ShenWork.Paper2.SourceRepresentative
open ShenWork.Paper2.SourceC6Representative
open ShenWork.CosineSpectrum

noncomputable def heatCosRepr (u₀ : intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun x => ∑' k,
    (Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) * cosineMode k x

theorem heatCosRepr_doublyEven (u₀ : intervalDomainPoint → ℝ) (s : ℝ) :
    DoublyEven (heatCosRepr u₀ s) := by
  simpa [heatCosRepr] using
    doublyEven_cosineSeries
      (fun k => Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k)
```

The only caveat is import placement: `heatCoeff` and `unitIntervalCosineEigenvalue` need the same imports/open namespaces used by the level-0 heat files.
