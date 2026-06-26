# Q682 / cron1: `cosineCoeffs` real-integral bridge and weak-H² Laplacian coefficient identity

## Verdict

Yes — the repo already has reusable lemmas relating `cosineCoeffs` to the real interval integral

```lean
∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
```

For positive modes, the best public lemma is:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral
```

Signature/location:

```lean
/-- For a real-valued `f`, the positive-mode cosine coefficient equals
`2 * ∫₀¹ cos(nπx) * f(x) dx`. -/
theorem cosineCoeffs_pos_eq_integral {f : ℝ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    cosineCoeffs f n =
      2 * ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x
```

- `ShenWork/Paper2/IntervalMildPicardRegularity.lean:417-431`

There is also a uniform all-modes public lemma:

```lean
theorem cosineCoeffs_eq_factor_mul_integral (f : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x
```

- `ShenWork/Paper2/IntervalMildPicardRegularity.lean:433-442`

And a raw-coefficient public wrapper:

```lean
/-- `cosineCoeffs f n = 2 · rawCoeff n f` for `n ≥ 1`. -/
theorem cosineCoeffs_eq_two_rawCoeff {f : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n) :
    cosineCoeffs f n = 2 * rawCoeff n f
```

- `ShenWork/Paper2/IntervalSourceC6Representative.lean:146-151`

## Private helper matching the exact pattern

`IntervalMildSourceDecayHelper.lean` has a private helper with exactly the normalization you need:

```lean
private theorem cosineCoeffs_eq_two_raw_integral
    {f : ℝ → ℝ} {k : ℕ} (hk : k ≠ 0) :
    cosineCoeffs f k =
      2 * ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x := by
  simp only [cosineCoeffs, unitIntervalNeumannCosineCoeff, if_neg hk]
  rw [unitIntervalCosineRawCoeff]
  have hcast :
      (fun x : ℝ =>
          (Real.cos ((k : ℝ) * Real.pi * x) : ℂ) * ((f x : ℝ) : ℂ)) =
        fun x : ℝ =>
          ((Real.cos ((k : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  rw [hcast, intervalIntegral.integral_ofReal, Complex.ofReal_re]
```

- `ShenWork/PDE/IntervalMildSourceDecayHelper.lean:127-141`

Since it is `private`, use the public `cosineCoeffs_pos_eq_integral` instead.

## The exact desired identity is not completed as a reusable theorem

I did **not** find a completed theorem named like

```lean
cosineCoeffs_secondDeriv_eq_neg_eigenvalue_mul
```

or a completed theorem directly proving

```lean
cosineCoeffs hf.secondDeriv k = -((k : ℝ) * Real.pi)^2 * cosineCoeffs f k
```

from `hf : IntervalWeakH2Neumann f`.

However, `IntervalSourceDecayQuantitative.lean` has the exact local pattern inline and comments spelling out the identity.  In the quadratic decay proof it unfolds `cosineCoeffs` to the real integral and proves:

```lean
have hcoeff : cosineCoeffs f k = 2 * raw := by
  -- replicate the (private) helper identity: for k ≠ 0,
  -- `cosineCoeffs f k = 2·∫₀¹ cos(kπx)·f(x) dx`
  simp only [ShenWork.IntervalNeumannFullKernel.cosineCoeffs,
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
    if_neg hk_ne,
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
  have hcast : ... := by
    funext x
    push_cast
    ring
  rw [hcast, intervalIntegral.integral_ofReal, Complex.ofReal_re, hraw_def]
```

- `ShenWork/PDE/IntervalSourceDecayQuantitative.lean:98-113`

Below that, the file has an attempted depth-2/quartic decay lemma whose comments state precisely your target step:

```lean
-- So cosineCoeffs(f'') k = -(kπ)² * cosineCoeffs(f) k
```

but the lemma body is unfinished with `sorry`.

- `ShenWork/PDE/IntervalSourceDecayQuantitative.lean:140-162`
- `ShenWork/PDE/IntervalSourceDecayQuantitative.lean:166-173`

So: the ingredients exist, but the reusable identity should be added.

## Suggested theorem to add

This should be a very small lemma, using only `hf.weak_cosine_laplacian` plus the public positive-mode normalization lemma:

```lean
import ShenWork.PDE.IntervalMildSourceDecayHelper
import ShenWork.Paper2.IntervalMildPicardRegularity

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)

namespace ShenWork.PDE.IntervalMildSourceDecayHelper

noncomputable section

/-- Weak-H² Neumann Laplacian identity at normalized positive cosine coefficients. -/
theorem intervalWeakH2Neumann_cosineCoeffs_secondDeriv_eq
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {k : ℕ} (hk : 1 ≤ k) :
    cosineCoeffs hf.secondDeriv k =
      -((k : ℝ) * Real.pi) ^ 2 * cosineCoeffs f k := by
  have hk_ne : k ≠ 0 := by omega
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral
        (f := hf.secondDeriv) (n := k) hk_ne,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral
        (f := f) (n := k) hk_ne]
  rw [hf.weak_cosine_laplacian k]
  ring

end
end ShenWork.PDE.IntervalMildSourceDecayHelper
```

If `rw` does not find the exact integral subterm, use explicit `have` bindings:

```lean
  have hsd := ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral
    (f := hf.secondDeriv) (n := k) hk_ne
  have hf0 := ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral
    (f := f) (n := k) hk_ne
  rw [hsd, hf0, hf.weak_cosine_laplacian k]
  ring
```

## Why this proves your desired statement

`IntervalWeakH2Neumann` contains exactly the raw integral identity:

```lean
weak_cosine_laplacian : ∀ k : ℕ,
  (∫ x in (0 : ℝ)..1,
      Real.cos ((k : ℝ) * Real.pi * x) * secondDeriv x) =
    -((k : ℝ) * Real.pi) ^ 2 *
      ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
```

- `ShenWork/PDE/IntervalMildSourceDecayHelper.lean:6-15`

The positive-mode lemma turns both raw integrals into normalized coefficients with the same factor `2`, and `ring` cancels/distributes that factor:

```lean
2 * (-(kπ)^2 * raw_f) = -(kπ)^2 * (2 * raw_f)
```
