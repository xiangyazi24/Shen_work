# Q1311 / cron1 — `deriv g_smooth 0 = 0` for an even cosine series power

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

Do **not** prove this by differentiating the `tsum` unless you specifically need the derivative formula for another reason.  In the current file, the shortest Lean route is already the pattern being used elsewhere:

```lean
even + differentiable/ContDiff 1  ⟹  derivative is odd  ⟹  derivative at 0 is 0
```

For your concrete

```lean
set g_smooth := fun x => p.ν * U_cos x ^ p.γ with hg_smooth_def
```

you already prove

```lean
have hg_C4 : ContDiff ℝ 4 g_smooth := ...
have hg_even : ∀ x, g_smooth (-x) = g_smooth x := by
  intro x
  simp only [hg_smooth_def, hU_even]
```

Then the endpoint boundary condition is simply:

```lean
have hg'_bc0 : deriv g_smooth 0 = 0 := by
  have hodd : ∀ x, deriv g_smooth (-x) = -(deriv g_smooth x) := by
    intro x
    have h1 := deriv_comp_neg (f := g_smooth) (x := x)
    rw [show (fun x => g_smooth (-x)) = g_smooth from funext hg_even] at h1
    linarith
  have h0 := hodd 0
  rw [neg_zero] at h0
  linarith
```

This avoids the chain rule, avoids the `rpow` derivative API, and avoids any `hasDerivAt_tsum` / uniform summability obligation.  It is exactly the same mathematical fact: an even `C¹` function has zero derivative at the origin.

## Reusable helper to add/extract

This helper is the right abstraction to put near the other Paper2 parity utilities, or locally in `IntervalConjugateLevel0BFormSourceOn.lean` if you want minimal surgery.

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open Set Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

/-- Derivative of an even real function is odd.

The `ContDiff` hypothesis is mathematically the differentiability guarantee.  The proof uses
Mathlib's `deriv_comp_neg`; the hypothesis is not syntactically consumed because `deriv` is
Lean's total derivative operator, but keep it in the theorem statement so callers record the
real analytic reason this rewrite is valid in the intended setting. -/
theorem deriv_even_odd_of_contDiff_one {g : ℝ → ℝ}
    (_hg : ContDiff ℝ 1 g)
    (heven : ∀ x : ℝ, g (-x) = g x) :
    ∀ x : ℝ, deriv g (-x) = -(deriv g x) := by
  intro x
  have h1 := deriv_comp_neg (f := g) (x := x)
  rw [show (fun x : ℝ => g (-x)) = g from funext heven] at h1
  linarith

/-- An even `C¹` real function has zero derivative at `0`. -/
theorem deriv_even_at_zero_eq_zero {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g)
    (heven : ∀ x : ℝ, g (-x) = g x) :
    deriv g 0 = 0 := by
  have hodd := deriv_even_odd_of_contDiff_one hg heven
  have h0 := hodd 0
  rw [neg_zero] at h0
  linarith

end ShenWork.Paper2
```

Then your local proof becomes just:

```lean
have hg'_bc0 : deriv g_smooth 0 = 0 :=
  ShenWork.Paper2.deriv_even_at_zero_eq_zero
    (hg_C4.of_le (by norm_num)) hg_even
```

## Directly for `U_cos` itself

If what you need is explicitly `U_cos' 0 = 0`, use the same helper before forming `g_smooth`:

```lean
have hU'_zero : deriv U_cos 0 = 0 :=
  ShenWork.Paper2.deriv_even_at_zero_eq_zero
    (hU_C4.of_le (by norm_num)) hU_even
```

This is stronger and cleaner than proving a termwise derivative formula.  The cosine-series content is used only to prove `hU_even` and `hU_C4`; once those are available, the boundary derivative is a pure parity fact.

If `hU_even` is not already in scope, for a raw cosine synthesis of the form

```lean
U_cos x = ∑' k, a k * cosineMode k x
```

you usually prove it by `tsum_congr` and `cos(-θ)=cos θ`:

```lean
have hU_even : ∀ x, U_cos (-x) = U_cos x := by
  intro x
  simp only [hU_cos_def]
  exact tsum_congr (fun k => by
    congr 1
    unfold ShenWork.CosineSpectrum.cosineMode
    rw [show (k : ℝ) * Real.pi * (-x) = -((k : ℝ) * Real.pi * x) by ring]
    rw [Real.cos_neg])
```

The exact unfolding name may be `hU_cos_def` in your local block, as in the surrounding `U_cos` proof.

## Why the `tsum` derivative route is the wrong local proof

The repo already has the per-mode facts in `ShenWork/PDE/CosineSpectrum.lean`:

```lean
theorem ShenWork.CosineSpectrum.cosineMode_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (cosineMode n)
      (-((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * x)) x

theorem ShenWork.CosineSpectrum.cosineMode_deriv (n : ℕ) (x : ℝ) :
    deriv (cosineMode n) x =
      -((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * x)

theorem ShenWork.CosineSpectrum.cosineMode_neumann_left (n : ℕ) :
    deriv (cosineMode n) 0 = 0
```

So, termwise, every cosine mode has zero derivative at `0`.  For a single term:

```lean
have hterm0 : ∀ k, deriv (fun x : ℝ => a k * ShenWork.CosineSpectrum.cosineMode k x) 0 = 0 := by
  intro k
  have h := (ShenWork.CosineSpectrum.cosineMode_hasDerivAt k 0).const_mul (a k)
  simpa [ShenWork.CosineSpectrum.cosineMode] using h.deriv
```

But to conclude

```lean
deriv (fun x => ∑' k, a k * cosineMode k x) 0 = ∑' k, 0
```

you need a `HasDerivAt.tsum` / `hasDerivAt_tsum` theorem plus a summable dominating family for derivatives in a neighborhood of `0`.  That is exactly the kind of termwise-differentiation obligation that the repo tries to avoid unless it is genuinely needed.  Here it is unnecessary because parity gives the endpoint derivative for free once you have global `C¹` and evenness.

## Patch at the current `g_smooth` site

In `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, the local block currently has helpers like this:

```lean
have deriv_even_odd : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g →
    (∀ x, g (-x) = g x) → ∀ x, deriv g (-x) = -(deriv g x) := by
  intro g _hg heven x
  have h1 := deriv_comp_neg (f := g) (x := x)
  rw [show (fun x => g (-x)) = g from funext heven] at h1
  linarith

have odd_zero : ∀ {g : ℝ → ℝ}, (∀ x, g (-x) = -(g x)) → g 0 = 0 := by
  intro g hodd
  have h := hodd 0
  rw [neg_zero] at h
  linarith
```

Then it proves higher endpoint facts by:

```lean
have hg'_odd : ∀ x, deriv g_smooth (-x) = -(deriv g_smooth x) :=
  deriv_even_odd (hg_C4.of_le (by norm_num)) hg_even
```

For the first derivative boundary value, just add:

```lean
have hg'_bc0 : deriv g_smooth 0 = 0 :=
  odd_zero hg'_odd
```

or use the reusable helper above directly.

## Minimal answer

For `U_cos`:

```lean
have hU'_zero : deriv U_cos 0 = 0 := by
  have hodd : ∀ x, deriv U_cos (-x) = -(deriv U_cos x) := by
    intro x
    have h1 := deriv_comp_neg (f := U_cos) (x := x)
    rw [show (fun x => U_cos (-x)) = U_cos from funext hU_even] at h1
    linarith
  have h0 := hodd 0
  rw [neg_zero] at h0
  linarith
```

For `g_smooth`:

```lean
have hg'_bc0 : deriv g_smooth 0 = 0 := by
  have hodd : ∀ x, deriv g_smooth (-x) = -(deriv g_smooth x) := by
    intro x
    have h1 := deriv_comp_neg (f := g_smooth) (x := x)
    rw [show (fun x => g_smooth (-x)) = g_smooth from funext hg_even] at h1
    linarith
  have h0 := hodd 0
  rw [neg_zero] at h0
  linarith
```

This is the robust Lean proof.  The `tsum` derivative computation is mathematically true under the right summability hypotheses, but it is the wrong proof obligation here.

No local `lake build` was run; this drop was produced through the GitHub connector only.
