# Q1142 / cron1 — `toSpanSingleton`, `fderivWithin`, and `ContDiffOn` on `Ioi 0`

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Source/version checked

The project pins Mathlib to Lean/Mathlib `v4.29.1`, with Mathlib rev:

```text
5e932f97dd25535344f80f9dd8da3aab83df0fe6
```

Relevant Mathlib files checked:

```text
Mathlib/Analysis/Calculus/ContDiff/Comp.lean
Mathlib/Analysis/Calculus/ContDiff/Defs.lean
Mathlib/Analysis/Calculus/ContDiff/Deriv.lean
Mathlib/Analysis/Calculus/Deriv/Basic.lean
Mathlib/Analysis/Calculus/FDeriv/Basic.lean
Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean
```

The short answer is: **use `ContinuousLinearMap.toSpanSingletonCLE`**, or equivalently use `ContDiffOn.smulRight` plus `ContinuousLinearMap.smulRight_one_eq_toSpanSingleton`.

There is no need to make `ContinuousLinearMap.toSpanSingleton ℝ` itself look like a `ContinuousLinearMap`.  Mathlib packages that map as a continuous linear equivalence:

```lean
(ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ))
```

This is the direct left-composition object for `ContDiffOn`.

## Exact term for the `ContDiffOn 0` `toSpanSingleton` goal

Given

```lean
hc2_on : ContinuousOn f₂ (Set.Ioi (0 : ℝ))
```

use:

```lean
have h2_toSpan :
    ContDiffOn ℝ 0
      (fun s : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (f₂ s))
      (Set.Ioi (0 : ℝ)) := by
  simpa [Function.comp_def] using
    (((ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ))).comp_contDiffOn_iff.mpr
      (show ContDiffOn ℝ 0 f₂ (Set.Ioi (0 : ℝ)) from
        contDiffOn_zero.mpr hc2_on))
```

This is the cleanest answer to the blocker.  `toSpanSingletonCLE` is the bundled continuous linear equivalence whose forward map is `fun x => ContinuousLinearMap.toSpanSingleton ℝ x`.

## Exact term for the `ContDiffOn 1` `toSpanSingleton` goal

Given

```lean
h1_on : ContDiffOn ℝ 1 f₁ (Set.Ioi (0 : ℝ))
```

use:

```lean
have h1_toSpan :
    ContDiffOn ℝ 1
      (fun s : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (f₁ s))
      (Set.Ioi (0 : ℝ)) := by
  simpa [Function.comp_def] using
    (((ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ))).comp_contDiffOn_iff.mpr
      h1_on)
```

## Equivalent `smulRight` version

The same two goals can also be proved using `ContDiffOn.smulRight`, since

```lean
(1 : ℝ →L[ℝ] ℝ).smulRight x = ContinuousLinearMap.toSpanSingleton ℝ x
```

by `ContinuousLinearMap.smulRight_one_eq_toSpanSingleton`.

For `ContDiffOn 0`:

```lean
have h2_toSpan_smulRight :
    ContDiffOn ℝ 0
      (fun s : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (f₂ s))
      (Set.Ioi (0 : ℝ)) := by
  simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using
    ((contDiffOn_const :
        ContDiffOn ℝ 0 (fun _ : ℝ => (1 : StrongDual ℝ ℝ))
          (Set.Ioi (0 : ℝ))).smulRight
      (show ContDiffOn ℝ 0 f₂ (Set.Ioi (0 : ℝ)) from
        contDiffOn_zero.mpr hc2_on))
```

For `ContDiffOn 1`:

```lean
have h1_toSpan_smulRight :
    ContDiffOn ℝ 1
      (fun s : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (f₁ s))
      (Set.Ioi (0 : ℝ)) := by
  simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using
    ((contDiffOn_const :
        ContDiffOn ℝ 1 (fun _ : ℝ => (1 : StrongDual ℝ ℝ))
          (Set.Ioi (0 : ℝ))).smulRight h1_on)
```

I would use the `toSpanSingletonCLE` version when the target is literally `toSpanSingleton`, and the `smulRight` version when your local derivative model is already written as `ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ...`.

## Full `fderivWithin` proof skeleton from `hd0`, `hd1`, `hc2_on`

This follows your intended two-step `contDiffOn_succ_of_fderivWithin` route.

```lean
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set
open scoped Topology ContDiff

example {f₀ f₁ f₂ : ℝ → ℝ}
    (hd0 : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f₀ (f₁ s) s)
    (hd1 : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f₁ (f₂ s) s)
    (hc2_on : ContinuousOn f₂ (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 2 f₀ (Set.Ioi (0 : ℝ)) := by
  let U : Set ℝ := Set.Ioi (0 : ℝ)
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

  -- First prove `f₁` is `C¹` on `U`.
  have h1_on : ContDiffOn ℝ 1 f₁ U := by
    have hd1_on : DifferentiableOn ℝ f₁ U := by
      intro x hx
      exact (hd1 x (by simpa [U] using hx)).differentiableAt.differentiableWithinAt

    have h2_toSpan :
        ContDiffOn ℝ 0
          (fun x : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (f₂ x)) U := by
      simpa [U, Function.comp_def] using
        (((ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ))).comp_contDiffOn_iff.mpr
          (show ContDiffOn ℝ 0 f₂ (Set.Ioi (0 : ℝ)) from
            contDiffOn_zero.mpr hc2_on))

    have hfd1 :
        ContDiffOn ℝ 0
          (fun x : ℝ => fderivWithin ℝ f₁ U x) U := by
      refine h2_toSpan.congr ?_
      intro x hx
      rw [fderivWithin_of_isOpen hUopen hx]
      rw [← toSpanSingleton_deriv (𝕜 := ℝ) (f := f₁) (x := x)]
      congr
      exact (hd1 x (by simpa [U] using hx)).deriv

    simpa using
      (contDiffOn_succ_of_fderivWithin
        (𝕜 := ℝ) (f := f₁) (s := U) (n := (0 : WithTop ℕ∞))
        hd1_on (by simp) hfd1)

  -- Now prove `f₀` is `C²` on `U`.
  have hd0_on : DifferentiableOn ℝ f₀ U := by
    intro x hx
    exact (hd0 x (by simpa [U] using hx)).differentiableAt.differentiableWithinAt

  have h1_toSpan :
      ContDiffOn ℝ 1
        (fun x : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (f₁ x)) U := by
    simpa [U, Function.comp_def] using
      (((ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ))).comp_contDiffOn_iff.mpr
        h1_on)

  have hfd0 :
      ContDiffOn ℝ 1
        (fun x : ℝ => fderivWithin ℝ f₀ U x) U := by
    refine h1_toSpan.congr ?_
    intro x hx
    rw [fderivWithin_of_isOpen hUopen hx]
    rw [← toSpanSingleton_deriv (𝕜 := ℝ) (f := f₀) (x := x)]
    congr
    exact (hd0 x (by simpa [U] using hx)).deriv

  simpa [U] using
    (contDiffOn_succ_of_fderivWithin
      (𝕜 := ℝ) (f := f₀) (s := U) (n := (1 : WithTop ℕ∞))
      hd0_on (by simp) hfd0)
```

The key conversion inside the `congr` blocks is:

```lean
rw [fderivWithin_of_isOpen hUopen hx]
rw [← toSpanSingleton_deriv (𝕜 := ℝ) (f := f₁) (x := x)]
congr
exact (hd1 x hx).deriv
```

and similarly for `f₀`.  This avoids using `HasDerivAt.hasFDerivAt.fderiv` directly; it uses the stable scalar derivative theorem

```lean
toSpanSingleton_deriv :
  ContinuousLinearMap.toSpanSingleton 𝕜 (deriv f x) = fderiv 𝕜 f x
```

plus `HasDerivAt.deriv`.

## Even shorter one-dimensional route

Since your domain is open and the functions are scalar one-dimensional, `Mathlib/Analysis/Calculus/ContDiff/Deriv.lean` gives:

```lean
contDiffOn_succ_iff_deriv_of_isOpen
```

This avoids `fderivWithin` and `toSpanSingleton` entirely.  The intended shape is:

```lean
have h1_on : ContDiffOn ℝ 1 f₁ (Set.Ioi (0 : ℝ)) := by
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, by simp, ?_⟩
  · intro x hx
    exact (hd1 x hx).differentiableAt.differentiableWithinAt
  · -- `deriv f₁ = f₂` on `Ioi 0`, so this is `ContDiffOn ℝ 0 f₂`.
    exact (contDiffOn_zero.mpr hc2_on).congr
      (fun x hx => (hd1 x hx).deriv.symm)
```

Then repeat once more for `f₀`, using `h1_on` as the derivative-side `ContDiffOn ℝ 1` input.  This is often the simplest proof in one-dimensional scalar problems.

## Bottom line

For the exact target you asked about, use either:

```lean
(((ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ))).comp_contDiffOn_iff.mpr
  (contDiffOn_zero.mpr hc2_on))
```

with `simpa [Function.comp_def]`, or the equivalent `smulRight` proof:

```lean
((contDiffOn_const :
    ContDiffOn ℝ 0 (fun _ : ℝ => (1 : StrongDual ℝ ℝ)) (Set.Ioi (0 : ℝ))).smulRight
  (contDiffOn_zero.mpr hc2_on))
```

with `simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]`.
