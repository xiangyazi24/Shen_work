# Q1134 / cron1 — `ContDiffOn.smulRight` API for scalar derivative CLMs

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

from `lake-manifest.json`.

Mathlib files checked at that pinned rev:

```text
Mathlib/Analysis/Calculus/ContDiff/Comp.lean
Mathlib/Analysis/Calculus/ContDiff/Defs.lean
Mathlib/Analysis/Calculus/Deriv/Basic.lean
Mathlib/Analysis/Calculus/FDeriv/Basic.lean
Mathlib/Analysis/Normed/Operator/Bilinear.lean
Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean
```

The relevant API is:

```lean
ContDiffOn.smulRight
```

not `ContDiffOn.clm_comp`.  `clm_comp` is for composing two CLM-valued families; your expression is a rank-one/smulRight family produced from a constant dual functional and a scalar-valued `C¹` function.

## Exact answer for the subgoal

Given:

```lean
h0 : ContDiffOn ℝ 1 f₁ (Set.Ioi 0)
```

the exact term I would use is:

```lean
have hsmul :
    ContDiffOn ℝ 1
      (fun s : ℝ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₁ s))
      (Set.Ioi (0 : ℝ)) := by
  simpa using
    ((contDiffOn_const :
        ContDiffOn ℝ 1 (fun _ : ℝ => (1 : StrongDual ℝ ℝ))
          (Set.Ioi (0 : ℝ))).smulRight h0)
```

The key is that `ContDiffOn.smulRight` has the shape:

```lean
theorem ContDiffOn.smulRight
    {f : E → StrongDual 𝕜 F} {g : E → G}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => (f x).smulRight (g x)) s
```

So instantiate:

```lean
f := fun _ : ℝ => (1 : StrongDual ℝ ℝ)
g := f₁
```

Since `StrongDual ℝ ℝ` is definitionally `ℝ →L[ℝ] ℝ`, the result is definitionally the same as your target using

```lean
ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₁ s)
```

## Full local theorem for your situation

Here is the complete pattern for your three hypotheses:

```lean
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set
open scoped Topology ContDiff

example {f₀ f₁ : ℝ → ℝ}
    (h0 : ContDiffOn ℝ 1 f₁ (Set.Ioi (0 : ℝ)))
    (hd0_on : DifferentiableOn ℝ f₀ (Set.Ioi (0 : ℝ)))
    (heq0 : Set.EqOn (deriv f₀) f₁ (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 2 f₀ (Set.Ioi (0 : ℝ)) := by
  -- This is the requested API step.
  have hsmul :
      ContDiffOn ℝ 1
        (fun x : ℝ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₁ x))
        (Set.Ioi (0 : ℝ)) := by
    simpa using
      ((contDiffOn_const :
          ContDiffOn ℝ 1 (fun _ : ℝ => (1 : StrongDual ℝ ℝ))
            (Set.Ioi (0 : ℝ))).smulRight h0)

  -- Convert the `deriv f₀ = f₁` equality into the CLM-valued `fderivWithin` equality.
  have hfderiv :
      ContDiffOn ℝ 1
        (fun x : ℝ => fderivWithin ℝ f₀ (Set.Ioi (0 : ℝ)) x)
        (Set.Ioi (0 : ℝ)) := by
    refine hsmul.congr ?_
    intro x hx
    rw [fderivWithin_of_isOpen isOpen_Ioi hx]
    have hxderiv : deriv f₀ x = f₁ x := heq0 hx
    simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton, hxderiv] using
      (toSpanSingleton_deriv (𝕜 := ℝ) (f := f₀) (x := x)).symm

  -- `n = 1`, so the analytic side condition in `contDiffOn_succ_of_fderivWithin`
  -- is impossible and is discharged by `simp`.
  simpa using
    (contDiffOn_succ_of_fderivWithin
      (𝕜 := ℝ) (f := f₀) (s := Set.Ioi (0 : ℝ))
      (n := (1 : WithTop ℕ∞))
      hd0_on (by simp) hfderiv)
```

## If you specifically want the `smulRightL` version

Your attempt with `ContinuousLinearMap.smulRightL (1 : ℝ →L[ℝ] ℝ)` was close, but the argument order is different.  At the pinned Mathlib rev, `smulRightL` is the continuous trilinear map:

```lean
ContinuousLinearMap.smulRightL :
  StrongDual 𝕜 E →L[𝕜] F →L[𝕜] E →L[𝕜] F
```

So for this case, first specialize the three explicit parameters and then apply it to the constant dual functional:

```lean
have hsmul_alt :
    ContDiffOn ℝ 1
      (fun x : ℝ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₁ x))
      (Set.Ioi (0 : ℝ)) := by
  simpa using
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : StrongDual ℝ ℝ)).contDiff.comp_contDiffOn h0)
```

I would still use the `ContDiffOn.smulRight` version in production: it is shorter, clearer, and exactly matches the API theorem in `ContDiff/Comp.lean`.

## Minimal drop-in replacement

For just the subgoal in your existing proof, this should be enough:

```lean
  have h_fderiv_model :
      ContDiffOn ℝ 1
        (fun s : ℝ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₁ s))
        (Set.Ioi (0 : ℝ)) := by
    simpa using
      ((contDiffOn_const :
          ContDiffOn ℝ 1 (fun _ : ℝ => (1 : StrongDual ℝ ℝ))
            (Set.Ioi (0 : ℝ))).smulRight h0)
```

Then use `ContDiffOn.congr` to replace this model by `fderivWithin ℝ f₀ (Set.Ioi 0)` on the open set, as in the full theorem above.
