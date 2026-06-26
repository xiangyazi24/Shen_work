# Q816 (cron2) — `ContDiffAt` congruence under eventual equality

Static Mathlib source inspection only; I did not run a local Lean build.

Checked Mathlib source:

```text
leanprover-community/mathlib4 @ 11b908e5cdd941b2d54b1b2ab55d069f5d8281d4
Mathlib/Analysis/Calculus/ContDiff/Defs.lean
```

## Short answer

Yes. Mathlib has the theorem you want:

```lean
theorem ContDiffAt.congr_of_eventuallyEq
    (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
    ContDiffAt 𝕜 n f₁ x
```

So if your hypotheses are oriented as

```lean
hfg : f =ᶠ[𝓝 x] g
hf  : ContDiffAt ℝ n f x
```

then the usual proof is:

```lean
exact hf.congr_of_eventuallyEq hfg.symm
```

The theorem’s eventual-equality argument is oriented as **new function =ᶠ old function**. Since the target is `g` and the known smooth function is `f`, `hfg.symm : g =ᶠ[𝓝 x] f` is the right direction.

## Minimal example

```lean
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Filter
open scoped Topology ContDiff

example {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {f g : E → F} {x : E}
    (hfg : f =ᶠ[𝓝 x] g)
    (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n g x := by
  exact hf.congr_of_eventuallyEq hfg.symm
```

If your eventual equality is already oriented as

```lean
hg : g =ᶠ[𝓝 x] f
```

then use it directly:

```lean
exact hf.congr_of_eventuallyEq hg
```

## Related within-at lemmas

The within-at version exists too:

```lean
theorem ContDiffWithinAt.congr_of_eventuallyEq
    (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x
```

For `ContDiffWithinAt`, Mathlib also has convenience/equivalence variants:

```lean
theorem Filter.EventuallyEq.congr_contDiffWithinAt
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x

theorem ContDiffWithinAt.congr_of_eventuallyEq_insert
    (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) :
    ContDiffWithinAt 𝕜 n f₁ s x

theorem ContDiffWithinAt.congr_of_eventuallyEq_of_mem
    (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f₁ s x
```

I did **not** find/need a separate theorem named `Filter.EventuallyEq.congr_contDiffAt`; for the non-within case, `ContDiffAt.congr_of_eventuallyEq` is the direct theorem.
