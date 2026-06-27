# Q1101 (cron3): Can 1A / 2A-sup be proved from pointwise `ContDiffAt` only?

## Verdict

Not from pointwise `ContDiffAt` alone.

The compactness step is easy **after** you have a closed-slab `ContinuousOn` theorem. But the proposed shortcut

```text
smooth on [c,T] × (0,1)
+ value is 0 at x = 0,1
⇒ extend by 0 to [c,T] × [0,1]
⇒ continuous on compact
⇒ bounded
```

is missing the essential middle proof: **continuity at the spatial boundary**. Boundary values alone do not imply the interior values tend to those boundary values. A toy counterexample is `f(s,x) = 1/x` on `x > 0`, with `f(s,0) = 0`: smooth on the open strip and zero at the boundary, but unbounded and discontinuous at the boundary.

So:

* For **2A-sup**, a compactness proof is sound if you first prove a closed-slab continuous extension of the source field. It need not be a separate “spectral representative” object, but it must give the same mathematical content: `ContinuousOn F (Icc c T ×ˢ Icc 0 1)` for a single field `F` agreeing with the source on the slab.
* For **1A**, the situation is stricter: you need a closed-slab continuous representative for the relevant second-derivative field, or an explicit uniform estimate. Pointwise existence of second derivatives / pointwise `ContDiffAt` does not give a uniform bound for the chosen `IntervalWeakH2Neumann.secondDeriv` across `s ∈ [c,T]`.

The current closed-slab representative strategy is not overkill for these targets; it is exactly what supplies the missing boundary continuity and a single jointly continuous field to compactify.

## Relevant repo context

In `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, the Level0 envelope theorem is:

```lean
theorem level0_chemDiv_envelope_summable
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ (envelope : ℕ → ℝ),
      Summable envelope ∧
      ∀ s ∈ Icc c T, ∀ n,
        |coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s n| ≤ envelope n
```

Inside it, the first block for 1A is explicitly:

```lean
have hH2 : ∃ (B : ℝ), 0 ≤ B ∧
    ∀ s ∈ Icc c T,
      ∃ (h2 : IntervalWeakH2Neumann
        (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)),
      (∫ x in (0 : ℝ)..1, |h2.secondDeriv x|) ≤ B := by
  -- ... uniform L¹ bound over [c,T] uses compactness + continuity of s ↦ f''_s
  sorry
```

That comment is accurate: compactness helps only after producing a continuous or otherwise uniformly bounded representative for the second derivative.

The structure providing the second derivative is:

```lean
structure IntervalWeakH2Neumann (f : ℝ → ℝ) where
  secondDeriv : ℝ → ℝ
  second_intervalIntegrable : IntervalIntegrable secondDeriv volume (0 : ℝ) 1
  second_abs_integral_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∫ x in (0 : ℝ)..1, |secondDeriv x| ≤ B
  weak_cosine_laplacian : ∀ k : ℕ,
    (∫ x in (0 : ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * secondDeriv x) =
      -((k : ℝ) * Real.pi) ^ 2 *
        ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
```

So for 1A, a pointwise `ContDiffAt` proof of the source does not identify a single `D2 : ℝ × ℝ → ℝ` that equals `h2.secondDeriv` for all `s` and is continuous/bounded on the closed slab.

## Exact Mathlib names: compact + continuous ⇒ bounded

The main theorem is:

```lean
IsCompact.exists_bound_of_continuousOn
```

Shape:

```lean
lemma IsCompact.exists_bound_of_continuousOn
    [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    {f : α → E} (hf : ContinuousOn f s) :
    ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C
```

For closed rectangles in `ℝ × ℝ`, use:

```lean
isCompact_Icc
IsCompact.prod
```

Typical construction:

```lean
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

open Set Topology

noncomputable section

example {c T : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Icc c T ×ˢ Icc (0 : ℝ) 1)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1, |F (s, x)| ≤ B := by
  have hK : IsCompact (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro s hs x hx
  have hq : (s, x) ∈ Icc c T ×ˢ Icc (0 : ℝ) 1 := by
    exact mem_prod.mpr ⟨hs, hx⟩
  have hnorm : ‖F (s, x)‖ ≤ C := hC (s, x) hq
  have habs : |F (s, x)| ≤ C := by
    simpa [Real.norm_eq_abs] using hnorm
  exact habs.trans (le_max_left C 0)
```

Useful equivalent/adjacent theorem names:

```lean
IsCompact.image_of_continuousOn
Bornology.IsBounded.exists_norm_le
IsCompact.bddAbove_image
IsCompact.exists_isMaxOn
```

The most direct one for a norm bound is still:

```lean
IsCompact.exists_bound_of_continuousOn
```

## What must be proved before the compactness step

For the compactness argument to apply to 2A-sup, you need a theorem of this shape:

```lean
let K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
let F : ℝ × ℝ → ℝ :=
  fun q => coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) q.1 q.2

have hF_closed : ContinuousOn F K := by
  -- not implied by interior pointwise ContDiffAt + boundary values alone
  sorry
```

A possible proof plan is casewise:

```lean
have hInt : ContinuousOn F (Icc c T ×ˢ Ioo (0 : ℝ) 1) := by
  -- from pointwise smoothness / ContDiffAt on the interior
  sorry

have hLeft : ∀ s ∈ Icc c T, ContinuousWithinAt F K (s, 0) := by
  -- must prove F(t,x) → 0 as x → 0+ uniformly enough in the product nhdsWithin
  sorry

have hRight : ∀ s ∈ Icc c T, ContinuousWithinAt F K (s, 1) := by
  -- must prove F(t,x) → 0 as x → 1-
  sorry
```

Then assemble by unfolding `ContinuousOn` and case-splitting on `x = 0`, `x = 1`, or `x ∈ Ioo 0 1`. Useful continuity API names for this assembly:

```lean
ContinuousOn.continuousWithinAt
ContinuousAt.continuousWithinAt
continuousOn_of_forall_continuousAt
ContinuousWithinAt.congr_of_eventuallyEq
ContinuousWithinAt.congr
ContinuousOn.congr
ContinuousOn.mono
```

But the hard part is not the case split; it is `hLeft` and `hRight`. Those are exactly the boundary-continuity content that closed-slab representatives usually supply.

## Why boundary equality alone is insufficient

The proposed facts:

```lean
ContinuousOn F (Icc c T ×ˢ Ioo (0 : ℝ) 1)
∀ s ∈ Icc c T, F (s, 0) = 0
∀ s ∈ Icc c T, F (s, 1) = 0
```

are not enough to derive:

```lean
ContinuousOn F (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

because they say nothing about the limit of `F (s,x)` as `x → 0+` or `x → 1-`. A function can be smooth on the interior, have boundary value zero, and still blow up or oscillate near the boundary.

So the true replacement for a closed-slab representative is not “pointwise smooth + boundary zero”, but:

```lean
pointwise smooth on the interior
+ one-sided boundary continuity to the boundary values
```

In Lean terms, the missing target is exactly:

```lean
ContinuousWithinAt F (Icc c T ×ˢ Icc (0 : ℝ) 1) (s, 0)
ContinuousWithinAt F (Icc c T ×ˢ Icc (0 : ℝ) 1) (s, 1)
```

for every `s ∈ Icc c T`.

## Consequences for 2A-sup

The compact-bound route is sound if the goal is only a sup bound on the source value:

```lean
∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  |coupledChemDivSourceLift p u s x| ≤ B
```

but it requires the closed-slab continuous extension proof first. You do not necessarily need the heavyweight spectral `ChemDivMixedReprData`; any direct proof of `ContinuousOn F K` suffices.

However, if the current known input is only pointwise `ContDiffAt` on the open strip plus `hbdry_zero`, then the route is not complete.

## Consequences for 1A

For 1A, compactness is useful only after you have a single two-variable second-derivative representative:

```lean
D2 : ℝ × ℝ → ℝ
```

with:

```lean
ContinuousOn D2 (Icc c T ×ˢ Icc (0 : ℝ) 1)
∀ s ∈ Icc c T, D2 agrees with the `secondDeriv` chosen in the H² certificate
```

Then `IsCompact.exists_bound_of_continuousOn` gives:

```lean
∃ B, ∀ s ∈ Icc c T, ∀ x ∈ Icc 0 1, |D2 (s,x)| ≤ B
```

and the L¹ bound follows by integrating the constant bound on `[0,1]`:

```lean
∫ x in (0 : ℝ)..1, |D2 (s,x)| ≤ B
```

using standard interval-integral monotonicity (`intervalIntegral.integral_mono_on`) and `intervalIntegral.integral_const` / `simp` for the constant integral.

But pointwise `ContDiffAt` for each `(s,x)` does not provide such a jointly continuous `D2`, and the `IntervalWeakH2Neumann` structure stores a per-slice `secondDeriv` choice rather than a jointly controlled field. Thus 1A still needs either:

* a closed-slab representative for the second derivative, or
* a direct uniform analytic estimate that bypasses compactness.

## Bottom line

* **2A-sup:** Yes, compactness can prove the sup bound from a closed-slab `ContinuousOn` extension. No, pointwise `ContDiffAt` on the open strip plus boundary equality is not enough.
* **1A:** No, not from pointwise `ContDiffAt` alone. You need a joint second-derivative representative or direct uniform estimates.
* **Exact compact theorem:** use `IsCompact.exists_bound_of_continuousOn` with `isCompact_Icc.prod isCompact_Icc`; use `Real.norm_eq_abs` to convert norms on `ℝ` to absolute values.
