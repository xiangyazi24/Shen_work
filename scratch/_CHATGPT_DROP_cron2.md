# Q774/Q770 (cron2) — Lean quick verification

Static repo/source inspection only; I did not run a Lean build.

## Q774 — `conjugatePicardIter p u₀ 0 s x` for `s ≤ 0`

### Bottom line

By definition in `ShenWork/Paper2/IntervalConjugatePicard.lean`,

```lean
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => ...
```

So the level-0 value is exactly

```lean
conjugatePicardIter p u₀ 0 s x
  = intervalFullSemigroupOperator s (intervalDomainLift u₀) x.1
```

For `s ≤ 0`, the intended value is therefore

```lean
conjugatePicardIter p u₀ 0 s x = 0
```

because the full Neumann kernel is zero at nonpositive time in the current Lean model.

### What the repo already has

The public kernel primitive is in

```text
ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean
```

```lean
/-- The heat kernel vanishes for non-positive time (Lean's `Real.sqrt` returns `0`
on non-positive inputs, so the prefactor `1/√(4πt)` is `0`). -/
theorem heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    heatKernel t x = 0 := by
  unfold heatKernel
  have h4t : 4 * Real.pi * t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  rw [Real.sqrt_eq_zero'.mpr h4t]
  simp
```

So Lean does not run into a complex-valued negative-time Gaussian here: `Real.sqrt` is totalized, `sqrt(nonpositive)=0`, and division by zero is totalized, making the prefactor zero.

I also found the exact operator-level statement, but it is **private** in

```text
ShenWork/Paper2/IntervalMildPicard.lean
```

```lean
private theorem intervalNeumannFullKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x y : ℝ) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  have hzero : (fun k : ℤ =>
      heatKernel t (x - y + 2 * (k : ℝ)) +
        heatKernel t (x + y + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
    funext k
    rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht,
      ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht]
    simp
  rw [hzero, tsum_zero]

private theorem intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  have hzero : (fun y : ℝ => intervalNeumannFullKernel t x y * f y) =
      fun _ : ℝ => (0 : ℝ) := by
    funext y
    rw [intervalNeumannFullKernel_of_nonpos ht x y]
    simp
  rw [hzero]
  simp
```

There is also a private derivative version immediately after it:

```lean
private theorem deriv_intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x = 0 := ...
```

### Answer to the search question

I did **not** find an exported/public theorem named like

```text
intervalFullSemigroupOperator_nonpos
intervalFullSemigroupOperator_of_nonpos
semigroupOperator_le_zero
S_nonpos
```

But the repo does contain the exact proof privately as

```lean
IntervalMildPicard.intervalFullSemigroupOperator_eq_zero_of_nonpos
```

modulo Lean's private-name hygiene. If the result is needed outside `IntervalMildPicard.lean`, promote/copy it to a public theorem in the full-kernel namespace, preferably near `heatKernel_of_nonpos`.

### Useful public lemma shape

```lean
namespace ShenWork.IntervalNeumannFullKernel

 theorem intervalNeumannFullKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x y : ℝ) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  have hzero :
      (fun k : ℤ =>
        heatKernel t (x - y + 2 * (k : ℝ)) +
          heatKernel t (x + y + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
    funext k
    rw [heatKernel_of_nonpos ht, heatKernel_of_nonpos ht]
    simp
  rw [hzero, tsum_zero]

 theorem intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  have hzero : (fun y : ℝ => intervalNeumannFullKernel t x y * f y) =
      fun _ : ℝ => (0 : ℝ) := by
    funext y
    rw [intervalNeumannFullKernel_of_nonpos ht x y]
    simp
  rw [hzero]
  simp

end ShenWork.IntervalNeumannFullKernel
```

Then the level-0 conjugate Picard fact is just:

```lean
theorem conjugatePicardIter_zero_of_nonpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {s : ℝ} (hs : s ≤ 0) (x : intervalDomainPoint) :
    conjugatePicardIter p u₀ 0 s x = 0 := by
  unfold conjugatePicardIter
  exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_eq_zero_of_nonpos
    hs (intervalDomainLift u₀) x.1
```

## Q770 — `Real.smoothTransition`, `smoothRightCutoff`, and support

### Bottom line

Mathlib **does** have the exact zero-side theorem for `Real.smoothTransition`:

```lean
@[simp]
nonrec theorem zero_iff_nonpos : smoothTransition x = 0 ↔ x ≤ 0

theorem zero_of_nonpos (h : x ≤ 0) : smoothTransition x = 0 := zero_iff_nonpos.2 h
```

This is in

```text
Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean
```

So yes:

```lean
Real.smoothTransition x = 0
```

whenever `x ≤ 0`.

Mathlib also has:

```lean
theorem one_of_one_le (h : 1 ≤ x) : smoothTransition x = 1
@[simp] theorem eq_one_iff_one_le : smoothTransition x = 1 ↔ 1 ≤ x
@[fun_prop] protected theorem contDiff {n : ℕ∞} : ContDiff ℝ n smoothTransition
```

### No `HasCompactSupport` for `smoothTransition`

I found no `HasCompactSupport` or `tsupport_smoothTransition` theorem for `Real.smoothTransition`, and such a theorem would be mathematically false: `smoothTransition x = 1` for every `1 ≤ x`, so its support is unbounded to the right.

More precisely, using `zero_iff_nonpos`, the ordinary support is morally `(0, ∞)`, and the topological support is morally `[0, ∞)`, not compact.

So the correct reusable fact is the one-sided vanishing theorem, not compact support.

### Repo-local `smoothRightCutoff`

The repo definition is in

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

```lean
/-- Smooth right cutoff equal to `0` on `(-∞, c']` and `1` on `[c, ∞)`. -/
def smoothRightCutoff (c' c : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((c - c')⁻¹ * (t - c'))
```

The file already proves exactly the needed endpoint facts:

```lean
theorem smoothRightCutoff_eq_zero_of_le {c' c t : ℝ} (hc : c' < c)
    (ht : t ≤ c') :
    smoothRightCutoff c' c t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.2 (sub_pos.2 hc).le) (sub_nonpos.2 ht)

theorem smoothRightCutoff_eq_one_of_ge {c' c t : ℝ} (hc : c' < c)
    (ht : c ≤ t) :
    smoothRightCutoff c' c t = 1 := by
  ...

theorem smoothRightCutoff_eventually_eq_one {c' c s : ℝ}
    (hc : c' < c) (hs : c < s) :
    smoothRightCutoff c' c =ᶠ[𝓝 s] fun _ : ℝ => 1 := by
  ...
```

So for your concrete formula,

```lean
smoothRightCutoff c' c t = 0
```

when `c' < c` and `t ≤ c'`; that is already landed.

### No compact support for `smoothRightCutoff` either

`HasCompactSupport (smoothRightCutoff c' c)` is also false for the right cutoff, because `smoothRightCutoff c' c t = 1` for all `t ≥ c`. It is a smooth step/right cutoff, not a bump.

What you can prove/use instead is support containment/equality on the left side, e.g.

```lean
theorem smoothRightCutoff_support_subset {c' c : ℝ} (hc : c' < c) :
    Function.support (smoothRightCutoff c' c) ⊆ Set.Ioi c' := by
  intro t ht
  exact lt_of_not_ge fun hle => ht (smoothRightCutoff_eq_zero_of_le hc hle)
```

With `Real.smoothTransition.pos_of_pos`, one can strengthen this to `support = Set.Ioi c'` if useful.

### Derivatives / flatness

I did not find a ready-made Mathlib theorem named like “all derivatives of `smoothTransition` vanish on `(-∞, 0]`” or an exported flatness theorem for `expNegInvGlue`/`smoothTransition`.

For points strictly inside the constant regions, derivative-zero facts are local-constancy consequences. At the boundary (`0` for `smoothTransition`, `c'` for `smoothRightCutoff`), the flatness is what Mathlib proves internally to establish `ContDiff`, but I did not locate a separately packaged theorem for all iterated derivatives at the boundary.

Practical takeaway: use the existing value-level theorem

```lean
Real.smoothTransition.zero_of_nonpos
```

and the repo-local theorem

```lean
smoothRightCutoff_eq_zero_of_le
```

for support/value arguments. If a proof needs actual boundary derivative vanishing, expect to add a small local lemma rather than finding a named `tsupport`/`HasCompactSupport` fact.
