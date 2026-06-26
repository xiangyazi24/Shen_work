# Q774 (cron2): nonpositive-time full Neumann semigroup

Static repo inspection only; I did not run a Lean build.

## Answer

The repo does have the key **kernel-level** fact:

```lean
theorem heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    heatKernel t x = 0
```

File:

```text
ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean
```

The comment there says explicitly that Lean’s `Real.sqrt` returns `0` on nonpositive inputs, so the prefactor `1 / sqrt(4πt)` is `0`.  In Lean, real division by zero is totalized, so this avoids any complex/undefined issue.

The proof is:

```lean
unfold heatKernel
have h4t : 4 * Real.pi * t ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
rw [Real.sqrt_eq_zero'.mpr h4t]
simp
```

So for `s ≤ 0`, every image Gaussian in the full Neumann kernel is zero.

## Did I find `intervalFullSemigroupOperator_nonpos`?

I did **not** find a named, ready-made theorem with any of the requested operator-level names:

```text
intervalFullSemigroupOperator.*nonpos
semigroupOperator.*le_zero
S_nonpos
```

The closest confirmed primitive is the kernel theorem above, plus existing code patterns that use it to make lattice summands all zero in the nonpositive-time branch.

For example, in `IntervalMildPicard.lean`, the joint-measurability proof for the full kernel has the branch:

```lean
have hzero : (fun k : ℤ => g k q) = fun _ : ℤ => (0 : ℝ) := by
  funext k
  simp [hg_def, ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht]
rw [hzero]
exact summable_zero
```

and `IntervalFullKernelSDependentMeasurable.lean` has the same pattern for the `(t - s) ≤ 0` branch:

```lean
have hz : (fun k : ℤ => g k w) = fun _ : ℤ => (0 : ℝ) := by
  funext k
  simp only [hg_def, heatKernel_of_nonpos hτ, add_zero]
rw [hz]
exact summable_zero
```

So the repo already treats the full-kernel lattice summand as zero for nonpositive time, but I did not locate a public lemma directly stating:

```lean
intervalFullSemigroupOperator s f x = 0
```

for `s ≤ 0`.

## What you can prove if needed

The missing operator-level lemma should be straightforward from `heatKernel_of_nonpos`:

```lean
theorem intervalNeumannFullKernel_of_nonpos {t x y : ℝ} (ht : t ≤ 0) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  have hzero :
      (fun k : ℤ => heatKernel t (x - y + 2 * k) +
        heatKernel t (x + y + 2 * k)) = fun _ => (0 : ℝ) := by
    funext k
    simp [heatKernel_of_nonpos ht]
  rw [hzero]
  simp
```

Then:

```lean
theorem intervalFullSemigroupOperator_of_nonpos {t : ℝ} (ht : t ≤ 0)
    (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  simp [intervalNeumannFullKernel_of_nonpos ht]
```

The exact final `simp` may need the namespace-qualified theorem name, but mathematically this is the direct route: kernel zero pointwise → integrand zero → integral zero.

## Consequence for Level0

If the Level0 identity is really:

```lean
conjugatePicardIter p u₀ 0 s = picardIter p u₀ 0 s
picardIter p u₀ 0 s x = intervalFullSemigroupOperator s (intervalDomainLift u₀) x
```

then for `s ≤ 0`, the intended result should be:

```lean
conjugatePicardIter p u₀ 0 s x = 0
```

but the repo support I confirmed is one level below that: `heatKernel_of_nonpos` and the all-zero full-kernel lattice-summand pattern. I did not find a named all-in-one theorem `intervalFullSemigroupOperator_nonpos` / `S_nonpos` to cite directly.
