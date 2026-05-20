# Shen_work — Current Task for Codex

## Build

```bash
~/.openclaw/workspace/scripts/remote-build.sh shen_work
~/.openclaw/workspace/scripts/remote-build.sh shen_work --file ShenWork/PDE/IntervalDomain.lean
```

NEVER run local `lake build`. Invariant: 0 sorry, BUILD OK.

## Task: Interval Semigroup Operator (Phase 4 of bounded-domain proposal)

File: `ShenWork/PDE/IntervalDomain.lean`

### What exists

The file already has:
- `intervalMeasure L := volume.restrict (Set.Icc 0 L)` — restricted Lebesgue measure
- `normalizedZerothReflectionKernel L t x y` — the reflected heat kernel (nonneg, integral=1, pointwise bound ≤ 1/√(4πt))
- `normalizedReflectedKernelIntegral_L1_Linfty_smoothing` — whole-line L1→L∞ bound
- `normalizedReflectedKernelOperator` — whole-line kernel operator with full API (nonneg, const, mono, bound, add, sub, contraction, smoothing)

### What to add

Define the **interval semigroup operator** and prove its key properties. This connects the whole-line kernel to the bounded-domain setting needed for Paper2.

#### 1. Definition

```lean
def intervalSemigroupOperator (L t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, normalizedZerothReflectionKernel L t x y * f y ∂ intervalMeasure L
```

#### 2. Restricted kernel integral ≤ 1

```lean
theorem normalizedZerothReflectionKernel_intervalIntegral_le_one
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤ 1
```

Proof sketch: `∫ K ∂ intervalMeasure = ∫ K in Icc 0 L ≤ ∫ K = 1` via `set_integral_le_integral` (K ≥ 0, K integrable) + `normalizedZerothReflectionKernel_integral`.

#### 3. Positivity preservation

```lean
theorem intervalSemigroupOperator_nonneg
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t f x
```

Proof: `integral_nonneg` (K ≥ 0, f ≥ 0).

#### 4. L1→L∞ smoothing

```lean
theorem intervalSemigroupOperator_L1_Linfty
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    ‖intervalSemigroupOperator L t f x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖f y‖ ∂ intervalMeasure L
```

Proof: same calc chain as `normalizedReflectedKernelIntegral_L1_Linfty_smoothing` but with `intervalMeasure` — `norm_integral_le_integral_norm`, `integral_mono_of_nonneg` (using pointwise bound), `integral_const_mul`. All these Mathlib lemmas work for arbitrary measures.

Key pattern for the pointwise bound step (needs beta-reduction):
```lean
· exact Filter.Eventually.of_forall fun y => by
    change ‖normalizedZerothReflectionKernel L t x y * f y‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖
    rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht L x y)]
    exact mul_le_mul_of_nonneg_right
      (normalizedZerothReflectionKernel_pointwise_bound ht L x y)
      (norm_nonneg _)
```

For integrability of the upper bound: `(hf_int.norm).smul (1 / Real.sqrt (4 * Real.pi * t))`.

#### 5. L∞ contraction

```lean
theorem intervalSemigroupOperator_Linfty_bound
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤ M
```

Proof: |∫ K f| ≤ ∫ K |f| ≤ M ∫ K ≤ M · 1 = M. Uses `normalizedZerothReflectionKernel_intervalIntegral_le_one`.

### Constraints

- 0 sorry, BUILD OK
- No axioms, no assumption structures
- Follow the naming pattern of the existing `normalizedReflectedKernelOperator_*` theorems
- Add theorems at the end of IntervalDomain.lean, before `end ShenWork.IntervalDomain`
- Run `rg -n "\bsorry\b" ShenWork --glob '*.lean'` after every edit
