# Q2599 (cron1) — Lean 4 / Mathlib v4.29 tactic sequences for interval integrals

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Answer summary

For problem (1), do not `rw` the affine-integral identity directly at the monotonicity inequality if binder names or pretty-printed interval binders are fighting you.  Prove the target-shape identity as a separate `have hR` with a `calc`, then close by transitivity:

```lean
exact le_trans hmono (le_of_eq hR)
```

For problem (2), do not use `linarith`.  The proof is exactly:

```lean
exact add_le_add h1 h2
```

or, if only parentheses/multiplication association differ:

```lean
simpa [mul_assoc] using add_le_add h1 h2
```

## Complete Lean code

```lean
import Mathlib

open MeasureTheory
open scoped Interval

noncomputable section

/-- Exact affine interval-integral identity.

This is the best way to avoid the bound-variable-renaming problem: prove the
identity in the exact target shape by `calc`, then use it by `le_of_eq` or
`rw [h_affine]` only at the final expression if needed.
-/
theorem intervalIntegral_const_mul_add_const_eq
    {a b eps C : ℝ} {G : ℝ → ℝ}
    (hG_int : IntervalIntegrable G volume a b) :
    (∫ s in a..b, eps * G s + C) =
      eps * (∫ s in a..b, G s) + (b - a) * C := by
  have hmul :
      (∫ s in a..b, eps * G s) = eps * (∫ s in a..b, G s) := by
    exact intervalIntegral.integral_const_mul eps G
  have hconst :
      (∫ _s in a..b, C) = (b - a) * C := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  calc
    (∫ s in a..b, eps * G s + C)
        = (∫ s in a..b, eps * G s) + ∫ _s in a..b, C := by
            exact intervalIntegral.integral_add
              (hG_int.const_mul eps) intervalIntegrable_const
    _ = eps * (∫ s in a..b, G s) + (b - a) * C := by
            rw [hmul, hconst]

/-- The special inequality in the question.

No `a ≤ b` hypothesis is needed here because this is just the affine integral
identity followed by reflexive inequality.
-/
theorem intervalIntegral_const_mul_add_const_le
    {a b eps C : ℝ} {G : ℝ → ℝ}
    (hG_int : IntervalIntegrable G volume a b) :
    (∫ s in a..b, eps * G s + C) ≤
      eps * (∫ s in a..b, G s) + (b - a) * C := by
  exact le_of_eq (intervalIntegral_const_mul_add_const_eq
    (a := a) (b := b) (eps := eps) (C := C) (G := G) hG_int)

/-- General monotone version: if `F ≤ eps * G + C` on a non-reversed interval,
then integrate and rewrite the affine upper integral.

This is the tactic sequence to use when your real goal came from a pointwise
upper bound and `intervalIntegral.integral_mono_on`.
-/
theorem intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on'
    {a b eps C : ℝ} {F G : ℝ → ℝ}
    (hab : a ≤ b)
    (hF_int : IntervalIntegrable F volume a b)
    (hG_int : IntervalIntegrable G volume a b)
    (hpoint : ∀ s ∈ Set.Icc a b, F s ≤ eps * G s + C) :
    (∫ s in a..b, F s) ≤
      eps * (∫ s in a..b, G s) + (b - a) * C := by
  have hR_int : IntervalIntegrable (fun s => eps * G s + C) volume a b :=
    (hG_int.const_mul eps).add intervalIntegrable_const

  have hmono :
      (∫ s in a..b, F s) ≤ (∫ s in a..b, eps * G s + C) := by
    exact intervalIntegral.integral_mono_on hab hF_int hR_int hpoint

  have hR :
      (∫ s in a..b, eps * G s + C) =
        eps * (∫ s in a..b, G s) + (b - a) * C := by
    exact intervalIntegral_const_mul_add_const_eq
      (a := a) (b := b) (eps := eps) (C := C) (G := G) hG_int

  exact le_trans hmono (le_of_eq hR)

/-- Same general lemma, but with the affine expression itself as `F`.
This matches the literal problem statement while still exercising the
`integral_mono_on` chain. -/
theorem intervalIntegral_affine_le_via_integral_mono_on
    {a b eps C : ℝ} {G : ℝ → ℝ}
    (hab : a ≤ b)
    (hG_int : IntervalIntegrable G volume a b) :
    (∫ s in a..b, eps * G s + C) ≤
      eps * (∫ s in a..b, G s) + (b - a) * C := by
  have hR_int : IntervalIntegrable (fun s => eps * G s + C) volume a b :=
    (hG_int.const_mul eps).add intervalIntegrable_const
  exact
    intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on'
      (a := a) (b := b) (eps := eps) (C := C)
      (F := fun s => eps * G s + C) (G := G)
      hab hR_int hG_int
      (by
        intro s hs
        rfl)

/-- Problem (2): the opaque integral expression is harmless.  Do not use
`linarith`; `add_le_add` has exactly the right type. -/
theorem add_two_bounds_with_opaque_interval_integral
    {a t eps Gbar Tbar C M : ℝ} {G : ℝ → ℝ}
    (h1 : eps * (∫ s in a..t, G s) ≤ eps * Gbar)
    (h2 : (t - a) * (C * M) ≤ Tbar * (C * M)) :
    eps * (∫ s in a..t, G s) + (t - a) * (C * M) ≤
      eps * Gbar + Tbar * (C * M) := by
  exact add_le_add h1 h2

/-- Same proof, written as a `calc`, useful when the target is part of a longer
proof and you want to avoid typeclass/tactic search noise. -/
theorem add_two_bounds_with_opaque_interval_integral_calc
    {a t eps Gbar Tbar C M : ℝ} {G : ℝ → ℝ}
    (h1 : eps * (∫ s in a..t, G s) ≤ eps * Gbar)
    (h2 : (t - a) * (C * M) ≤ Tbar * (C * M)) :
    eps * (∫ s in a..t, G s) + (t - a) * (C * M) ≤
      eps * Gbar + Tbar * (C * M) := by
  calc
    eps * (∫ s in a..t, G s) + (t - a) * (C * M)
        ≤ eps * Gbar + (t - a) * (C * M) := by
            exact add_le_add_right h1 ((t - a) * (C * M))
    _ ≤ eps * Gbar + Tbar * (C * M) := by
            exact add_le_add_left h2 (eps * Gbar)

/-- Variant for the common parenthesization mismatch `(t-a)*C*M` versus
`(t-a)*(C*M)`.  `simpa [mul_assoc]` normalizes it after `add_le_add`. -/
theorem add_two_bounds_with_opaque_interval_integral_assoc
    {a t eps Gbar Tbar C M : ℝ} {G : ℝ → ℝ}
    (h1 : eps * (∫ s in a..t, G s) ≤ eps * Gbar)
    (h2 : (t - a) * C * M ≤ Tbar * C * M) :
    eps * (∫ s in a..t, G s) + (t - a) * (C * M) ≤
      eps * Gbar + Tbar * (C * M) := by
  simpa [mul_assoc] using add_le_add h1 h2

end
```

## Drop-in tactic sequences

### Problem (1), after `hmono`

If you already have

```lean
hmono : (∫ s in a..b, F s) ≤ (∫ s in a..b, eps * G s + C)
```

then use this exact sequence:

```lean
have hR :
    (∫ s in a..b, eps * G s + C) =
      eps * (∫ s in a..b, G s) + (b - a) * C := by
  have hmul :
      (∫ s in a..b, eps * G s) = eps * (∫ s in a..b, G s) := by
    exact intervalIntegral.integral_const_mul eps G
  have hconst :
      (∫ _s in a..b, C) = (b - a) * C := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  calc
    (∫ s in a..b, eps * G s + C)
        = (∫ s in a..b, eps * G s) + ∫ _s in a..b, C := by
            exact intervalIntegral.integral_add
              (hG_int.const_mul eps) intervalIntegrable_const
    _ = eps * (∫ s in a..b, G s) + (b - a) * C := by
            rw [hmul, hconst]

exact le_trans hmono (le_of_eq hR)
```

The important point is the final line: use `le_trans hmono (le_of_eq hR)` instead of rewriting `hmono` in place.

### Problem (2), exact close

```lean
exact add_le_add h1 h2
```

If the products differ only by association:

```lean
simpa [mul_assoc] using add_le_add h1 h2
```

If you want the no-surprises `calc` version:

```lean
calc
  eps * (∫ s in a..t, G s) + (t - a) * (C * M)
      ≤ eps * Gbar + (t - a) * (C * M) := by
          exact add_le_add_right h1 ((t - a) * (C * M))
  _ ≤ eps * Gbar + Tbar * (C * M) := by
          exact add_le_add_left h2 (eps * Gbar)
```
