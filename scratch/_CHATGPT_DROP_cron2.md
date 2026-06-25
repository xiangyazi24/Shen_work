# Q584 (cron2): summability of `C / (max 1 k)^2`

## Executive verdict

On `chatgpt-scratch`, the exact definition is **not** the π-normalized version.  It is:

```lean
def reciprocalSquareTerm (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2
```

and the existing theorem is:

```lean
theorem reciprocalSquareTerm_summable : Summable reciprocalSquareTerm
```

The clean wiring for

```lean
Summable (fun k : ℕ => C / (max (1 : ℝ) (k : ℝ)) ^ 2)
```

is to drop the finite `k = 0` term with

```lean
rw [← summable_nat_add_iff (k := 1)]
```

Then the tail term at `k = n+1` satisfies

```lean
max (1 : ℝ) ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ)
```

so the tail is definitionally/algebraically

```lean
C / ((n + 1 : ℝ)^2) = C * reciprocalSquareTerm (n + 1)
```

and this is summable by

```lean
(reciprocalSquareTerm_summable.comp_injective (fun a b h => by omega)).mul_left C
```

Note: the assumption `0 ≤ C` is **not needed** for pure summability, since scalar multiples of summable series are summable for all real `C`.  It is useful only if you prove the result by nonnegative comparison.

## Exact repo definition

`ShenWork/PDE/IntervalDomainRegularityBootstrap.lean:117`

```lean
/-- Reciprocal-square summand controlling the second-derivative series. -/
def reciprocalSquareTerm (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2
```

`ShenWork/PDE/IntervalDomainRegularityBootstrap.lean:120`

```lean
theorem reciprocalSquareTerm_summable : Summable reciprocalSquareTerm := by
  change Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2)
  exact Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
```

Important consequence: `reciprocalSquareTerm 0 = 0`, because real division by zero gives `1 / 0 = 0`.  Your target sequence has value `C` at `k = 0`, because `max 1 0 = 1`.  So do **not** try a global pointwise comparison

```lean
C / (max 1 k)^2 ≤ C * reciprocalSquareTerm k
```

at `k = 0`; it is false when `0 < C`.  First throw away the finite initial term.

## Recommended theorem

This version is stronger than requested: no `0 ≤ C` hypothesis is needed.

```lean
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open ShenWork.IntervalDomainRegularityBootstrap

noncomputable section

/-- `∑ C / (max 1 k)^2` is summable.  The `k=0` term is finite, and the tail is
`C * reciprocalSquareTerm (k+1)`. -/
theorem summable_const_div_max_one_nat_sq (C : ℝ) :
    Summable (fun k : ℕ => C / (max (1 : ℝ) (k : ℝ)) ^ 2) := by
  -- Remove the finite initial term `k = 0`.
  rw [← summable_nat_add_iff (k := 1)]
  -- On the shifted tail, `max 1 (n+1) = n+1`, so the term is exactly
  -- `C * reciprocalSquareTerm (n+1)`.
  have htail :
      (fun n : ℕ => C / (max (1 : ℝ) ((n + 1 : ℕ) : ℝ)) ^ 2)
        = fun n : ℕ => C * reciprocalSquareTerm (n + 1) := by
    funext n
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simp [reciprocalSquareTerm, max_eq_right hn, mul_one_div]
  rw [htail]
  exact (reciprocalSquareTerm_summable.comp_injective
    (fun a b h => by omega)).mul_left C
```

If you want to keep the requested nonnegativity assumption in the theorem statement:

```lean
theorem summable_nonneg_const_div_max_one_nat_sq {C : ℝ} (_hC : 0 ≤ C) :
    Summable (fun k : ℕ => C / (max (1 : ℝ) (k : ℝ)) ^ 2) :=
  summable_const_div_max_one_nat_sq C
```

## If `omega` is undesirable

The only use of `omega` is to prove injectivity of `fun n => n + 1`.  You can replace it with a direct `Nat.succ` argument if Lean accepts the definitional shape in your file:

```lean
(reciprocalSquareTerm_summable.comp_injective
  (fun a b h => by exact Nat.succ.inj h)).mul_left C
```

If Lean sees `a + 1` rather than `Nat.succ a`, keep the `omega` version; that exact pattern already appears in the repo's indexed/default `ChemDivAdotEnvelope.lean`.

## Existing pattern in `ChemDivAdotEnvelope.lean` on the indexed/default branch

`ChemDivAdotEnvelope.lean` is currently 404 on `chatgpt-scratch`, but the indexed/default branch contains the same tail-shift pattern:

```lean
theorem adotEnvelope_summable {Cdot : ℝ} (hC : 0 ≤ Cdot) :
    Summable (adotEnvelope Cdot) := by
  rw [← summable_nat_add_iff (k := 1)]
  apply Summable.of_nonneg_of_le
  · intro n; exact adotEnvelope_nonneg hC (n + 1)
  · intro n
    show adotEnvelope Cdot (n + 1) ≤ Cdot * reciprocalSquareTerm (n + 1)
    simp only [adotEnvelope, Nat.succ_ne_zero, ↓reduceIte, reciprocalSquareTerm]
    have hn1_pos : (0 : ℝ) < (↑(n + 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.succ_pos n)
    have hden_pos : (0 : ℝ) < (↑(n + 1) : ℝ) ^ 2 := by positivity
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left hC hden_pos
    rw [mul_pow]
    have hpi_sq : (1 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    calc (↑(n + 1) : ℝ) ^ 2
        = (↑(n + 1) : ℝ) ^ 2 * 1 := by ring
      _ ≤ (↑(n + 1) : ℝ) ^ 2 * Real.pi ^ 2 := by
          exact mul_le_mul_of_nonneg_left hpi_sq (by positivity)
  · exact (reciprocalSquareTerm_summable.comp_injective
      (fun a b h => by omega)).mul_left Cdot
```

For your `max 1 k` sequence the comparison is even simpler than the `π` case: after shifting to `n+1`, there is no π denominator to compare away; it is just equality with `C * reciprocalSquareTerm (n+1)`.