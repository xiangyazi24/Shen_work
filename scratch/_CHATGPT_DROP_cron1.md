# Q1848 (cron1) -- `tsum` closure for the `heatDu` tail bound

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was only:

```text
Q1848 (cron1): cron1 /tmp/q_cron1_tsum.txt
```

The local file `/tmp/q_cron1_tsum.txt` was not present in the runtime I can inspect, and it is not readable through the GitHub connector. I used the current repository state plus the previous `srcSlice1`/`heatDu_tail_linf_bound` context to infer the intended target.

I did **not** use Python, `/mnt/data`, the sandbox, or a sandbox link. I did not run Lean locally.

## Inferred target

The immediate target is the `tsum` part of the proposed helper:

```lean
private theorem heatDu_tail_linf_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ∃ CΔ : ℝ, 0 ≤ CΔ ∧
      ∀ t : ℝ, c + 1 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |heatDu u₀ t x| ≤ CΔ
```

from Q1833.  The pain point is the final step after defining

```lean
term n = unitIntervalCosineHeatSecondPointWeight t x n *
  cosineCoeffs (intervalDomainLift u₀) n

maj n = Cbase * M₀ * reciprocalSquareTerm n
```

and proving:

```lean
hterm_abs : ∀ n, |term n| ≤ maj n
hmaj_summable : Summable maj
```

You want a robust Lean way to conclude:

```lean
|∑' n, term n| ≤ ∑' n, maj n
```

and then rewrite the RHS to the concrete constant.

## Main advice

Do **not** inline `abs_tsum_le_tsum_abs` and `tsum_le_tsum` everywhere.  Add a local helper once:

```lean
private theorem abs_tsum_le_tsum_of_abs_le
```

Then the `heatDu_tail_linf_bound` proof only needs to provide a termwise majorant and summability of the majorant.

This avoids the usual elaboration fragility around:

```lean
abs_tsum_le_tsum_abs
norm_tsum_le_tsum_norm
tsum_le_tsum
```

and makes the proof readable.

## The reusable `tsum` helper

Add this near the `heatDu_tail_linf_bound` helper, in namespace
`ShenWork.Paper2.HeatResolverJointC2Direct`.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- If a real series is termwise dominated in absolute value by a summable
nonnegative majorant, then the absolute value of its `tsum` is bounded by the
`tsum` of the majorant.  This packages the common
`norm_tsum_le_tsum_norm` + `tsum_le_tsum` pattern. -/
private theorem abs_tsum_le_tsum_of_abs_le
    {f g : ℕ → ℝ}
    (hg_nonneg : ∀ n : ℕ, 0 ≤ g n)
    (hfg : ∀ n : ℕ, |f n| ≤ g n)
    (hg : Summable g) :
    |∑' n : ℕ, f n| ≤ ∑' n : ℕ, g n := by
  have hf : Summable f := by
    refine Summable.of_norm_bounded hg ?_
    intro n
    simpa [Real.norm_eq_abs] using hfg n
  have hfnorm : Summable fun n : ℕ => ‖f n‖ := hf.norm
  have hfabs : Summable fun n : ℕ => |f n| := by
    simpa [Real.norm_eq_abs] using hfnorm
  calc
    |∑' n : ℕ, f n| = ‖∑' n : ℕ, f n‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖f n‖ := by
      exact norm_tsum_le_tsum_norm hf
    _ = ∑' n : ℕ, |f n| := by
      congr 1
      ext n
      rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, g n := by
      exact tsum_le_tsum hfg hfabs hg

end ShenWork.Paper2.HeatResolverJointC2Direct
```

If your local Mathlib snapshot rejects the line

```lean
exact norm_tsum_le_tsum_norm hf
```

try the no-explicit-summability form:

```lean
      simpa using (norm_tsum_le_tsum_norm (f := f))
```

or the method form, if available:

```lean
      exact hf.norm_tsum_le
```

The rest of the helper is stable.  In recent Mathlib, one of those three names/forms is the standard API for `‖tsum f‖ ≤ tsum (‖f‖)`.

## The cleaned-up `heatDu_tail_linf_bound` tsum block

Inside `heatDu_tail_linf_bound`, after you have:

```lean
  let Cbase : ℝ := 4 / ((c + 1) ^ 2 * Real.pi ^ 2)
  let rec : ℕ → ℝ :=
    ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm
  let S : ℝ := ∑' n : ℕ, rec n
  let term : ℕ → ℝ := fun n =>
    ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n
  let maj : ℕ → ℝ := fun n => Cbase * M₀ * rec n
```

use this exact structure.

```lean
  have hrec_nonneg : ∀ n : ℕ, 0 ≤ rec n := by
    intro n
    dsimp [rec]
    unfold ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm
    positivity

  have hmaj_nonneg : ∀ n : ℕ, 0 ≤ maj n := by
    intro n
    dsimp [maj]
    positivity

  have hmaj_summable : Summable maj := by
    dsimp [maj, rec]
    simpa [mul_assoc] using
      (ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm_summable.mul_left
        (Cbase * M₀))

  have hterm_abs : ∀ n : ℕ, |term n| ≤ maj n := by
    intro n
    have hwt :=
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight_abs_le
        ht_pos x n
    have hcoeff : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ := hu₀_bound n
    have htime :
        4 / (t ^ 2 * Real.pi ^ 2) ≤ Cbase := by
      dsimp [Cbase]
      have htail_pos : 0 < c + 1 := by linarith
      have hsq : (c + 1) ^ 2 ≤ t ^ 2 := by
        nlinarith [htail_pos, le_of_lt ht]
      have hden : (c + 1) ^ 2 * Real.pi ^ 2 ≤ t ^ 2 * Real.pi ^ 2 := by
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg Real.pi)
      have hden_pos : 0 < (c + 1) ^ 2 * Real.pi ^ 2 := by positivity
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hden_pos hden
    dsimp [term, maj, rec]
    rw [abs_mul]
    calc
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight t x n| *
          |cosineCoeffs (intervalDomainLift u₀) n|
          ≤ ((4 / (t ^ 2 * Real.pi ^ 2)) *
              ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n) * M₀ := by
            exact mul_le_mul hwt hcoeff hM₀_nonneg
              (mul_nonneg (by positivity)
                (hrec_nonneg n))
      _ ≤ (Cbase *
              ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n) * M₀ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right htime (hrec_nonneg n)) hM₀_nonneg
      _ = Cbase * M₀ *
            ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := by
            ring

  have hsum_bound : |∑' n : ℕ, term n| ≤ ∑' n : ℕ, maj n :=
    abs_tsum_le_tsum_of_abs_le hmaj_nonneg hterm_abs hmaj_summable
```

That is the robust replacement for the fragile inline block:

```lean
|∑' n, term n| ≤ ∑' n, |term n| ≤ ∑' n, maj n
```

## Rewriting the majorant `tsum`

Now rewrite the RHS with a separate lemma.  This avoids `simp` guessing the wrong direction for scalar multiplication.

```lean
  have hmaj_tsum : (∑' n : ℕ, maj n) = Cbase * M₀ * S := by
    calc
      (∑' n : ℕ, maj n)
          = ∑' n : ℕ, (Cbase * M₀) * rec n := by
              congr 1
              ext n
              dsimp [maj]
              ring
      _ = (Cbase * M₀) * (∑' n : ℕ, rec n) := by
              rw [tsum_mul_left]
      _ = Cbase * M₀ * S := by
              dsimp [S]
              ring
```

If `tsum_mul_left` rewrites in the opposite orientation in your local snapshot, use this variant:

```lean
      _ = (Cbase * M₀) * (∑' n : ℕ, rec n) := by
              simpa using (tsum_mul_left (a := Cbase * M₀) (f := rec)).symm
```

Depending on the exact theorem statement, the scalar argument might be called `c` instead of `a`; the positional version is usually safest:

```lean
              simpa using (tsum_mul_left (Cbase * M₀) rec).symm
```

## Final tail line

Once `hsum_bound` and `hmaj_tsum` are available, the tail line is just:

```lean
  calc
    |heatDu u₀ t x|
        = |∑' n : ℕ, term n| := by
            rw [heatDu_eq_secondValue u₀ ht_pos]
            unfold ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
            congr 1
            ext n
            dsimp [term]
    _ ≤ ∑' n : ℕ, maj n := hsum_bound
    _ = Cbase * M₀ * S := hmaj_tsum
```

If the first equality is already after `rw [heatDu_eq_secondValue ...]` and an `unfold`, use only the last two lines:

```lean
  calc
    |∑' n : ℕ, term n| ≤ ∑' n : ℕ, maj n := hsum_bound
    _ = Cbase * M₀ * S := hmaj_tsum
```

## Common compile pitfalls

### 1. `M₀` nonnegativity

You need this early:

```lean
have hM₀_nonneg : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
```

Without it, `mul_le_mul` and `hmaj_nonneg` will get stuck.

### 2. `Cbase` nonnegativity

After `let Cbase := 4 / ((c + 1)^2 * Real.pi^2)`, prove:

```lean
have hCbase_nonneg : 0 ≤ Cbase := by
  dsimp [Cbase]
  positivity
```

This helps `positivity` close `hmaj_nonneg`.

### 3. The time-denominator monotonicity

The core inequality is:

```lean
4 / (t ^ 2 * Real.pi ^ 2) ≤ 4 / ((c + 1) ^ 2 * Real.pi ^ 2)
```

from `c + 1 < t`.  The proof above uses `div_le_div_of_nonneg_left`; it needs the lower denominator positive.

If `div_le_div_of_nonneg_left` wants the denominator inequality in the other order in your snapshot, prove it by field simplification instead:

```lean
      have hden_pos : 0 < (c + 1) ^ 2 * Real.pi ^ 2 := by positivity
      have hden_t_pos : 0 < t ^ 2 * Real.pi ^ 2 := by positivity
      field_simp [hden_pos.ne', hden_t_pos.ne']
      nlinarith [hden]
```

### 4. Avoid `abs_tsum_le_tsum_abs` directly

It may elaborate differently across snapshots.  The local helper `abs_tsum_le_tsum_of_abs_le` isolates the API choice to one line.

## Bottom line

For Q1848, the correct `tsum` close is:

```lean
have hsum_bound : |∑' n : ℕ, term n| ≤ ∑' n : ℕ, maj n :=
  abs_tsum_le_tsum_of_abs_le hmaj_nonneg hterm_abs hmaj_summable

have hmaj_tsum : (∑' n : ℕ, maj n) = Cbase * M₀ * S := by
  calc
    (∑' n : ℕ, maj n) = ∑' n : ℕ, (Cbase * M₀) * rec n := by
      congr 1
      ext n
      dsimp [maj]
      ring
    _ = (Cbase * M₀) * (∑' n : ℕ, rec n) := by
      rw [tsum_mul_left]
    _ = Cbase * M₀ * S := by
      dsimp [S]
      ring
```

Use those two facts in `heatDu_tail_linf_bound`; then the rest of the `srcSlice1` coefficient bound is just continuity + pointwise bound + `cosineCoeffs_abs_le_of_continuous_bounded`.
