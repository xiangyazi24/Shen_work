# Q1253 / cron1 — fill `unitIntervalCosineEigenvalue_sq_exp_summable`

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Target

In `ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean`, replace the `sorry` in:

```lean
local notation "λ_" n => unitIntervalCosineEigenvalue n

private theorem unitIntervalCosineEigenvalue_sq_exp_summable
    {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => (λ_ n) ^ 2 * Real.exp (-r * (λ_ n)) := by
  sorry
```

with the proof below.

The proof follows the requested route exactly:

1. set `ρ = r * Real.pi ^ 2`;
2. use `Real.summable_pow_mul_exp_neg_nat_mul 4` at `ρ`;
3. rewrite `λ_ n = (n : ℝ)^2 * Real.pi^2`;
4. use `(n : ℝ) ≤ (n : ℝ)^2` for naturals;
5. dominate
   `((λ_ n)^2) * exp (-r * λ_ n)` by
   `Real.pi^4 * ((n : ℝ)^4 * exp (-ρ * n))`.

## Full Lean code

Standalone check imports are included.  If pasting directly into `IntervalHeatSemigroupFlooredSourceTimeData.lean`, the imports are already present upstream enough in the current file; paste only the theorem body/replacement.

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

local notation "λ_" n => unitIntervalCosineEigenvalue n

private theorem unitIntervalCosineEigenvalue_sq_exp_summable
    {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => (λ_ n) ^ 2 * Real.exp (-r * (λ_ n)) := by
  set ρ : ℝ := r * Real.pi ^ 2 with hρ_def
  have hρ : 0 < ρ := by
    rw [hρ_def]
    positivity
  have hbase : Summable fun n : ℕ =>
      Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 4 (r := ρ) hρ).mul_left
        (Real.pi ^ 4)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        have hmul : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
          mul_nonneg hn0 (sub_nonneg.mpr hn1)
        nlinarith
    have hlam_eq : (λ_ n) = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hlam_sq_eq : (λ_ n) ^ 2 = (n : ℝ) ^ 4 * Real.pi ^ 4 := by
      rw [hlam_eq]
      ring
    have hexp_le :
        Real.exp (-r * (λ_ n)) ≤ Real.exp (-ρ * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hmul : ρ * (n : ℝ) ≤ ρ * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hn_sq_ge hρ.le
      rw [hlam_eq, hρ_def] at hmul ⊢
      nlinarith
    calc
      (λ_ n) ^ 2 * Real.exp (-r * (λ_ n))
          = ((n : ℝ) ^ 4 * Real.pi ^ 4) * Real.exp (-r * (λ_ n)) := by
              rw [hlam_sq_eq]
      _ ≤ ((n : ℝ) ^ 4 * Real.pi ^ 4) * Real.exp (-ρ * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by
            ring

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

## Minimal replacement body only

```lean
  set ρ : ℝ := r * Real.pi ^ 2 with hρ_def
  have hρ : 0 < ρ := by
    rw [hρ_def]
    positivity
  have hbase : Summable fun n : ℕ =>
      Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 4 (r := ρ) hρ).mul_left
        (Real.pi ^ 4)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        have hmul : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
          mul_nonneg hn0 (sub_nonneg.mpr hn1)
        nlinarith
    have hlam_eq : (λ_ n) = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hlam_sq_eq : (λ_ n) ^ 2 = (n : ℝ) ^ 4 * Real.pi ^ 4 := by
      rw [hlam_eq]
      ring
    have hexp_le :
        Real.exp (-r * (λ_ n)) ≤ Real.exp (-ρ * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hmul : ρ * (n : ℝ) ≤ ρ * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hn_sq_ge hρ.le
      rw [hlam_eq, hρ_def] at hmul ⊢
      nlinarith
    calc
      (λ_ n) ^ 2 * Real.exp (-r * (λ_ n))
          = ((n : ℝ) ^ 4 * Real.pi ^ 4) * Real.exp (-r * (λ_ n)) := by
              rw [hlam_sq_eq]
      _ ≤ ((n : ℝ) ^ 4 * Real.pi ^ 4) * Real.exp (-ρ * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = Real.pi ^ 4 * ((n : ℝ) ^ 4 * Real.exp (-ρ * (n : ℝ))) := by
            ring
```

## Notes

* The `n = 0` case in `hn_sq_ge` is handled separately; for `n > 0`, `1 ≤ (n : ℝ)` gives `n ≤ n^2`.
* The exponential comparison is the monotonicity of `Real.exp` applied to `-r * λ_n ≤ -ρ * n`, which follows from `ρ * n ≤ ρ * n^2` after expanding `ρ` and `λ_n`.
* This drop was produced via the GitHub connector only; no local `lake build` was run.
