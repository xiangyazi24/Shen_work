# Q1719 (cron2): `i = 1` proof for `hA_global_bounds`

GitHub-connector only. I did not read the local `/tmp/q_cron2_i1proof.txt` file and did not run Lean locally. I inferred the target from `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`: inside `cutoffResolverMajorant_bddAbove_direct`, the local proof

```lean
have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
    ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
```

still has the `i = 1` branch as a `sorry`.

## Bottom line

The `i = 1` branch is just the two-term Leibniz bound for

```lean
A(t) = φ(t) * R(t)
```

where

```lean
φ t = smoothRightCutoff (c / 2) c t
R t = resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

Use the bound

```text
‖A' t‖ ≤ Φ₀ * Bt 1 k + Φ₁ * Bt 0 k
```

where `Φ₀` and `Φ₁` are the global cutoff derivative bounds and `Bt` comes from the physical resolver data.

## Required setup before `hA_global_bounds`

Add this before entering `hA_global_bounds`:

```lean
obtain ⟨Bt, Hphys⟩ :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hu₀_pos
```

Also, if possible, define `A` with a named equation:

```lean
set A := fun t : ℝ =>
  smoothRightCutoff (c / 2) c t *
    resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
  with hA_def
```

If the file already has `set A := ...` without `with hA_def`, either add the `with hA_def`, or replace the `rw [hAeq]` line below by the corresponding `change`/`show` that unfolds the local `A`.

## Replacement for the `i = 1` branch

Replace the current

```lean
      · -- i = 1: A'(t) is bounded
        sorry
```

with:

```lean
      · -- i = 1: finite Leibniz bound for A = φ * R
        classical
        have hc'c : c / 2 < c := by linarith
        have h0Top : ((0 : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by norm_num
        have h1TopNat : ((1 : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by norm_num
        have h0Nat : (0 : ℕ) ≤ 2 := by norm_num
        have h1Nat : (1 : ℕ) ≤ 2 := by norm_num
        have h1TopWT : (((1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
          exact_mod_cast h1Nat

        let φ : ℝ → ℝ := smoothRightCutoff (c / 2) c
        let R : ℝ → ℝ :=
          resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k

        have hAeq : A = fun t : ℝ => φ t * R t := by
          funext t
          simp [hA_def, φ, R]

        have hφC2 : ContDiff ℝ (2 : ℕ∞) φ := by
          simpa [φ] using
            (smoothRightCutoff_contDiff (c' := c / 2) (c := c))

        have hRC2 : ContDiff ℝ (2 : ℕ∞) R := by
          simpa [R] using Hphys.coeff_contDiff k

        let Φ0 : ℝ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 0 h0Top
        let Φ1 : ℝ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 1 h1TopNat
        refine ⟨Φ0 * Bt 1 k + Φ1 * Bt 0 k, ?_⟩
        intro t

        have hφ0 : ‖iteratedFDeriv ℝ 0 φ t‖ ≤ Φ0 := by
          dsimp [Φ0, φ]
          exact resolverSmoothRightCutoffDerivBound_spec hc'c h0Top t
        have hφ1 : ‖iteratedFDeriv ℝ 1 φ t‖ ≤ Φ1 := by
          dsimp [Φ1, φ]
          exact resolverSmoothRightCutoffDerivBound_spec hc'c h1TopNat t
        have hR0 : ‖iteratedFDeriv ℝ 0 R t‖ ≤ Bt 0 k := by
          dsimp [R]
          exact Hphys.coeff_bound 0 k t h0Nat
        have hR1 : ‖iteratedFDeriv ℝ 1 R t‖ ≤ Bt 1 k := by
          dsimp [R]
          exact Hphys.coeff_bound 1 k t h1Nat
        have hΦ0_nonneg : 0 ≤ Φ0 := by
          dsimp [Φ0]
          exact resolverSmoothRightCutoffDerivBound_nonneg hc'c h0Top
        have hΦ1_nonneg : 0 ≤ Φ1 := by
          dsimp [Φ1]
          exact resolverSmoothRightCutoffDerivBound_nonneg hc'c h1TopNat

        rw [hAeq]
        have hprod := norm_iteratedFDeriv_mul_le hφC2 hRC2 t h1TopWT
        calc
          ‖iteratedFDeriv ℝ 1 (fun t : ℝ => φ t * R t) t‖
              ≤ ∑ r ∈ Finset.range (1 + 1), ((1 : ℕ).choose r : ℝ) *
                  ‖iteratedFDeriv ℝ r φ t‖ *
                  ‖iteratedFDeriv ℝ (1 - r) R t‖ := by
                simpa [mul_assoc] using hprod
          _ ≤ Φ0 * Bt 1 k + Φ1 * Bt 0 k := by
            -- Expand the two terms r = 0 and r = 1.
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            simp only [Finset.sum_range_zero, zero_add, Nat.choose_self, Nat.choose_one_right,
              Nat.cast_one, one_mul]
            have hterm0 :
                ‖iteratedFDeriv ℝ 0 φ t‖ * ‖iteratedFDeriv ℝ 1 R t‖ ≤
                  Φ0 * Bt 1 k := by
              exact mul_le_mul hφ0 hR1 (norm_nonneg _) hΦ0_nonneg
            have hterm1 :
                ‖iteratedFDeriv ℝ 1 φ t‖ * ‖iteratedFDeriv ℝ 0 R t‖ ≤
                  Φ1 * Bt 0 k := by
              exact mul_le_mul hφ1 hR0 (norm_nonneg _) hΦ1_nonneg
            exact add_le_add hterm0 hterm1
```

## If the final `rw/simp` block is brittle

If Lean does not like the explicit expansion of `Finset.range (1 + 1)`, keep the sum-form proof instead. Define

```lean
let B1 : ℝ := ∑ r ∈ Finset.range (1 + 1), ((1 : ℕ).choose r : ℝ) *
  (if hr : (r : ℕ∞) ≤ (2 : ℕ∞) then
    resolverSmoothRightCutoffDerivBound (c / 2) c hc'c r hr
   else 0) * Bt (1 - r) k
```

return `⟨B1, ...⟩`, and close with `Finset.sum_le_sum`. This is usually more robust than hand-simplifying the two terms.

## Caveat

This is the same physical-data route as the previous `i = 0`/`i12` answers. If the theorem must remain purely direct, then `Hphys.coeff_bound` must be replaced by a new direct global bound for `resolverTimeCoeff` and its first time derivative. `ContDiff` alone cannot give global boundedness on the noncompact time axis.
