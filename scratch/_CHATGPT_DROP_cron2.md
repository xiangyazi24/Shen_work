# Q1683 (cron2): `i12_compact`

GitHub-connector only. I did not read the local `/tmp` file or run Lean. I inferred the target from `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`: inside `cutoffResolverMajorant_bddAbove_direct`, the local proof `hA_global_bounds` still has the `i = 1` and `i = 2` branches as `sorry`.

## Compact answer

Do not close `i = 1` and `i = 2` by separate time-region arguments. Close all `i <= 2` with one finite Leibniz bound for

```lean
A t = smoothRightCutoff (c / 2) c t *
  resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

The required setup is:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

#check norm_iteratedFDeriv_mul_le
#check resolverSmoothRightCutoffDerivBound_spec
#check resolverSmoothRightCutoffDerivBound_nonneg
#check ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

Before `hA_global_bounds`, add:

```lean
obtain ⟨Bt, Hphys⟩ :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hu₀_pos
```

Then replace the whole three-case `interval_cases i` proof by this pattern:

```lean
have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
    ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
  intro i hi
  classical
  have hc'c : c / 2 < c := by linarith
  have hiTop : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hi
  let phi : ℝ → ℝ := smoothRightCutoff (c / 2) c
  let R : ℝ → ℝ := resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k
  have hAeq : A = fun t : ℝ => phi t * R t := by
    funext t
    simp [A, phi, R]
  have hphiC2 : ContDiff ℝ (2 : ℕ∞) phi := by
    simpa [phi] using smoothRightCutoff_contDiff (c' := c / 2) (c := c)
  have hRC2 : ContDiff ℝ (2 : ℕ∞) R := by
    simpa [R] using Hphys.coeff_contDiff k
  let B_i : ℝ :=
    ∑ r ∈ Finset.range (i + 1),
      (i.choose r : ℝ) *
        (if hr : (r : ℕ∞) ≤ (2 : ℕ∞) then
          resolverSmoothRightCutoffDerivBound (c / 2) c hc'c r hr
        else 0) * Bt (i - r) k
  refine ⟨B_i, ?_⟩
  intro t
  rw [hAeq]
  calc
    ‖iteratedFDeriv ℝ i (fun t : ℝ => phi t * R t) t‖
        ≤ ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
            ‖iteratedFDeriv ℝ r phi t‖ *
            ‖iteratedFDeriv ℝ (i - r) R t‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hphiC2 hRC2 t hiTop
    _ ≤ B_i := by
      unfold B_i
      apply Finset.sum_le_sum
      intro r hrmem
      have hri : r ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrmem)
      have hrNat : r ≤ 2 := le_trans hri hi
      have hirNat : i - r ≤ 2 := le_trans (Nat.sub_le i r) hi
      have hrTop : (r : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hrNat
      have hphi := resolverSmoothRightCutoffDerivBound_spec hc'c hrTop t
      have hR : ‖iteratedFDeriv ℝ (i - r) R t‖ ≤ Bt (i - r) k := by
        simpa [R] using Hphys.coeff_bound (i - r) k t hirNat
      have hnn : 0 ≤ (i.choose r : ℝ) *
          resolverSmoothRightCutoffDerivBound (c / 2) c hc'c r hrTop := by
        exact mul_nonneg (Nat.cast_nonneg _) (resolverSmoothRightCutoffDerivBound_nonneg hc'c hrTop)
      calc
        (i.choose r : ℝ) * ‖iteratedFDeriv ℝ r phi t‖ * ‖iteratedFDeriv ℝ (i - r) R t‖
            ≤ (i.choose r : ℝ) *
                resolverSmoothRightCutoffDerivBound (c / 2) c hc'c r hrTop *
                ‖iteratedFDeriv ℝ (i - r) R t‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by simpa [phi] using hphi) (Nat.cast_nonneg _))
                (norm_nonneg _)
        _ ≤ (i.choose r : ℝ) *
                resolverSmoothRightCutoffDerivBound (c / 2) c hc'c r hrTop * Bt (i - r) k := by
              exact mul_le_mul_of_nonneg_left hR hnn
        _ = (i.choose r : ℝ) *
                (if hr : (r : ℕ∞) ≤ (2 : ℕ∞) then
                  resolverSmoothRightCutoffDerivBound (c / 2) c hc'c r hr
                else 0) * Bt (i - r) k := by
              rw [dif_pos hrTop]
```

This automatically gives the compact constants

```text
B1 = Phi0 * Bt 1 k + Phi1 * Bt 0 k
B2 = Phi0 * Bt 2 k + 2 * Phi1 * Bt 1 k + Phi2 * Bt 0 k
```

This is the same physical-data route as the previous `i = 0` answer. A genuinely direct proof would need new global bounds for the first two time derivatives of `resolverTimeCoeff`; `ContDiff` alone is not enough on the noncompact time axis.
