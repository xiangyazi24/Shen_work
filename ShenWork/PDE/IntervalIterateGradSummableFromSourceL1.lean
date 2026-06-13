import ShenWork.PDE.IntervalDuhamelSpectralC2FromSourceL1
import ShenWork.PDE.IntervalParabolicDuhamelDirectBound
import ShenWork.PDE.IntervalIterateGradMajorant

/-!
# Iterate gradient (∂ₓₓ leg `HuGrad`) summability from source-`ℓ¹`-at-weight

This lane discharges the Picard-iterate's spatial-`∂ₓₓ` gradient-majorant
summability `HuGrad : ∀ m ≤ 2, Summable (boundedWeightJointGradMajorant Bt m)`
from honest physical inputs (source ℓ¹ at the appropriate `|kπ|`/`λ_k` weight,
`u₀` coefficient bounds, and `t > 0`) plus the committed homogeneous heat trace.

## Step 1 — weight-variant Duhamel summables

The committed `IntervalParabolicDuhamelDirectBound` gives the τ-free per-mode
multiplier bound `|D_k| ≤ Bv k`, and the committed KEY IDENTITY
`eigen_smul_abs_spectralCoeff_eq` gives
`λ_k · |duhamelSpectralCoeff a t k| = |duhamelSecondMode λ_k t (a·,k)| = |D_k|`.
Hence a `|kπ|`-weighted Duhamel summable follows from `Summable (|kπ|·Bv)` by
`Summable.of_nonneg_of_le`, with NO time-derivative hypothesis (the parabolic
time integral already cancels the unbounded `∂ₓₓ` eigenvalue).
-/

open ShenWork.IntervalParabolicDuhamelDirectBound
open ShenWork.IntervalParabolicDuhamelSecondDerivBoundedWeight (duhamelSecondMode)
open ShenWork.IntervalDuhamelSpectralC2FromSourceL1 (eigen_smul_abs_spectralCoeff_eq)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalIterateGradMajorant (gradMajorant_two_eq grad2_summable_of_components)
open ShenWork.IntervalResolverJointC2Physical (boundedWeightJointGradMajorant)
open ShenWork.IntervalResolverSpectralJointC2Concrete (gradCosWeight gradCosWeight_nonneg)
open ShenWork.IntervalResolverSpectralTimeC2
  (eigenvalue_sq_mul_exp_summable eigenvalue_cube_mul_exp_summable)

namespace ShenWork.IntervalIterateGradSummableFromSourceL1

open scoped Real

/-- **Per-mode `|kπ|·λ_k`-weighted Duhamel bound.**
`|kπ| · (λ_k · |duhamelSpectralCoeff a t k|) ≤ |kπ| · Bv k`, directly from the
KEY IDENTITY (`λ_k·|Û_k| = |D_k|`) and the committed direct bound `|D_k| ≤ Bv k`
for `k ≥ 1`; the `k = 0` factor `|0·π| = 0` kills the term. -/
theorem duhamelSpectral_gradWeighted_perMode_le
    {a : ℝ → ℕ → ℝ} {Bv : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (hac : Continuous (fun s => a s k))
    (hBv : ∀ s ∈ Set.Icc (0 : ℝ) t, |a s k| ≤ Bv k) :
    |(k : ℝ) * Real.pi| * (unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k|)
      ≤ |(k : ℝ) * Real.pi| * Bv k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · have hlam_pos : 0 < unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue
      have : (0 : ℝ) < (k : ℝ) * Real.pi := by positivity
      positivity
    have hid : unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k|
        = |duhamelSecondMode (unitIntervalCosineEigenvalue k) t (fun s => a s k)| :=
      eigen_smul_abs_spectralCoeff_eq a t k
    have hDk : |duhamelSecondMode (unitIntervalCosineEigenvalue k) t (fun s => a s k)|
        ≤ Bv k :=
      parabolicDuhamel_perMode_bound_direct hlam_pos ht hac hBv
    rw [hid]
    exact mul_le_mul_of_nonneg_left hDk (abs_nonneg _)

/-- **Step 1: `|kπ|·λ_k`-weighted Duhamel summable from source-`ℓ¹` at weight `|kπ|`.**
`Summable (fun k => |kπ| · (λ_k · |duhamelSpectralCoeff a t k|))` from
`Summable (fun k => |kπ| · Bv k)`, the per-mode sup bound, and `t ≥ 0`. -/
theorem duhamelSpectral_gradWeighted_summable_of_sourceL1
    {a : ℝ → ℕ → ℝ} {Bv : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hac : ∀ k, Continuous (fun s => a s k))
    (hBv : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) t, |a s k| ≤ Bv k)
    (hsum : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bv k)) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| *
      (unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k|)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsum
  · exact mul_nonneg (abs_nonneg _)
      (mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
  · exact duhamelSpectral_gradWeighted_perMode_le ht k (hac k) (hBv k)

/-- **Step 1b: bare `|kπ|`-weighted Duhamel summable** (the `T3`-Duhamel piece).
`Summable (fun k => |kπ| · |duhamelSpectralCoeff a t k|)` from `Summable (|kπ|·Bv)`,
where `Bv` bounds `|duhamelSpectralCoeff a t k|` per-mode (e.g. the committed
`abs_duhamelSpectralCoeff_le` envelope). -/
theorem duhamelSpectral_absWeighted_summable
    {a : ℝ → ℕ → ℝ} {Bv : ℕ → ℝ} {t : ℝ}
    (hle : ∀ k, |duhamelSpectralCoeff a t k| ≤ Bv k)
    (hsum : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bv k)) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * |duhamelSpectralCoeff a t k|) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (hle k) (abs_nonneg _)) hsum

/-! ## Step 1c — the homogeneous-side weighted summables (heat-trace family).

The iterate homogeneous coefficient is `e^{-tλ_k}·û₀_k` (with `|û₀_k| ≤ M₀`); its
`i`-th time derivative carries an extra `λ_k^i` and keeps the `e^{-tλ}` super-decay.
The three gradMajorant homogeneous components carry weights:
* `T1`: `|kπ|·λ_k·(M₀·e^{-tλ}) = √λ·λ·M₀·e^{-tλ}`;
* `T2`: `λ_k·(M₀·λ_k·e^{-tλ}) = λ²·M₀·e^{-tλ}` (`eigenvalue_sq_mul_exp_summable`);
* `T3`: `|kπ|·(M₀·λ²·e^{-tλ}) = √λ·λ²·M₀·e^{-tλ}`.
The half-integer powers are dominated by integer ones via `√λ ≤ λ` for `k ≥ 1`
(`λ_k = (kπ)² ≥ π² > 1`) and `= 0` at `k = 0`. -/

/-- `√λ_k ≤ λ_k` for every `k` (`λ_0 = 0`; `λ_k ≥ π² > 1` for `k ≥ 1`). -/
theorem sqrtEig_le_eig (k : ℕ) :
    Real.sqrt (unitIntervalCosineEigenvalue k) ≤ unitIntervalCosineEigenvalue k := by
  have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
    unfold unitIntervalCosineEigenvalue; positivity
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; unfold unitIntervalCosineEigenvalue; simp
  · have h1 : (1 : ℝ) ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hkpi : (1 : ℝ) ≤ (k : ℝ) * Real.pi := by nlinarith [Real.pi_pos]
      nlinarith [hkpi]
    calc Real.sqrt (unitIntervalCosineEigenvalue k)
        ≤ Real.sqrt (unitIntervalCosineEigenvalue k * unitIntervalCosineEigenvalue k) :=
          Real.sqrt_le_sqrt (by nlinarith [h1, hlam])
      _ = unitIntervalCosineEigenvalue k := Real.sqrt_mul_self hlam

/-- **`T1`-homog summable**: `Σ |kπ|·λ_k·(M₀·e^{-tλ_k})` summable for `t > 0`.
`|kπ| = √λ ≤ λ`, so the term is `≤ M₀·(λ²·e^{-tλ})`. -/
theorem hom_grad_T1_summable {t M₀ : ℝ} (ht : 0 < t) (hM₀ : 0 ≤ M₀) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k *
      (M₀ * Real.exp (-t * unitIntervalCosineEigenvalue k))) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((eigenvalue_sq_mul_exp_summable ht).mul_left M₀)
  · exact mul_nonneg (mul_nonneg (abs_nonneg _)
      (by unfold unitIntervalCosineEigenvalue; positivity))
      (mul_nonneg hM₀ (Real.exp_nonneg _))
  · have habs : |(k : ℝ) * Real.pi| = Real.sqrt (unitIntervalCosineEigenvalue k) := by
      unfold unitIntervalCosineEigenvalue
      rw [Real.sqrt_sq_eq_abs]
    rw [habs]
    have hsqle := sqrtEig_le_eig k
    have he : 0 ≤ Real.exp (-t * unitIntervalCosineEigenvalue k) := Real.exp_nonneg _
    have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue; positivity
    calc Real.sqrt (unitIntervalCosineEigenvalue k) * unitIntervalCosineEigenvalue k *
          (M₀ * Real.exp (-t * unitIntervalCosineEigenvalue k))
        ≤ unitIntervalCosineEigenvalue k * unitIntervalCosineEigenvalue k *
            (M₀ * Real.exp (-t * unitIntervalCosineEigenvalue k)) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsqle hlam)
            (mul_nonneg hM₀ he)
      _ = M₀ * (unitIntervalCosineEigenvalue k *
            (unitIntervalCosineEigenvalue k *
              Real.exp (-t * unitIntervalCosineEigenvalue k))) := by ring

/-- **`T2`-homog summable**: `Σ λ_k·(M₀·λ_k·e^{-tλ_k})` summable for `t > 0`. -/
theorem hom_grad_T2_summable {t M₀ : ℝ} (ht : 0 < t) (hM₀ : 0 ≤ M₀) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k *
      (M₀ * (unitIntervalCosineEigenvalue k *
        Real.exp (-t * unitIntervalCosineEigenvalue k)))) := by
  refine ((eigenvalue_sq_mul_exp_summable ht).mul_left M₀).congr (fun k => by ring)

/-- **`T3`-homog summable**: `Σ |kπ|·(M₀·λ_k²·e^{-tλ_k})` summable for `t > 0`.
`|kπ| = √λ ≤ λ`, so the term is `≤ M₀·(λ³·e^{-tλ})`. -/
theorem hom_grad_T3_summable {t M₀ : ℝ} (ht : 0 < t) (hM₀ : 0 ≤ M₀) :
    Summable (fun k : ℕ => |(k : ℝ) * Real.pi| *
      (M₀ * (unitIntervalCosineEigenvalue k * unitIntervalCosineEigenvalue k *
        Real.exp (-t * unitIntervalCosineEigenvalue k)))) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((eigenvalue_cube_mul_exp_summable ht).mul_left M₀)
  · exact mul_nonneg (abs_nonneg _) (mul_nonneg hM₀
      (mul_nonneg (mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
        (by unfold unitIntervalCosineEigenvalue; positivity)) (Real.exp_nonneg _)))
  · have habs : |(k : ℝ) * Real.pi| = Real.sqrt (unitIntervalCosineEigenvalue k) := by
      unfold unitIntervalCosineEigenvalue
      rw [Real.sqrt_sq_eq_abs]
    rw [habs]
    have hsqle := sqrtEig_le_eig k
    have he : 0 ≤ Real.exp (-t * unitIntervalCosineEigenvalue k) := Real.exp_nonneg _
    have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue; positivity
    calc Real.sqrt (unitIntervalCosineEigenvalue k) *
          (M₀ * (unitIntervalCosineEigenvalue k * unitIntervalCosineEigenvalue k *
            Real.exp (-t * unitIntervalCosineEigenvalue k)))
        ≤ unitIntervalCosineEigenvalue k *
            (M₀ * (unitIntervalCosineEigenvalue k * unitIntervalCosineEigenvalue k *
              Real.exp (-t * unitIntervalCosineEigenvalue k))) := by
          apply mul_le_mul_of_nonneg_right hsqle
          exact mul_nonneg hM₀ (mul_nonneg (mul_nonneg hlam hlam) he)
      _ = M₀ * (unitIntervalCosineEigenvalue k * (unitIntervalCosineEigenvalue k *
            (unitIntervalCosineEigenvalue k *
              Real.exp (-t * unitIntervalCosineEigenvalue k)))) := by ring

/-! ## Step 2 — the iterate `HuGrad` capstone from honest weighted-`Btu` summables.

`boundedWeightJointGradMajorant Btu m` expands (`gradCosWeight`):
* `m = 0`: `|kπ|·Btu0 k`;
* `m = 1`: `λ_k·Btu0 k + |kπ|·Btu1 k`;
* `m = 2`: `|kπ|·λ_k·Btu0 k + 2·λ_k·Btu1 k + |kπ|·Btu2 k`  (`gradMajorant_two_eq`).
The honest inputs are the FIVE weighted-`Btu` `Summable` conditions (the A¹-class
residual the source-`ℓ¹`-at-weight phase produces — each provable from Step 1's
weight-variant Duhamel summable for the Duhamel part of `Btu i` plus the
committed homogeneous heat trace for the `e^{-tλ}û₀` part).  This file states them
cleanly and assembles `∀ m ≤ 2, Summable (boundedWeightJointGradMajorant Btu m)`. -/

/-- `gradMajorant` at order `0`: `boundedWeightJointGradMajorant Bt 0 k = |kπ|·Bt0 k`. -/
theorem gradMajorant_zero_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 0 k = |(k : ℝ) * Real.pi| * Bt 0 k := by
  rw [boundedWeightJointGradMajorant, Finset.sum_range_one]
  show (Nat.choose 0 0 : ℝ) * Bt 0 k * gradCosWeight (0 - 0) k = _
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self]
  show 1 * Bt 0 k * |(k : ℝ) * Real.pi| = _
  ring

/-- `gradMajorant` at order `1`:
`boundedWeightJointGradMajorant Bt 1 k = λ_k·Bt0 k + |kπ|·Bt1 k`. -/
theorem gradMajorant_one_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 1 k
      = unitIntervalCosineEigenvalue k * Bt 0 k + |(k : ℝ) * Real.pi| * Bt 1 k := by
  rw [boundedWeightJointGradMajorant, Finset.sum_range_succ, Finset.sum_range_one]
  show (Nat.choose 1 0 : ℝ) * Bt 0 k * gradCosWeight (1 - 0) k
      + (Nat.choose 1 1 : ℝ) * Bt 1 k * gradCosWeight (1 - 1) k = _
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one]
  show 1 * Bt 0 k * gradCosWeight 1 k + 1 * Bt 1 k * gradCosWeight 0 k = _
  show 1 * Bt 0 k * unitIntervalCosineEigenvalue k + 1 * Bt 1 k * |(k : ℝ) * Real.pi| = _
  ring

/-- **Step 2 capstone: the iterate `HuGrad` from honest weighted-`Btu` summables.**
`∀ m ≤ 2, Summable (boundedWeightJointGradMajorant Btu m)` from the five honest
weighted-`Btu` `Summable` conditions (the A¹-class residual).  NO `HuGrad` /
`IteratePicardJointC2Data` / capstone taken as a hypothesis. -/
theorem iterate_gradSummable_of_weightedBtuSummable {Btu : ℕ → ℕ → ℝ}
    (s0 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 0 k))
    (s1a : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 0 k))
    (s1 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 1 k))
    (s2a : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Btu 0 k))
    (s2b : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 1 k))
    (s2c : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 2 k)) :
    ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Btu m) := by
  intro m hm
  have hm2 : m ≤ 2 := by exact_mod_cast hm
  interval_cases m
  · exact (s0.congr (fun k => (gradMajorant_zero_eq Btu k).symm))
  · exact ((s1a.add s1).congr (fun k => (gradMajorant_one_eq Btu k).symm))
  · exact grad2_summable_of_components s2a s2b s2c

/-- **Composed `Hg2u`.**  Feeding the Step-2 capstone into the committed consumer
`iterate_Hg2u_of_gradSummable` emits the single order-2 gradient summable. -/
theorem iterate_Hg2u_of_weightedBtuSummable {Btu : ℕ → ℕ → ℝ}
    (s0 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 0 k))
    (s1a : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 0 k))
    (s1 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 1 k))
    (s2a : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Btu 0 k))
    (s2b : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Btu 1 k))
    (s2c : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Btu 2 k)) :
    Summable (boundedWeightJointGradMajorant Btu 2) :=
  ShenWork.IntervalIterateGradMajorant.iterate_Hg2u_of_gradSummable
    (iterate_gradSummable_of_weightedBtuSummable s0 s1a s1 s2a s2b s2c)

end ShenWork.IntervalIterateGradSummableFromSourceL1
