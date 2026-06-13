import ShenWork.Paper2.IntervalCD6HeatSmoothness

noncomputable section

namespace ShenWork.Paper2.CD6SpectralTail

open ShenWork.Paper2.ACBPolynomialBridge
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.PicardLimitK1C2Coeff (SourceC2CoeffFields)

theorem natShiftSix_of_eigenCube_bound
    {a : ℕ → ℝ} {B0 B : ℝ} (hzero : |a 0| ≤ B0)
    (hcube : ∀ n, 1 ≤ n →
      unitIntervalCosineEigenvalue n ^ (3 : ℕ) * |a n| ≤ B) :
    ∀ n, |a n| ≤ max B0 (64 * B) / ((n : ℝ) + 1) ^ (6 : ℕ) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    norm_num only [Nat.cast_zero, zero_add, one_pow, div_one]
    exact hzero.trans (le_max_left _ _)
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnp1_pos : 0 < (n : ℝ) + 1 := by positivity
    have hpi_ge_one : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hshift_le : ((n : ℝ) + 1) ^ (6 : ℕ) ≤
        64 * (((n : ℝ) * Real.pi) ^ 2) ^ (3 : ℕ) := by
      have hnp1_le : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have hpow1 : ((n : ℝ) + 1) ^ (6 : ℕ) ≤
          (2 * (n : ℝ)) ^ (6 : ℕ) := by
        exact pow_le_pow_left₀ (by positivity) hnp1_le 6
      have hpi6 : (n : ℝ) ^ (6 : ℕ) ≤
          ((n : ℝ) * Real.pi) ^ (6 : ℕ) := by
        have hnnon : 0 ≤ (n : ℝ) := by positivity
        have hn_le : (n : ℝ) ≤ (n : ℝ) * Real.pi := by
          calc (n : ℝ) = (n : ℝ) * 1 := by ring
            _ ≤ (n : ℝ) * Real.pi :=
              mul_le_mul_of_nonneg_left hpi_ge_one hnnon
        exact pow_le_pow_left₀ hnnon hn_le 6
      calc ((n : ℝ) + 1) ^ (6 : ℕ)
          ≤ (2 * (n : ℝ)) ^ (6 : ℕ) := hpow1
        _ = 64 * (n : ℝ) ^ (6 : ℕ) := by ring
        _ ≤ 64 * ((n : ℝ) * Real.pi) ^ (6 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hpi6 (by norm_num)
        _ = 64 * (((n : ℝ) * Real.pi) ^ 2) ^ (3 : ℕ) := by ring
    have hlam_eq : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hmain : ((n : ℝ) + 1) ^ (6 : ℕ) * |a n| ≤ 64 * B := by
      calc ((n : ℝ) + 1) ^ (6 : ℕ) * |a n|
          ≤ (64 * (((n : ℝ) * Real.pi) ^ 2) ^ (3 : ℕ)) * |a n| := by
            exact mul_le_mul_of_nonneg_right hshift_le (abs_nonneg _)
        _ = 64 * (unitIntervalCosineEigenvalue n ^ (3 : ℕ) * |a n|) := by
            rw [hlam_eq]
            ring
        _ ≤ 64 * B := mul_le_mul_of_nonneg_left (hcube n hn) (by norm_num)
    have hmain' := hmain.trans (le_max_right B0 (64 * B))
    rw [le_div_iff₀ (pow_pos hnp1_pos 6)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain'

def localRestart_sourceFields_of_eigenCube
    {p : CM2Params} {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {T σ C0 C C0dot Cdot : ℝ}
    (L : LocalRestart p u T σ)
    (hC : 0 ≤ max C0 (64 * C)) (hCdot : 0 ≤ max C0dot (64 * Cdot))
    (ha0 : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0)
    (ha : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n →
      unitIntervalCosineEigenvalue n ^ (3 : ℕ) * |L.aC s n| ≤ C)
    (hdot0 : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot)
    (hdot : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n →
      unitIntervalCosineEigenvalue n ^ (3 : ℕ) * |L.srcC.adot s n| ≤ Cdot) :
    SourceC2CoeffFields L.srcC :=
  localRestart_sourceFields_of_natShiftSix L hC hCdot
    (fun s hs => natShiftSix_of_eigenCube_bound (ha0 s hs) (ha s hs))
    (fun s hs => natShiftSix_of_eigenCube_bound (hdot0 s hs) (hdot s hs))

end ShenWork.Paper2.CD6SpectralTail
