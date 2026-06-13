import ShenWork.Paper2.IntervalPicardLimitK1C2Coeff
import Mathlib.Analysis.PSeries
noncomputable section
namespace ShenWork.Paper2.ACBPolynomialEnvelope
open ShenWork.Paper2.PicardLimitK1C2Coeff
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
private def env1 (C : ℝ) (n : ℕ) : ℝ :=
  C * Real.pi ^ 2 * (((n : ℝ) + 1) ^ (4 : ℕ))⁻¹
private def env2 (C : ℝ) (n : ℕ) : ℝ :=
  C * Real.pi ^ 4 * (((n : ℝ) + 1) ^ (2 : ℕ))⁻¹
private theorem shift_pseries_two :
    Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (2 : ℕ))⁻¹) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  simpa [one_div] using (summable_nat_add_iff
    (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) 1).2 hbase
private theorem shift_pseries_four :
    Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (4 : ℕ))⁻¹) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (4 : ℕ)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  simpa [one_div] using (summable_nat_add_iff
    (f := fun n : ℕ => 1 / (n : ℝ) ^ (4 : ℕ)) 1).2 hbase
private theorem lam_le_shift (n : ℕ) :
    unitIntervalCosineEigenvalue n ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by
  unfold unitIntervalCosineEigenvalue
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hpi2 : 0 ≤ Real.pi ^ 2 := by positivity
  have hs : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hn0]
  nlinarith
private theorem lam_sq_le_shift (n : ℕ) :
    unitIntervalCosineEigenvalue n * unitIntervalCosineEigenvalue n ≤
      Real.pi ^ 4 * ((n : ℝ) + 1) ^ 4 := by
  have h := lam_le_shift n
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hshift : 0 ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  calc unitIntervalCosineEigenvalue n * unitIntervalCosineEigenvalue n
      ≤ (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) *
          (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) :=
        mul_le_mul h h hlam hshift
    _ = Real.pi ^ 4 * ((n : ℝ) + 1) ^ 4 := by ring
private theorem eigen_one_bound {b : ℝ} {C : ℝ} {n : ℕ}
    (hb : |b| ≤ C / ((n : ℝ) + 1) ^ (6 : ℕ)) :
    unitIntervalCosineEigenvalue n * |b| ≤ env1 C n := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hb' := mul_le_mul (lam_le_shift n) hb (abs_nonneg _)
    (by positivity : 0 ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)
  calc unitIntervalCosineEigenvalue n * |b|
      ≤ (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) *
          (C / ((n : ℝ) + 1) ^ (6 : ℕ)) := hb'
    _ = env1 C n := by
      dsimp [env1]
      field_simp [ne_of_gt hm]
private theorem eigen_two_bound {b : ℝ} {C : ℝ} {n : ℕ}
    (hb : |b| ≤ C / ((n : ℝ) + 1) ^ (6 : ℕ)) :
    unitIntervalCosineEigenvalue n * (unitIntervalCosineEigenvalue n * |b|)
      ≤ env2 C n := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hb' := mul_le_mul (lam_sq_le_shift n) hb (abs_nonneg _)
    (by positivity : 0 ≤ Real.pi ^ 4 * ((n : ℝ) + 1) ^ 4)
  calc unitIntervalCosineEigenvalue n * (unitIntervalCosineEigenvalue n * |b|)
      = (unitIntervalCosineEigenvalue n * unitIntervalCosineEigenvalue n) * |b| := by ring
    _ ≤ (Real.pi ^ 4 * ((n : ℝ) + 1) ^ 4) *
          (C / ((n : ℝ) + 1) ^ (6 : ℕ)) := hb'
    _ = env2 C n := by
      dsimp [env2]
      field_simp [ne_of_gt hm]
def sourceC2CoeffFields_of_natShiftSix
    {a : ℝ → ℕ → ℝ} {src : DuhamelSourceTimeC1 a}
    {C Cdot : ℝ} (hC : 0 ≤ C) (hCdot : 0 ≤ Cdot)
    (ha : ∀ s, 0 ≤ s → ∀ n,
      |a s n| ≤ C / ((n : ℝ) + 1) ^ (6 : ℕ))
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |src.adot s n| ≤ Cdot / ((n : ℝ) + 1) ^ (6 : ℕ)) :
    SourceC2CoeffFields src where
  sourceEigenEnvelope := env1 C
  sourceEigen_nonneg := fun n => by dsimp [env1]; positivity
  sourceEigen_summable := by
    simpa [env1] using shift_pseries_four.mul_left (C * Real.pi ^ 2)
  sourceEigen_bound := fun s hs n => eigen_one_bound (ha s hs n)
  sourceEigenSqEnvelope := env2 C
  sourceEigenSq_nonneg := fun n => by dsimp [env2]; positivity
  sourceEigenSq_summable := by
    simpa [env2] using shift_pseries_two.mul_left (C * Real.pi ^ 4)
  sourceEigenSq_bound := fun s hs n => eigen_two_bound (ha s hs n)
  adotEigenEnvelope := env1 Cdot
  adotEigen_nonneg := fun n => by dsimp [env1]; positivity
  adotEigen_summable := by
    simpa [env1] using shift_pseries_four.mul_left (Cdot * Real.pi ^ 2)
  adotEigen_bound := fun s hs n => eigen_one_bound (hadot s hs n)
  adotEigenSqEnvelope := env2 Cdot
  adotEigenSq_nonneg := fun n => by dsimp [env2]; positivity
  adotEigenSq_summable := by
    simpa [env2] using shift_pseries_two.mul_left (Cdot * Real.pi ^ 4)
  adotEigenSq_bound := fun s hs n => eigen_two_bound (hadot s hs n)
end ShenWork.Paper2.ACBPolynomialEnvelope
