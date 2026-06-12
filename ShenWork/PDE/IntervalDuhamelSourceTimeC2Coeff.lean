import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalResolverSpectralTimeC2

open ShenWork.IntervalSourceCoefficientTimeC1
open ShenWork.IntervalResolverSpectralTimeC2
open ShenWork.PDE
open ShenWork.PDE.ResolventEstimate

noncomputable section

namespace ShenWork.IntervalDuhamelSourceTimeC2Coeff

/-- Mode-wise multiplication by a bounded weight preserves the strengthened
`DuhamelSourceTimeC2Coeff` package. -/
def duhamelSourceTimeC2Coeff_mul_weight
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    (c : ℕ → ℝ) {Cw : ℝ} (hCw_nn : 0 ≤ Cw)
    (hCw : ∀ n, |c n| ≤ Cw) :
    DuhamelSourceTimeC2Coeff (fun s n => c n * a s n) where
  toTimeC1 := duhamelSourceTimeC1_mul_weight src.toTimeC1 c hCw_nn hCw
  sourceEigenEnvelope := fun n => Cw * src.sourceEigenEnvelope n
  sourceEigen_nonneg := fun n =>
    mul_nonneg hCw_nn (src.sourceEigen_nonneg n)
  sourceEigen_summable := src.sourceEigen_summable.mul_left Cw
  sourceEigen_bound := fun s hs n => by
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n * |c n * a s n|
        = |c n| * (unitIntervalCosineEigenvalue n * |a s n|) := by
            rw [abs_mul]
            ring
      _ ≤ Cw * src.sourceEigenEnvelope n :=
          mul_le_mul (hCw n) (src.sourceEigen_bound s hs n)
            (mul_nonneg hlam (abs_nonneg _)) hCw_nn
  sourceEigenSqEnvelope := fun n => Cw * src.sourceEigenSqEnvelope n
  sourceEigenSq_nonneg := fun n =>
    mul_nonneg hCw_nn (src.sourceEigenSq_nonneg n)
  sourceEigenSq_summable := src.sourceEigenSq_summable.mul_left Cw
  sourceEigenSq_bound := fun s hs n => by
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * |c n * a s n|)
        = |c n| * (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n * |a s n|)) := by
            rw [abs_mul]
            ring
      _ ≤ Cw * src.sourceEigenSqEnvelope n :=
          mul_le_mul (hCw n) (src.sourceEigenSq_bound s hs n)
            (mul_nonneg hlam (mul_nonneg hlam (abs_nonneg _))) hCw_nn
  adotEigenEnvelope := fun n => Cw * src.adotEigenEnvelope n
  adotEigen_nonneg := fun n =>
    mul_nonneg hCw_nn (src.adotEigen_nonneg n)
  adotEigen_summable := src.adotEigen_summable.mul_left Cw
  adotEigen_bound := fun s hs n => by
    change unitIntervalCosineEigenvalue n *
        |c n * src.toTimeC1.adot s n| ≤ Cw * src.adotEigenEnvelope n
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n * |c n * src.toTimeC1.adot s n|
        = |c n| *
            (unitIntervalCosineEigenvalue n * |src.toTimeC1.adot s n|) := by
            rw [abs_mul]
            ring
      _ ≤ Cw * src.adotEigenEnvelope n :=
          mul_le_mul (hCw n) (src.adotEigen_bound s hs n)
            (mul_nonneg hlam (abs_nonneg _)) hCw_nn
  adotEigenSqEnvelope := fun n => Cw * src.adotEigenSqEnvelope n
  adotEigenSq_nonneg := fun n =>
    mul_nonneg hCw_nn (src.adotEigenSq_nonneg n)
  adotEigenSq_summable := src.adotEigenSq_summable.mul_left Cw
  adotEigenSq_bound := fun s hs n => by
    change unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |c n * src.toTimeC1.adot s n|) ≤
      Cw * src.adotEigenSqEnvelope n
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * |c n * src.toTimeC1.adot s n|)
        = |c n| * (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n * |src.toTimeC1.adot s n|)) := by
            rw [abs_mul]
            ring
      _ ≤ Cw * src.adotEigenSqEnvelope n :=
          mul_le_mul (hCw n) (src.adotEigenSq_bound s hs n)
            (mul_nonneg hlam (mul_nonneg hlam (abs_nonneg _))) hCw_nn

/-- The concrete elliptic resolver multiplier preserves
`DuhamelSourceTimeC2Coeff`. -/
def duhamelSourceTimeC2Coeff_resolver_weight
    (p : CM2Params) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) :
    DuhamelSourceTimeC2Coeff
      (fun s n => intervalNeumannResolverWeight p n * a s n) :=
  duhamelSourceTimeC2Coeff_mul_weight src
    (intervalNeumannResolverWeight p) (div_nonneg zero_le_one p.hμ.le) (fun n => by
      rw [abs_of_nonneg (intervalNeumannResolverWeight_nonneg p n)]
      unfold intervalNeumannResolverWeight
      apply one_div_le_one_div_of_le p.hμ
      linarith [unitIntervalNeumannSpectrum_eigenvalue_nonneg n])

end ShenWork.IntervalDuhamelSourceTimeC2Coeff
