/- Bochner-Duhamel identities in the weighted coefficient realization. -/
import ShenWork.PDE.WeightedCoefficientSpace
import ShenWork.PDE.SectorialOperator

namespace ShenWork.PDE

open MeasureTheory
open FractionalPower
open SectorialOperator
open scoped ENNReal

noncomputable section

/-- A coordinatewise complex Duhamel identity lifts to the complete weighted
`ell^2` realization.  All analytic work is exposed as membership and Bochner
integrability hypotheses; the conclusion contains no coordinatewise
interchange assumption. -/
theorem weightedCoeffToLp_mild_eq
    {L sigma a t : ℝ} {growth : ℕ → ℝ}
    {c source : ℝ → ℕ → ℂ}
    (hct : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L sigma (c t) n)
    (hlinear : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L sigma
        (diagonalSemigroupCoeff growth (t - a) (c a)) n)
    (hsource : ∀ s : ℝ, Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L sigma
        (diagonalSemigroupCoeff growth (t - s) (source s)) n)
    (hint : IntervalIntegrable
      (fun s => weightedCoeffToLp L sigma
        (diagonalSemigroupCoeff growth (t - s) (source s))
        (hsource s)) volume a t)
    (hcoord : ∀ n : ℕ,
      c t n = diagonalSemigroupCoeff growth (t - a) (c a) n +
        ∫ s in a..t,
          diagonalSemigroupCoeff growth (t - s) (source s) n) :
    weightedCoeffToLp L sigma (c t) hct =
      weightedCoeffToLp L sigma
          (diagonalSemigroupCoeff growth (t - a) (c a)) hlinear +
        ∫ s in a..t, weightedCoeffToLp L sigma
          (diagonalSemigroupCoeff growth (t - s) (source s))
          (hsource s) := by
  ext n
  change
    weightedCoeffToLp L sigma (c t) hct n =
      weightedCoeffToLp L sigma
          (diagonalSemigroupCoeff growth (t - a) (c a)) hlinear n +
        (∫ s in a..t, weightedCoeffToLp L sigma
          (diagonalSemigroupCoeff growth (t - s) (source s))
          (hsource s)) n
  rw [coeffL2_intervalIntegral_apply hint n]
  simp only [weightedCoeffToLp_apply]
  unfold weightedCoeffSequence
  rw [hcoord n, mul_add]
  congr 1
  exact (intervalIntegral.integral_const_mul
    (((1 + neumannEigenvalue L n) ^ sigma : ℝ) : ℂ)
    (fun s => diagonalSemigroupCoeff growth (t - s) (source s) n)).symm

/-- A coordinatewise mild identity whose linear and Duhamel terms already
belong to weighted `ell^2` forces the target coefficient family itself to
belong to the same fractional space.  This is the endpoint-membership exit
needed by first-exit bootstraps. -/
theorem fractionalPowerEnergy_summable_of_mild
    {L sigma a t : ℝ} {growth : ℕ → ℝ}
    {c source : ℝ → ℕ → ℂ}
    (hlinear : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L sigma
        (diagonalSemigroupCoeff growth (t - a) (c a)) n)
    (hsource : ∀ s : ℝ, Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L sigma
        (diagonalSemigroupCoeff growth (t - s) (source s)) n)
    (hint : IntervalIntegrable
      (fun s => weightedCoeffToLp L sigma
        (diagonalSemigroupCoeff growth (t - s) (source s))
        (hsource s)) volume a t)
    (hcoord : ∀ n : ℕ,
      c t n = diagonalSemigroupCoeff growth (t - a) (c a) n +
        ∫ s in a..t,
          diagonalSemigroupCoeff growth (t - s) (source s) n) :
    Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma (c t) n := by
  let z : CoeffL2 :=
    weightedCoeffToLp L sigma
        (diagonalSemigroupCoeff growth (t - a) (c a)) hlinear +
      ∫ s in a..t, weightedCoeffToLp L sigma
        (diagonalSemigroupCoeff growth (t - s) (source s))
        (hsource s)
  have hzcoord : ∀ n : ℕ,
      z n = weightedCoeffSequence L sigma (c t) n := by
    intro n
    change
      weightedCoeffToLp L sigma
          (diagonalSemigroupCoeff growth (t - a) (c a)) hlinear n +
        (∫ s in a..t, weightedCoeffToLp L sigma
          (diagonalSemigroupCoeff growth (t - s) (source s))
          (hsource s)) n = weightedCoeffSequence L sigma (c t) n
    rw [coeffL2_intervalIntegral_apply hint n]
    simp only [weightedCoeffToLp_apply]
    unfold weightedCoeffSequence
    rw [hcoord n, mul_add]
    congr 1
    exact intervalIntegral.integral_const_mul
      (((1 + neumannEigenvalue L n) ^ sigma : ℝ) : ℂ)
      (fun s => diagonalSemigroupCoeff growth (t - s) (source s) n)
  have hzsum : Summable fun n : ℕ => ‖z n‖ ^ 2 := by
    have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    simpa using (lp.memℓp z).summable hp
  exact hzsum.congr (fun n => by
    rw [hzcoord n, weightedCoeffSequence_norm_sq])

#print axioms weightedCoeffToLp_mild_eq
#print axioms fractionalPowerEnergy_summable_of_mild

end

end ShenWork.PDE
