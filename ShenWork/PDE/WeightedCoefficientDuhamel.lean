/- Bochner-Duhamel identities in the weighted coefficient realization. -/
import ShenWork.PDE.WeightedCoefficientSpace
import ShenWork.PDE.SectorialOperator

namespace ShenWork.PDE

open MeasureTheory
open FractionalPower
open SectorialOperator

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

#print axioms weightedCoeffToLp_mild_eq

end

end ShenWork.PDE
