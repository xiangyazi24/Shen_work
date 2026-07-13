/- Positive-time strong membership and time continuity for classical orbits. -/
import ShenWork.Paper3.IntervalDomainStrongDuhamel
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
import ShenWork.Paper2.IntervalNeumannHeatGradientL2BrickB
import ShenWork.Paper2.IntervalChiNegH1EnergyDeriv

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.FractionalPower

noncomputable section

/-- For exponents at most one, the fractional Neumann weight is controlled by
the graph norm of the Laplacian. -/
theorem fractionalPowerEnergyTerm_le_graphEnergy
    {sigma : ℝ} (hsigma1 : sigma ≤ 1)
    (a b : ℕ → ℂ) (n : ℕ)
    (hrel : b n = -((neumannEigenvalue 1 n : ℝ) : ℂ) * a n) :
    fractionalPowerEnergyTerm 1 sigma a n ≤
      2 * ‖a n‖ ^ 2 + 2 * ‖b n‖ ^ 2 := by
  let lam := neumannEigenvalue 1 n
  have hlam0 : 0 ≤ lam := neumannEigenvalue_nonneg 1 n
  have hbase : 1 ≤ 1 + lam := by linarith
  have hexp : 2 * sigma ≤ (2 : ℝ) := by linarith
  have hweight : (1 + lam) ^ (2 * sigma) ≤ (1 + lam) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hb : ‖b n‖ ^ 2 = lam ^ 2 * ‖a n‖ ^ 2 := by
    rw [hrel]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hlam0]
    ring
  have hgraph : (1 + lam) ^ (2 : ℝ) * ‖a n‖ ^ 2 ≤
      2 * ‖a n‖ ^ 2 + 2 * (lam ^ 2 * ‖a n‖ ^ 2) := by
    rw [Real.rpow_two]
    nlinarith [sq_nonneg (lam - 1), sq_nonneg ‖a n‖]
  unfold fractionalPowerEnergyTerm fractionalPowerWeight
  dsimp [lam] at hweight hb hgraph ⊢
  calc
    (1 + neumannEigenvalue 1 n) ^ (2 * sigma) * ‖a n‖ ^ 2 ≤
        (1 + neumannEigenvalue 1 n) ^ (2 : ℝ) * ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ ≤ 2 * ‖a n‖ ^ 2 +
        2 * (neumannEigenvalue 1 n ^ 2 * ‖a n‖ ^ 2) := hgraph
    _ = 2 * ‖a n‖ ^ 2 + 2 * ‖b n‖ ^ 2 := by rw [hb]

/-- Square-summable coefficients and square-summable Laplacian coefficients
give membership in every fractional power below the full Laplacian domain. -/
theorem fractionalPowerEnergy_summable_of_graphCoeffs
    {sigma : ℝ} (hsigma1 : sigma ≤ 1)
    {a b : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2)
    (hrel : ∀ n, b n = -((neumannEigenvalue 1 n : ℝ) : ℂ) * a n) :
    Summable fun n => fractionalPowerEnergyTerm 1 sigma a n := by
  apply Summable.of_nonneg_of_le
    (fun n => fractionalPowerEnergyTerm_nonneg 1 sigma a n)
    (fun n => fractionalPowerEnergyTerm_le_graphEnergy
      hsigma1 a b n (hrel n))
  exact (ha.mul_left 2).add (hb.mul_left 2)

theorem fractionalPowerEnergy_tsum_le_graphCoeffs
    {sigma : ℝ} (hsigma1 : sigma ≤ 1)
    {a b : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2)
    (hrel : ∀ n, b n = -((neumannEigenvalue 1 n : ℝ) : ℂ) * a n) :
    (∑' n, fractionalPowerEnergyTerm 1 sigma a n) ≤
      2 * (∑' n, ‖a n‖ ^ 2) + 2 * (∑' n, ‖b n‖ ^ 2) := by
  have henergy := fractionalPowerEnergy_summable_of_graphCoeffs
    hsigma1 ha hb hrel
  have hmajor : Summable fun n =>
      2 * ‖a n‖ ^ 2 + 2 * ‖b n‖ ^ 2 :=
    (ha.mul_left 2).add (hb.mul_left 2)
  have hle := henergy.tsum_le_tsum
    (fun n => fractionalPowerEnergyTerm_le_graphEnergy
      hsigma1 a b n (hrel n)) hmajor
  rw [Summable.tsum_add (ha.mul_left 2) (hb.mul_left 2),
    ha.tsum_mul_left, hb.tsum_mul_left] at hle
  exact hle

#print axioms fractionalPowerEnergyTerm_le_graphEnergy
#print axioms fractionalPowerEnergy_summable_of_graphCoeffs
#print axioms fractionalPowerEnergy_tsum_le_graphCoeffs

end

end ShenWork.Paper3
