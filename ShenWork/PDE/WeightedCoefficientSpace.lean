/- Weighted cosine coefficients realized in Mathlib's complete `ell^2` space. -/
import ShenWork.PDE.FractionalPowerSpace
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace ShenWork.PDE

open FractionalPower
open scoped ENNReal

noncomputable section

/-- The ambient complete Hilbert sequence space used for Bochner-Duhamel
integration. -/
abbrev CoeffL2 := lp (fun _ : ℕ => ℂ) 2

/-- Multiplication by the square root of the fractional-power energy weight. -/
def weightedCoeffSequence (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((1 + neumannEigenvalue L n) ^ sigma : ℝ) * a n

theorem weightedCoeffSequence_norm_sq
    (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖weightedCoeffSequence L sigma a n‖ ^ 2 =
      fractionalPowerEnergyTerm L sigma a n := by
  have hbase : 0 < 1 + neumannEigenvalue L n :=
    one_add_neumannEigenvalue_pos L n
  simp only [weightedCoeffSequence, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hbase sigma)]
  unfold fractionalPowerEnergyTerm fractionalPowerWeight
  rw [mul_pow]
  congr 1
  rw [show 2 * sigma = sigma * 2 by ring, Real.rpow_mul hbase.le]
  simp [pow_two]

/-- A weighted-energy coefficient family as an element of complete `ell^2`. -/
def weightedCoeffToLp
    (L sigma : ℝ) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n) :
    CoeffL2 :=
  ⟨weightedCoeffSequence L sigma a, by
    apply memℓp_gen
    simpa [weightedCoeffSequence_norm_sq] using ha⟩

@[simp] theorem weightedCoeffToLp_apply
    (L sigma : ℝ) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n)
    (n : ℕ) :
    weightedCoeffToLp L sigma a ha n = weightedCoeffSequence L sigma a n :=
  rfl

/-- Its sequence norm is exactly the square root of the weighted energy. -/
theorem norm_weightedCoeffToLp
    (L sigma : ℝ) (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n) :
    ‖weightedCoeffToLp L sigma a ha‖ =
      Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [show (2 : ℝ≥0∞).toReal = 2 by norm_num, Real.rpow_two]
  rw [show (∑' n : ℕ, ‖weightedCoeffToLp L sigma a ha n‖ ^ 2) =
      ∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n by
    apply tsum_congr
    intro n
    exact weightedCoeffSequence_norm_sq L sigma a n]
  exact (Real.sqrt_eq_rpow _).symm

#print axioms weightedCoeffSequence_norm_sq
#print axioms norm_weightedCoeffToLp

end

end ShenWork.PDE
