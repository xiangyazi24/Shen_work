import ShenWork.Paper1.Theorem12TentWeightFiniteness
import ShenWork.Paper1.Theorem12WeightedEnergy

open Filter MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted first-derivative reductions on the whole line

The tent-exhaustion theorem acts on an *unweighted* field `w` and inserts
the factor `exp (2 * eta * x)` itself.  Thus the correct field for the
weighted population derivative is the raw bracket below, rather than
`paper5WeightedPopulationX` (which already contains one exponential
weight).

This file records only the exact algebraic identification and the resulting
uniform-cap reduction.  Establishing the uniform cap bound is the remaining
Henry-type analytic input; it is deliberately not hidden in this interface.
-/

/-- The unweighted bracket whose exponential conjugate is the formal first
spatial derivative of the population perturbation. -/
def paper5RawPopulationX
    (eta : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  eta * (u t x - U x) + (deriv (u t) x - deriv U x)

/-- The formal weighted first derivative has exactly one exponential factor
in front of the raw derivative bracket. -/
theorem paper5WeightedPopulationX_eq_exp_mul_rawPopulationX
    (eta : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) :
    paper5WeightedPopulationX eta u U t x =
      Real.exp (eta * x) * paper5RawPopulationX eta u U t x := by
  simp [paper5WeightedPopulationX, paper5WeightedPopulation,
    paper5RawPopulationX]
  ring

/-- **Reduction, not the Henry closure.**  A uniform family of cap-energy
bounds for the raw first derivative gives square-integrability of the
already-conjugated field `paper5WeightedPopulationX`.

The cap hypothesis is intentionally stated for `paper5RawPopulationX`.
Putting `paper5WeightedPopulationX` there would insert the exponential
weight twice and would prove a different, unnecessarily stronger claim. -/
theorem paper5WeightedPopulationX_sq_integrable_of_uniform_raw_cap
    {eta C t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (heta : 0 < eta)
    (hraw_cont : Continuous (paper5RawPopulationX eta u U t))
    (hcap : ∀ n : ℕ,
      Integrable (fun x =>
        capWeight eta (n : ℝ) x *
          |paper5RawPopulationX eta u U t x| ^ 2))
    (hbound : ∀ n : ℕ,
      (∫ x : ℝ,
        capWeight eta (n : ℝ) x *
          |paper5RawPopulationX eta u U t x| ^ 2) ≤ C) :
    Integrable (fun x =>
      (paper5WeightedPopulationX eta u U t x) ^ 2) := by
  have hfull : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |paper5RawPopulationX eta u U t x| ^ 2) :=
    fullWeightedL2_integrable_of_uniform_cap
      heta hraw_cont hcap hbound
  refine hfull.congr (Eventually.of_forall fun x => ?_)
  change Real.exp (2 * eta * x) *
      |paper5RawPopulationX eta u U t x| ^ 2 =
    (paper5WeightedPopulationX eta u U t x) ^ 2
  rw [paper5WeightedPopulationX_eq_exp_mul_rawPopulationX,
    mul_pow, sq_abs]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

end ShenWork.Paper1

#print axioms ShenWork.Paper1.paper5WeightedPopulationX_eq_exp_mul_rawPopulationX
#print axioms ShenWork.Paper1.paper5WeightedPopulationX_sq_integrable_of_uniform_raw_cap
