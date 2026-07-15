import ShenWork.Paper1.WholeLineWeightedRegularityGradient
import ShenWork.Paper1.Theorem12EnergyProducer

open Filter MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted second-derivative reductions on the whole line

As for the first derivative, the cap-exhaustion input must be the raw
unweighted bracket.  The results below isolate that bracket, identify its
single exponential conjugate, and reduce the diffusion pairing required by
the weighted energy identity to square-integrability of the weighted second
derivative.

No estimate of the raw cap energies is asserted here.  Producing a bound
uniform in the cap radius remains the Henry-type analytic step.
-/

/-- The unweighted bracket whose exponential conjugate is the formal second
spatial derivative of the population perturbation. -/
def paper5RawPopulationXX
    (eta : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  eta ^ 2 * (u t x - U x) +
    2 * eta * (deriv (u t) x - deriv U x) +
    (iteratedDeriv 2 (u t) x - iteratedDeriv 2 U x)

/-- The formal weighted second derivative has exactly one exponential factor
in front of the raw second-derivative bracket. -/
theorem paper5WeightedPopulationXX_eq_exp_mul_rawPopulationXX
    (eta : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t x : ℝ) :
    paper5WeightedPopulationXX eta u U t x =
      Real.exp (eta * x) * paper5RawPopulationXX eta u U t x := by
  simp [paper5WeightedPopulationXX, paper5WeightedPopulation,
    paper5RawPopulationXX]
  ring

/-- **Reduction, not the Henry closure.**  Uniform cap-energy bounds for the
raw second derivative imply square-integrability of the conjugated formal
second derivative. -/
theorem paper5WeightedPopulationXX_sq_integrable_of_uniform_raw_cap
    {eta C t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (heta : 0 < eta)
    (hraw_cont : Continuous (paper5RawPopulationXX eta u U t))
    (hcap : ∀ n : ℕ,
      Integrable (fun x =>
        capWeight eta (n : ℝ) x *
          |paper5RawPopulationXX eta u U t x| ^ 2))
    (hbound : ∀ n : ℕ,
      (∫ x : ℝ,
        capWeight eta (n : ℝ) x *
          |paper5RawPopulationXX eta u U t x| ^ 2) ≤ C) :
    Integrable (fun x =>
      (paper5WeightedPopulationXX eta u U t x) ^ 2) := by
  have hfull : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |paper5RawPopulationXX eta u U t x| ^ 2) :=
    fullWeightedL2_integrable_of_uniform_cap
      heta hraw_cont hcap hbound
  refine hfull.congr (Eventually.of_forall fun x => ?_)
  change Real.exp (2 * eta * x) *
      |paper5RawPopulationXX eta u U t x| ^ 2 =
    (paper5WeightedPopulationXX eta u U t x) ^ 2
  rw [paper5WeightedPopulationXX_eq_exp_mul_rawPopulationXX,
    mul_pow, sq_abs]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The formal weighted second derivative is continuous under the same `C²`
slice hypotheses already consumed by the diffusion identity. -/
theorem paper5WeightedPopulationXX_continuous
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U) :
    Continuous (paper5WeightedPopulationXX eta u U t) := by
  have hWcont : Continuous (paper5WeightedPopulation eta u U t) := by
    unfold paper5WeightedPopulation
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (hu2.continuous.sub hU2.continuous)
  have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hud : Continuous (deriv (u t)) :=
    hu2.continuous_deriv (by norm_num)
  have hUd : Continuous (deriv U) :=
    hU2.continuous_deriv (by norm_num)
  have hu2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (u t) := by
    simpa using hu2
  have hU2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) U := by
    simpa using hU2
  have hudd : Continuous (deriv (deriv (u t))) :=
    ((contDiff_succ_iff_deriv.mp hu2').2.2).continuous_deriv (by norm_num)
  have hUdd : Continuous (deriv (deriv U)) :=
    ((contDiff_succ_iff_deriv.mp hU2').2.2).continuous_deriv (by norm_num)
  have hiteru : Continuous (fun x => iteratedDeriv 2 (u t) x) := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one] using hudd
  have hiterU : Continuous (fun x => iteratedDeriv 2 U x) := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one] using hUdd
  unfold paper5WeightedPopulationXX
  exact ((continuous_const.mul hWcont).add
      (((continuous_const.mul hexp).mul (hud.sub hUd)))).add
    (hexp.mul (hiteru.sub hiterU))

/-- The weighted closeness integral is exactly the square integral of the
formal weighted population perturbation. -/
theorem paper5WeightedPopulation_sq_integrable_of_weighted_difference
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2)) :
    Integrable (fun x =>
      (paper5WeightedPopulation eta u U t x) ^ 2) := by
  refine hclose.congr (Eventually.of_forall fun x => ?_)
  change Real.exp (2 * eta * x) * |u t x - U x| ^ 2 =
    (Real.exp (eta * x) * (u t x - U x)) ^ 2
  rw [mul_pow, sq_abs]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- **Reduction of `hdiff_int`.**  Weighted closeness supplies the `W²`
factor, while an independently established weighted `Wₓₓ²` estimate supplies
the second factor.  Continuous `C²` representatives then make `W * Wₓₓ`
integrable by the whole-line Young inequality.

The genuinely analytic remaining premise is `hWxx2`; this theorem does not
claim to produce it from unweighted pointwise regularity. -/
theorem paper5WeightedPopulation_mul_XX_integrable_of_XX_sq
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2))
    (hWxx2 : Integrable (fun x =>
      (paper5WeightedPopulationXX eta u U t x) ^ 2)) :
    Integrable (fun x =>
      paper5WeightedPopulation eta u U t x *
        paper5WeightedPopulationXX eta u U t x) := by
  have hW2 := paper5WeightedPopulation_sq_integrable_of_weighted_difference
    hclose
  have hWcont : Continuous (paper5WeightedPopulation eta u U t) := by
    unfold paper5WeightedPopulation
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (hu2.continuous.sub hU2.continuous)
  exact integrable_mul_of_sq_integrable_of_continuous
    hWcont (paper5WeightedPopulationXX_continuous hu2 hU2) hW2 hWxx2

end ShenWork.Paper1

#print axioms ShenWork.Paper1.paper5WeightedPopulationXX_eq_exp_mul_rawPopulationXX
#print axioms ShenWork.Paper1.paper5WeightedPopulationXX_sq_integrable_of_uniform_raw_cap
#print axioms ShenWork.Paper1.paper5WeightedPopulationXX_continuous
#print axioms ShenWork.Paper1.paper5WeightedPopulation_mul_XX_integrable_of_XX_sq
