import ShenWork.Paper1.Theorem12EnergyProducer
import ShenWork.PDE.GagliardoNirenberg

open Filter MeasureTheory Set Topology
open intervalIntegral

noncomputable section

namespace ShenWork.Paper1

/-!
# Whole-line weighted `H¹` pointwise envelope

The paper's Step 4 restarts at a fixed positive time and uses the one-dimensional
Sobolev estimate to turn the weighted `L²` population and gradient bounds into
the pointwise envelope (5.38).  The lemma below records the translation-uniform
whole-line form of that estimate.  It uses a unit interval beginning at the
evaluation point, so no assertion about limits of an arbitrary representative
at spatial infinity is needed.
-/

/-- A continuously differentiable real function whose value and derivative
are square-integrable is uniformly bounded.  The displayed constant is the
unit-interval Agmon bound with both local integrals enlarged to the whole
line. -/
theorem wholeLine_H1_sq_pointwise_le
    {f f' : ℝ → ℝ}
    (hf : Continuous f)
    (hf' : Continuous f')
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf2 : Integrable (fun x => f x ^ 2))
    (hf'2 : Integrable (fun x => f' x ^ 2))
    (x : ℝ) :
    f x ^ 2 ≤
      2 * (∫ y, f y ^ 2) +
        2 * Real.sqrt (∫ y, f y ^ 2) *
          Real.sqrt (∫ y, f' y ^ 2) := by
  let g : ℝ → ℝ := fun y => f (x + y)
  let g' : ℝ → ℝ := fun y => f' (x + y)
  have hg : Continuous g := hf.comp (continuous_const.add continuous_id)
  have hg' : Continuous g' := hf'.comp (continuous_const.add continuous_id)
  have hgderiv : ∀ y, HasDerivAt g (g' y) y := by
    intro y
    simpa [g, g'] using
      (hderiv (x + y)).comp y
        ((hasDerivAt_const y x).add (hasDerivAt_id y))
  have hg2 : Integrable (fun y => g y ^ 2) := by
    simpa [g, add_comm] using hf2.comp_add_right x
  have hg'2 : Integrable (fun y => g' y ^ 2) := by
    simpa [g', add_comm] using hf'2.comp_add_right x
  have hgg' : Integrable (fun y => g y * g' y) :=
    integrable_mul_of_sq_integrable_of_continuous hg hg' hg2 hg'2
  have hlocal := ShenWork.GagliardoNirenberg.agmon_inequality_interval
    (L := (1 : ℝ)) (by norm_num) hg.continuousOn
    (fun y _hy => hgderiv y) (hg'.intervalIntegrable 0 1)
    hg2.intervalIntegrable hg'2.intervalIntegrable
    hgg'.intervalIntegrable (x := (0 : ℝ)) (by norm_num)
  have hI :
      (∫ y in (0 : ℝ)..1, g y ^ 2) ≤ ∫ y, g y ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun y => sq_nonneg (g y)) hg2
  have hI' :
      (∫ y in (0 : ℝ)..1, g' y ^ 2) ≤ ∫ y, g' y ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun y => sq_nonneg (g' y)) hg'2
  have hI0 : 0 ≤ ∫ y in (0 : ℝ)..1, g y ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun y _ => sq_nonneg (g y))
  have hI'0 : 0 ≤ ∫ y in (0 : ℝ)..1, g' y ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun y _ => sq_nonneg (g' y))
  have hsqrt := Real.sqrt_le_sqrt hI'
  have hprod :
      2 * Real.sqrt (∫ y in (0 : ℝ)..1, g y ^ 2) *
          Real.sqrt (∫ y in (0 : ℝ)..1, g' y ^ 2) ≤
        2 * Real.sqrt (∫ y, g y ^ 2) * Real.sqrt (∫ y, g' y ^ 2) := by
    have hsqrt0 : 0 ≤ Real.sqrt (∫ y in (0 : ℝ)..1, g y ^ 2) :=
      Real.sqrt_nonneg _
    have hsqrtI := Real.sqrt_le_sqrt hI
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hsqrtI (by norm_num)) hsqrt
      (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hbound := hlocal.trans (add_le_add (mul_le_mul_of_nonneg_left hI (by norm_num)) hprod)
  have hgint : (∫ y, g y ^ 2) = ∫ y, f y ^ 2 := by
    simpa [g] using
      (integral_add_left_eq_self (fun y : ℝ => f y ^ 2) x)
  have hg'int : (∫ y, g' y ^ 2) = ∫ y, f' y ^ 2 := by
    simpa [g'] using
      (integral_add_left_eq_self (fun y : ℝ => f' y ^ 2) x)
  simpa [g, hgint, hg'int] using hbound

/-- Existential uniform bound form of the whole-line `H¹` estimate. -/
theorem exists_uniform_abs_bound_of_wholeLine_H1
    {f f' : ℝ → ℝ}
    (hf : Continuous f)
    (hf' : Continuous f')
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf2 : Integrable (fun x => f x ^ 2))
    (hf'2 : Integrable (fun x => f' x ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  let K : ℝ :=
    2 * (∫ y, f y ^ 2) +
      2 * Real.sqrt (∫ y, f y ^ 2) *
        Real.sqrt (∫ y, f' y ^ 2)
  have hK0 : 0 ≤ K := by
    exact (sq_nonneg (f 0)).trans
      (wholeLine_H1_sq_pointwise_le hf hf' hderiv hf2 hf'2 0)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro x
  have hx := wholeLine_H1_sq_pointwise_le hf hf' hderiv hf2 hf'2 x
  change f x ^ 2 ≤ K at hx
  have hsqrt : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK0
  nlinarith [sq_abs (f x), abs_nonneg (f x), Real.sqrt_nonneg K]

/-- The formal weighted derivative is continuous under spatial `C²`
regularity of the solution slice and wave profile. -/
theorem paper5WeightedPopulationX_continuous
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U) :
    Continuous (paper5WeightedPopulationX eta u U t) := by
  have hW : Continuous (paper5WeightedPopulation eta u U t) := by
    unfold paper5WeightedPopulation
    fun_prop
  unfold paper5WeightedPopulationX
  exact (continuous_const.mul hW).add
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((hu2.continuous_deriv (by norm_num)).sub
        (hU2.continuous_deriv (by norm_num))))

/-- Weighted `H¹` regularity at one positive slice gives the uniform
pointwise weighted-error envelope used in (5.38). -/
theorem exists_paper5WeightedPopulation_uniform_abs_bound_of_H1
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U)
    (hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta u U t x ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta u U t x ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |paper5WeightedPopulation eta u U t x| ≤ C := by
  have hWcont : Continuous (paper5WeightedPopulation eta u U t) := by
    unfold paper5WeightedPopulation
    fun_prop
  have hWxcont : Continuous (paper5WeightedPopulationX eta u U t) :=
    paper5WeightedPopulationX_continuous hu2 hU2
  have hderiv : ∀ x, HasDerivAt
      (paper5WeightedPopulation eta u U t)
      (paper5WeightedPopulationX eta u U t x) x := by
    intro x
    exact paper5WeightedPopulation_space_hasDerivAt
      (hu2.differentiable (by norm_num) x)
      (hU2.differentiable (by norm_num) x)
  exact exists_uniform_abs_bound_of_wholeLine_H1
    hWcont hWxcont hderiv hW2 hWx2

/-- Unconjugating the weighted `H¹` bound gives the precise exponentially
decaying pointwise perturbation envelope from the paper's (5.38). -/
theorem exists_weightedDifference_pointwise_envelope_of_H1
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (u t)) (hU2 : ContDiff ℝ 2 U)
    (hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta u U t x ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta u U t x ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |u t x - U x| ≤ C * Real.exp (-eta * x) := by
  rcases exists_paper5WeightedPopulation_uniform_abs_bound_of_H1
      hu2 hU2 hW2 hWx2 with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x
  have hraw := hbound x
  rw [paper5WeightedPopulation, abs_mul,
    abs_of_pos (Real.exp_pos _)] at hraw
  have hexp : Real.exp (-eta * x) * Real.exp (eta * x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    |u t x - U x| =
        Real.exp (-eta * x) *
          (Real.exp (eta * x) * |u t x - U x|) := by
            rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (-eta * x) * C :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
    _ = C * Real.exp (-eta * x) := by ring

section AxiomAudit

#print axioms wholeLine_H1_sq_pointwise_le
#print axioms exists_uniform_abs_bound_of_wholeLine_H1
#print axioms paper5WeightedPopulationX_continuous
#print axioms exists_paper5WeightedPopulation_uniform_abs_bound_of_H1
#print axioms exists_weightedDifference_pointwise_envelope_of_H1

end AxiomAudit

end ShenWork.Paper1
