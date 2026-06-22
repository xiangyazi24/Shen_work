import ShenWork.Paper3.IntervalDomainPersistenceActualMInterface

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- The `part2ULower` field in the logistic input package requires eventual
domination by the displayed Theorem 2.1(2) threshold itself. -/
theorem logistic_part2_field_shape_exact
    {p : CM2Params} (h : IntervalDomainLogisticPersistenceInputs p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (u v : ℝ → intervalDomain.Point → ℝ)
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∀ᶠ t in atTop,
      ∀ x : intervalDomain.Point, theorem21Part2LowerU p ≤ u t x :=
  h.part2ULower ha hb hχ0 hm hβ hχ u v hsol

/-- The `part3ULower` field in the logistic input package requires eventual
domination by the displayed Theorem 2.1(3) threshold itself. -/
theorem logistic_part3_field_shape_exact
    {p : CM2Params} (h : IntervalDomainLogisticPersistenceInputs p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β)
    (u v : ℝ → intervalDomain.Point → ℝ)
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∀ᶠ t in atTop,
      ∀ x : intervalDomain.Point, theorem21Part3LowerU p ≤ u t x :=
  h.part3ULower ha hb hχ0 hm hβ u v hsol

/-- The raw Theorem 2.1(2) persistence field has the same exact threshold
shape as a liminf lower bound, not an eventual pointwise lower bound. -/
theorem uniformPart2Raw_field_shape_exact
    {p : CM2Params} (h : UniformPersistencePart2Raw intervalDomain p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (u v : ℝ → intervalDomain.Point → ℝ)
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    let lowerU :=
      ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
        (1 / p.α)
    lowerU ≤ liminfInfValue intervalDomain u ∧
      p.ν / p.μ * lowerU ^ p.γ ≤ liminfInfValue intervalDomain v :=
  h ha hb hχ0 hm hβ hχ u v hsol

/-- The raw Theorem 2.1(3) persistence field has the same exact threshold
shape as a liminf lower bound and is entered under `1 < p.m`. -/
theorem uniformPart3Raw_field_shape_exact
    {p : CM2Params} (h : UniformPersistencePart3Raw intervalDomain p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β)
    (u v : ℝ → intervalDomain.Point → ℝ)
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    let lowerU :=
      min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
        max (1 / (p.m - 1)) (1 / p.α)
    lowerU ≤ liminfInfValue intervalDomain u ∧
      p.ν / p.μ * lowerU ^ p.γ ≤ liminfInfValue intervalDomain v :=
  h ha hb hχ0 hm hβ u v hsol

/-- The exact-threshold field cannot be discharged from a bare
`liminf >= threshold` scalar statement. -/
theorem exact_threshold_liminf_obstruction (θ : ℝ) :
    Filter.liminf (fun t : ℝ => θ - Real.exp (-t)) atTop = θ ∧
      ¬ (∀ᶠ t in atTop, θ ≤ θ - Real.exp (-t)) :=
  liminf_threshold_not_eventually_exact θ

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.logistic_part2_field_shape_exact
#print axioms ShenWork.Paper3.logistic_part3_field_shape_exact
#print axioms ShenWork.Paper3.uniformPart2Raw_field_shape_exact
#print axioms ShenWork.Paper3.uniformPart3Raw_field_shape_exact
#print axioms ShenWork.Paper3.exact_threshold_liminf_obstruction
