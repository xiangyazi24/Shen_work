import ShenWork.Paper3.ScalarLogisticDiniExact
import ShenWork.Paper3.IntervalDomainPersistenceInfCobounds
import ShenWork.Paper3.IntervalDomainPersistenceSpatialMinContinuity

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Positivity of the actual linear logistic growth coefficient in the
Theorem 2.1(2) small-sensitivity regime. -/
theorem actualLinearGrowthCoeff_pos
    {p : CM2Params} (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    0 < p.a - actualLinearChemLoss p := by
  have hTheta : 0 < Theta_beta (p.β - 1) :=
    Theta_beta_pos_of_nonneg (by linarith)
  have hden : 0 < p.μ * Theta_beta (p.β - 1) :=
    mul_pos p.hμ hTheta
  have hχmul : p.χ₀ * (p.μ * Theta_beta (p.β - 1)) < p.a := by
    rw [lt_div_iff₀ hden] at hχ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hχ
  simp only [actualLinearChemLoss]
  nlinarith

/-- Interval Part2 liminf conclusion from the genuine actual-linear Dini
minimum inequality, scalar logistic comparison, and v-transfer. -/
theorem intervalDomain_part2_liminfUV_of_actualLinearDini
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hD : ActualLinearSpatialMinimumDini p u)
    (hslope : ∀ t ∈ Set.Ioi (0 : ℝ),
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) -
              intervalDomainSpatialMin u t) / h))
    (hT0 : 0 < T0)
    (hv_cobdd : IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (v t))) :
    theorem21Part2LowerU p ≤ liminfInfValue intervalDomain u ∧
      p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤
        liminfInfValue intervalDomain v := by
  have hqa : 0 < p.a - actualLinearChemLoss p :=
    actualLinearGrowthCoeff_pos hβ hχ
  let q : CM2Params :=
    { N := p.N, hN := p.hN, α := p.α, γ := p.γ, m := p.m,
      μ := p.μ, ν := p.ν, χ₀ := p.χ₀,
      a := p.a - actualLinearChemLoss p, b := p.b, β := p.β,
      hα := p.hα, hγ := p.hγ, hm := p.hm,
      hμ := p.hμ, hν := p.hν, ha := hqa.le, hb := p.hb,
      hβ := p.hβ }
  have hDq : RightLowerDiniGE (intervalDomainSpatialMin u)
      (fun y => q.a * y - q.b * y ^ (1 + q.α)) (Set.Ioi 0) := by
    simpa [q, actualLinearLogisticRhs, actualLinearChemLoss] using
      hD.to_RightLowerDiniGE hslope
  have huq :
      (q.a / q.b) ^ (1 / q.α) ≤
        Filter.liminf (intervalDomainSpatialMin u) atTop :=
    logistic_liminf_ge_of_RightLowerDiniGE
      (q := q) hqa hb
      (fun T hT0T =>
        intervalDomainSpatialMin_continuousOn_of_positiveGlobalBoundedSolution
          hsol hT0 hT0T)
      hDq hT0
      (intervalDomainSpatialMin_pos_of_positiveGlobalBoundedSolution hsol hT0)
      (intervalDomain_infValue_isCoboundedUnder_of_positiveGlobalBoundedSolution
        hsol)
  have hθpos : 0 < theorem21Part2LowerU p := by
    simpa [theorem21Part2LowerU] using
      theorem_2_1_part2_lowerU_pos p ha hb hχ0 hm hβ hχ
  have hu : theorem21Part2LowerU p ≤ liminfInfValue intervalDomain u := by
    simpa [q, theorem21Part2LowerU, liminfInfValue,
      intervalDomainSpatialMin, intervalDomain, actualLinearChemLoss] using huq
  exact ⟨hu,
    intervalDomain_liminf_v_ge_of_u_liminf_lower'
      hsol hθpos hv_cobdd hu⟩

#print axioms actualLinearGrowthCoeff_pos
#print axioms intervalDomain_part2_liminfUV_of_actualLinearDini

end

end ShenWork.Paper3
