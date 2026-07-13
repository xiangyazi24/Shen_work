/-
  Audit of the interval model used by the Paper3 spectral linearization.

  `intervalDomain` is the legacy `m = 1` flux, while `intervalDomainM` carries
  the paper-faithful `u^m` flux.  The spectral growth `sigma` is the latter
  linearization.  These coincide on the legacy domain exactly along the
  explicitly assumed `m = 1` slice.
-/
import ShenWork.Paper3.IntervalDomainEllipticQuadraticRemainder
import ShenWork.PDE.IntervalDomain

namespace ShenWork.Paper3

open ShenWork.IntervalDomain

noncomputable section

/-- The paper-faithful chemotaxis divergence reduces to the legacy divergence
when `m = 1`. -/
theorem intervalDomainChemotaxisDivM_eq_of_m_eq_one
    (p : CM2Params) (hm : p.m = 1)
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalDomainChemotaxisDivM p u v x =
      intervalDomainChemotaxisDiv p u v x := by
  unfold intervalDomainChemotaxisDivM intervalDomainChemotaxisDiv
  congr 1
  funext y
  rw [hm, Real.rpow_one]

/-- Growth rate obtained by linearizing the actual legacy `intervalDomain`
flux, whose density factor is `u` rather than `u^m`. -/
def sigmaLegacyIntervalDomain
    (p : CM2Params) (uStar vStar lambdaN : ℝ) : ℝ :=
  -lambdaN +
    p.χ₀ * p.ν * p.γ *
      (uStar ^ p.γ * lambdaN) /
        ((1 + vStar) ^ p.β * (p.μ + lambdaN)) -
    p.a * p.α

/-- On `m = 1`, the paper spectral formula is exactly the linearization of the
legacy interval flux. -/
theorem sigma_eq_sigmaLegacyIntervalDomain_of_m_eq_one
    (p : CM2Params) (hm : p.m = 1)
    (uStar vStar lambdaN : ℝ) :
    sigma p uStar vStar lambdaN =
      sigmaLegacyIntervalDomain p uStar vStar lambdaN := by
  unfold sigma sigmaLegacyIntervalDomain
  rw [hm]
  congr 3
  congr 2
  congr 1
  ring

/-- A legacy interval classical solution is a faithful `intervalDomainM`
classical solution on the explicit `m=1` slice.  All domain fields coincide
definitionally except the chemotaxis divergence, handled by
`intervalDomainChemotaxisDivM_eq_of_m_eq_one`. -/
theorem isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    (p : CM2Params) (hm : p.m = 1) {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomain p T u v) :
    ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomainM p T u v := by
  open ShenWork.Paper2 in
  refine IsPaper2ClassicalSolution.of_components
    hsol.T_pos ?_ ?_ ?_ ?_ ?_ ?_
  · exact hsol.regularity
  · intro t x ht0 htT
    exact hsol.u_pos' ht0 htT
  · intro t x ht0 htT
    exact hsol.v_nonneg ht0 htT
  · intro t x ht0 htT hx
    have h := hsol.pde_u ht0 htT hx
    change
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x -
          p.χ₀ * intervalDomain.chemotaxisDiv p (u t) (v t) x +
            u t x * (p.a - p.b * u t x ^ p.α) at h
    change
      intervalDomainM.timeDeriv u t x =
        intervalDomainM.laplacian (u t) x -
          p.χ₀ * intervalDomainM.chemotaxisDiv p (u t) (v t) x +
            u t x * (p.a - p.b * u t x ^ p.α)
    change
      deriv (fun s : ℝ => u s x) t =
        intervalDomainLaplacian (u t) x -
          p.χ₀ * intervalDomainChemotaxisDivM p (u t) (v t) x +
            u t x * (p.a - p.b * u t x ^ p.α)
    rw [intervalDomainChemotaxisDivM_eq_of_m_eq_one p hm]
    exact h
  · intro t x ht0 htT hx
    exact hsol.pde_v ht0 htT hx
  · intro t x ht0 htT hx
    exact hsol.neumann ht0 htT hx

/-- Global legacy solutions transfer to the faithful domain on `m=1`. -/
theorem isPaper2GlobalClassicalSolution_intervalDomainM_of_m_eq_one
    (p : CM2Params) (hm : p.m = 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : ShenWork.Paper2.IsPaper2GlobalClassicalSolution
      intervalDomain p u v) :
    ShenWork.Paper2.IsPaper2GlobalClassicalSolution
      intervalDomainM p u v := by
  intro T hT
  exact isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm (hglobal T hT)

/-- Away from `m = 1`, the two displayed chemotactic multipliers can genuinely
differ; this concrete witness prevents silently identifying the two models. -/
theorem sigma_paper_multiplier_ne_legacy_witness :
    (2 : ℝ) ^ ((2 : ℝ) + 1 - 1) ≠ (2 : ℝ) ^ (1 : ℝ) := by
  norm_num [Real.rpow_two]

#print axioms intervalDomainChemotaxisDivM_eq_of_m_eq_one
#print axioms sigma_eq_sigmaLegacyIntervalDomain_of_m_eq_one
#print axioms isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
#print axioms isPaper2GlobalClassicalSolution_intervalDomainM_of_m_eq_one
#print axioms sigma_paper_multiplier_ne_legacy_witness

end

end ShenWork.Paper3
