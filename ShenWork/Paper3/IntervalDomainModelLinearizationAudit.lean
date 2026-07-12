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

/-- Away from `m = 1`, the two displayed chemotactic multipliers can genuinely
differ; this concrete witness prevents silently identifying the two models. -/
theorem sigma_paper_multiplier_ne_legacy_witness :
    (2 : ℝ) ^ ((2 : ℝ) + 1 - 1) ≠ (2 : ℝ) ^ (1 : ℝ) := by
  norm_num [Real.rpow_two]

#print axioms intervalDomainChemotaxisDivM_eq_of_m_eq_one
#print axioms sigma_eq_sigmaLegacyIntervalDomain_of_m_eq_one
#print axioms sigma_paper_multiplier_ne_legacy_witness

end

end ShenWork.Paper3
