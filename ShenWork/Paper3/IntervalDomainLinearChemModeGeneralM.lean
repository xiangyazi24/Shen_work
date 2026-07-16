/- Exact general-`m` modal multiplier of the eliminated linear chemotaxis flux. -/
import ShenWork.Paper3.IntervalDomainLinearChemMode

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateCosineSeries
open ShenWork.IntervalPicardLimitCoeffConv
open ShenWork.IntervalDomainResolverStrictPos

noncomputable section

/-- The eliminated linear signal flux realizes the paper-faithful general-`m`
chemotaxis correction in the full modal growth rate.  Unlike the legacy
wrapper, this identity does not specialize the population exponent to one. -/
theorem paper3LinearChemFlux_mode_eq_growthCorrection_generalM
    (p : CM2Params)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ)
    (hUcont : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1))
    (hsource_lin : Summable fun n : ℕ =>
      (paper3LinearEllipticSourceCoeffReal p uStar (u t) n) ^ 2) :
    -p.χ₀ * (((k : ℝ) * Real.pi) *
        intervalSineInner
          (fun x =>
            uStar ^ p.m * paper3SensitivityFactor p.β vStar *
              paper3LinearSignalGradient p uStar (u t) x) k) =
      (unitIntervalCosineEigenvalue k +
          unitIntervalLinearizedGrowth p uStar vStar k + p.a * p.α) *
        paper3PerturbationCoeffM u uStar t k := by
  rw [intervalSineInner_const_mul_p3]
  unfold paper3LinearSignalGradient
  rw [intervalSineInner_paper3ResolvedSourceGradient p hsource_lin k]
  rw [paper3LinearEllipticSourceCoeffReal_eq_perturbationCoeffM
    p uStar u t k hUcont]
  simp only [paper3SensitivityFactor]
  have hu : 0 < uStar := heq.u_pos
  have hvbase : 0 < 1 + vStar := by linarith [heq.v_nonneg]
  have hmu : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
    intervalNeumannResolver_denom_pos p k
  have hpowU :
      uStar ^ p.m * uStar ^ (p.γ - 1) =
        uStar ^ (p.m + p.γ - 1) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hpowV :
      (1 + vStar) ^ (-p.β) = 1 / (1 + vStar) ^ p.β := by
    simpa [one_div] using Real.rpow_neg hvbase.le p.β
  simp only [unitIntervalLinearizedGrowth, sigma,
    unitIntervalCosineEigenvalue, unitIntervalNeumannSpectrum,
    paper3PowerDeriv, intervalNeumannResolverGradWeight]
  rw [hpowV]
  field_simp [ne_of_gt hmu, ne_of_gt (Real.rpow_pos_of_pos hvbase p.β)]
  ring_nf at hpowU ⊢
  have hcombine :
      uStar ^ p.m * p.γ * uStar ^ (-1 + p.γ) =
        p.γ * uStar ^ (-1 + p.γ + p.m) := by
    calc
      uStar ^ p.m * p.γ * uStar ^ (-1 + p.γ) =
          p.γ * (uStar ^ p.m * uStar ^ (-1 + p.γ)) := by ring
      _ = p.γ * uStar ^ (-1 + p.γ + p.m) := by rw [hpowU]
  rw [hcombine]

#print axioms paper3LinearChemFlux_mode_eq_growthCorrection_generalM

end

end ShenWork.Paper3
