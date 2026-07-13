/- Exact modal multiplier of the eliminated linear chemotaxis flux. -/
import ShenWork.Paper3.IntervalDomainResolvedSourceSineCoeff
import ShenWork.Paper3.IntervalDomainFullModeDuhamel
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit
import ShenWork.Paper3.IntervalDomainLocalNemytskiiBounds

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

/-- Linear elliptic source coefficients are the scalar derivative of the
power source times the perturbation cosine coefficients. -/
theorem paper3LinearEllipticSourceCoeffReal_eq_perturbationCoeffM
    (p : CM2Params) (uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ)
    (hUcont : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1)) :
    paper3LinearEllipticSourceCoeffReal p uStar (u t) k =
      (p.ν * paper3PowerDeriv p.γ uStar) *
        paper3PerturbationCoeffM u uStar t k := by
  have hphi : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hUcont.sub continuousOn_const
  unfold paper3LinearEllipticSourceCoeffReal
  rw [show paper3IntervalEllipticLinearProfile p uStar (u t) =
      fun x => (p.ν * paper3PowerDeriv p.γ uStar) *
        paper3IntervalPerturbationProfile uStar (u t) x by rfl]
  rw [cosineCoeffs_const_mul_of_intervalIntegrable
      (p.ν * paper3PowerDeriv p.γ uStar) k hphi]
  rw [show paper3IntervalPerturbationProfile uStar (u t) =
      fun x => intervalDomainLift (u t) x - uStar by rfl]
  rw [cosineCoeffs_sub_eq hUcont continuousOn_const k]
  rw [cosineCoeffs_const]
  simp only [paper3PerturbationCoeffM, solutionCoeffM,
    paper3EquilibriumCosineCoeff]

lemma intervalSineInner_const_mul_p3
    (c : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    intervalSineInner (fun x => c * f x) k =
      c * intervalSineInner f k := by
  unfold intervalSineInner
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk]
    rw [show (∫ y in (0 : ℝ)..1,
        Real.sin ((k : ℝ) * Real.pi * y) * (c * f y)) =
      c * ∫ y in (0 : ℝ)..1,
        Real.sin ((k : ℝ) * Real.pi * y) * f y by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring]
    ring

/-- The eliminated linear signal flux produces exactly the chemotaxis part of
the full modal growth rate.  This is the complete multiplier, not the pure
Neumann heat multiplier. -/
theorem paper3LinearChemFlux_mode_eq_growthCorrection
    (p : CM2Params) (hm : p.m = 1)
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
  rw [hm, hpowV]
  have hpowUone :
      uStar ^ (1 : ℝ) * uStar ^ (p.γ - 1) = uStar ^ p.γ := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hpowExp : uStar ^ (1 + p.γ - 1) = uStar ^ p.γ := by
    congr 1
    ring
  rw [hpowExp]
  field_simp [ne_of_gt hmu, ne_of_gt (Real.rpow_pos_of_pos hvbase p.β)]
  ring_nf at hpowUone ⊢
  have hcombine :
      uStar ^ (1 : ℝ) * p.γ * uStar ^ (-1 + p.γ) =
        p.γ * uStar ^ p.γ := by
    calc
      uStar ^ (1 : ℝ) * p.γ * uStar ^ (-1 + p.γ) =
          p.γ * (uStar ^ (1 : ℝ) * uStar ^ (-1 + p.γ)) := by ring
      _ = p.γ * uStar ^ p.γ := by rw [hpowUone]
  rw [hcombine]

#print axioms paper3LinearEllipticSourceCoeffReal_eq_perturbationCoeffM
#print axioms paper3LinearChemFlux_mode_eq_growthCorrection

end

end ShenWork.Paper3
