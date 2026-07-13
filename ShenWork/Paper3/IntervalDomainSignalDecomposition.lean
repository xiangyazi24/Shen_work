/-
  Exact reconstruction of the eliminated elliptic signal perturbation from its
  linear and quadratic source pieces.
-/
import ShenWork.Paper3.IntervalDomainSignalComponentBounds
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.Paper2.IntervalResolverWeakBounds

namespace ShenWork.Paper3

open MeasureTheory Real
open ShenWork.PDE
open ShenWork.PDE.ResolventEstimate
open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalResolverWeakBounds

noncomputable section

lemma paper3IntervalEllipticLinearResolvedCoeff_re_eq
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) :
    (paper3IntervalEllipticLinearResolvedCoeff p uStar u k).re =
      paper3LinearEllipticSourceCoeffReal p uStar u k *
        intervalNeumannResolverWeight p k := by
  simp only [paper3IntervalEllipticLinearResolvedCoeff,
    shiftedNeumannResolventCoeff,
    paper3IntervalEllipticLinearSourceCoeff,
    paper3LinearEllipticSourceCoeffReal,
    intervalNeumannResolverWeight]
  have heq :
      (((p.μ : ℂ) + (shiftedNeumannEigenvalue 0 k : ℂ))⁻¹ *
          (cosineCoeffs
            (paper3IntervalEllipticLinearProfile p uStar u) k : ℂ)) =
        (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k)⁻¹ *
          cosineCoeffs
            (paper3IntervalEllipticLinearProfile p uStar u) k : ℝ) : ℂ) := by
    simp only [shiftedNeumannEigenvalue, add_zero, ← Complex.ofReal_add,
      ← Complex.ofReal_inv, Complex.ofReal_mul]
  rw [heq, Complex.ofReal_re]
  ring

lemma paper3IntervalEllipticRemainderResolvedCoeff_re_eq
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) :
    (paper3IntervalEllipticRemainderResolvedCoeff p uStar u k).re =
      paper3QuadraticEllipticSourceCoeffReal p uStar u k *
        intervalNeumannResolverWeight p k := by
  simp only [paper3IntervalEllipticRemainderResolvedCoeff,
    shiftedNeumannResolventCoeff,
    paper3IntervalEllipticRemainderSourceCoeff,
    paper3QuadraticEllipticSourceCoeffReal,
    intervalNeumannResolverWeight]
  have heq :
      (((p.μ : ℂ) + (shiftedNeumannEigenvalue 0 k : ℂ))⁻¹ *
          (cosineCoeffs
            (paper3IntervalEllipticRemainderProfile p uStar u) k : ℂ)) =
        (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k)⁻¹ *
          cosineCoeffs
            (paper3IntervalEllipticRemainderProfile p uStar u) k : ℝ) : ℂ) := by
    simp only [shiftedNeumannEigenvalue, add_zero, ← Complex.ofReal_add,
      ← Complex.ofReal_inv, Complex.ofReal_mul]
  rw [heq, Complex.ofReal_re]
  ring

/-- Exact value-series decomposition of the elliptic signal perturbation. -/
theorem paper3IntervalResolver_value_sub_eq_signalComponents
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ)
    (hlin : IntervalIntegrable
      (paper3IntervalEllipticLinearProfile p uStar u) volume 0 1)
    (hrem : IntervalIntegrable
      (paper3IntervalEllipticRemainderProfile p uStar u) volume 0 1)
    (hsource_u : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2)
    (hsource_star : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p (fun _ => uStar) k).re) ^ 2)
    (hsource_lin : Summable fun k : ℕ =>
      (paper3LinearEllipticSourceCoeffReal p uStar u k) ^ 2)
    (hsource_rem : Summable fun k : ℕ =>
      (paper3QuadraticEllipticSourceCoeffReal p uStar u k) ^ 2)
    (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x -
        intervalNeumannResolverR p (fun _ => uStar) x =
      paper3LinearSignalValue p uStar u x.1 +
        paper3QuadraticSignalValue p uStar u x.1 := by
  rw [resolverR_apply_eq, resolverR_apply_eq]
  have hsub :=
    (resolver_cosineSeries_summable_of_sourceL2 p hsource_u x.1).tsum_sub
      (resolver_cosineSeries_summable_of_sourceL2 p hsource_star x.1)
  simp only [unitIntervalCosineMode] at hsub
  rw [← hsub]
  simp only [paper3LinearSignalValue, paper3QuadraticSignalValue]
  rw [← paper3ResolvedSourceValue_add p hsource_lin hsource_rem x.1]
  unfold paper3ResolvedSourceValue
  refine tsum_congr (fun k => ?_)
  have hsplit := intervalNeumannResolverCoeff_split
    p uStar u k hlin hrem
  have hre := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hre
  rw [hre, paper3IntervalEllipticLinearResolvedCoeff_re_eq,
    paper3IntervalEllipticRemainderResolvedCoeff_re_eq]
  simp only [unitIntervalCosineMode]
  ring

/-- Exact differentiated-series decomposition of the elliptic signal
perturbation. -/
theorem paper3IntervalResolver_gradient_sub_eq_signalComponents
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ)
    (hlin : IntervalIntegrable
      (paper3IntervalEllipticLinearProfile p uStar u) volume 0 1)
    (hrem : IntervalIntegrable
      (paper3IntervalEllipticRemainderProfile p uStar u) volume 0 1)
    (hsource_u : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2)
    (hsource_star : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p (fun _ => uStar) k).re) ^ 2)
    (hsource_lin : Summable fun k : ℕ =>
      (paper3LinearEllipticSourceCoeffReal p uStar u k) ^ 2)
    (hsource_rem : Summable fun k : ℕ =>
      (paper3QuadraticEllipticSourceCoeffReal p uStar u k) ^ 2)
    (x : intervalDomainPoint) :
    intervalNeumannResolverRGrad p u x -
        intervalNeumannResolverRGrad p (fun _ => uStar) x =
      paper3LinearSignalGradient p uStar u x.1 +
        paper3QuadraticSignalGradient p uStar u x.1 := by
  rw [resolverRGrad_apply_eq, resolverRGrad_apply_eq]
  have hsub :=
    (resolver_sineSeries_summable_of_sourceL2 p hsource_u x.1).tsum_sub
      (resolver_sineSeries_summable_of_sourceL2 p hsource_star x.1)
  rw [← hsub]
  simp only [paper3LinearSignalGradient, paper3QuadraticSignalGradient]
  rw [← paper3ResolvedSourceGradient_add p hsource_lin hsource_rem x.1]
  unfold paper3ResolvedSourceGradient
  refine tsum_congr (fun k => ?_)
  have hsplit := intervalNeumannResolverCoeff_split
    p uStar u k hlin hrem
  have hre := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hre
  rw [hre, paper3IntervalEllipticLinearResolvedCoeff_re_eq,
    paper3IntervalEllipticRemainderResolvedCoeff_re_eq]
  simp only [intervalNeumannResolverGradWeight,
    intervalNeumannResolverWeight]
  ring

#print axioms paper3IntervalEllipticLinearResolvedCoeff_re_eq
#print axioms paper3IntervalResolver_value_sub_eq_signalComponents
#print axioms paper3IntervalResolver_gradient_sub_eq_signalComponents

end

end ShenWork.Paper3
