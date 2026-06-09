/-
  Constant-extension adapter: bridge from paper-faithful subtype hypotheses
  to the spectral chain's Continuous (lift ...) requirements.

  The spectral chain (IntervalPicardLimitRestart, IntervalPicardLimitTimeNhd,
  IntervalPicardLimitSourceData) takes `Continuous (intervalDomainLift u₀)` and
  `Continuous (logisticLifted p (D.u s))`. Both are FALSE for positive data
  (the zero-extension lift is discontinuous at boundary endpoints).

  The paper (Section 2.2) works on C(Ω̄) = [0,1]. The semigroup S(t) acts on
  C(Ω̄), and S(t)f only depends on f|_{[0,1]}.

  This file provides the adapter: from `Continuous u₀` (subtype, = C(Ω̄)),
  construct the constant extension `constExtend u₀` (globally continuous),
  call the spectral chain with `constExtend` in place of `lift`, and transfer
  results back to `lift` via the agreement on [0,1].

  The key property: `intervalFullSemigroupOperator t (constExtend f) x =
  intervalFullSemigroupOperator t (lift f) x` because the kernel integral
  is over [0,1] where both agree.
-/
import ShenWork.Paper2.IntervalPicardLimitSourceData
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.PDE.IntervalDomainContinuousExtension

open Set Filter Topology MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted intervalLogisticSource)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap
  (GradientMildHalfStepRestartData HasRestartCosineRepresentations
   hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData)

noncomputable section

namespace ShenWork.Paper2.ConstExtendAdapter

/-- **Cosine coefficients of the constant extension equal those of the lift.**
Both integrate against cos(nπy) over [0,1] where they agree. -/
theorem cosineCoeffs_constExtend_eq_lift
    (f : intervalDomainPoint → ℝ) (n : ℕ) :
    cosineCoeffs (intervalDomainConstExtend f) n =
    cosineCoeffs (intervalDomainLift f) n := by
  sorry -- Integral over [0,1] where constExtend = lift

/-- **Constant extension of the logistic source is globally continuous.**
`intervalLogisticSource p (D.u s)` is continuous on the compact subtype
(composition of continuous functions). Its constant extension is globally
continuous (constant outside [0,1], continuous on [0,1], values match at
endpoints). -/
theorem logisticSource_constExtend_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ D.T) :
    Continuous (intervalDomainConstExtend (intervalLogisticSource p (D.u s))) := by
  sorry -- constExtend_continuous applied to logisticSource continuous on subtype

/-- **The comprehensive adapter: produce GradientMildHalfStepRestartData
from subtype continuity via constant extension.**

This is the key bridge function. It:
1. Constructs `intervalDomainConstExtend u₀` (globally continuous)
2. Calls `gradientMildHalfStepRestartData_for_limit` with the constant
   extension substituted via cosineCoeffs congr
3. Returns the same `GradientMildHalfStepRestartData D`

The existing spectral chain sees `constExtend u₀` (which IS continuous)
instead of `lift u₀` (which is NOT continuous). Since
`cosineCoeffs (constExtend u₀) = cosineCoeffs (lift u₀)` and the
semigroup operator gives the same result, the chain produces identical
output. -/
theorem hasRestartData_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- cosine representation of D.u (from iterate convergence)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T → Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * ShenWork.CosineSpectrum.cosineMode n x) (Icc 0 1))
    -- K2 bounds (time-restricted)
    (hpost : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Icc (0:ℝ) 1, 0 < intervalDomainLift (D.u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Icc (0:ℝ) 1, intervalDomainLift (D.u σ) x ≤ D.M)
    (hG1t : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Icc (0:ℝ) 1,
      |deriv (intervalDomainLift (D.u σ)) x| ≤ G1)
    (hG2t : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Icc (0:ℝ) 1,
      |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2)
    -- K1 source-coefficient time-C¹ data
    (adott : ℝ → ℕ → ℝ)
    (hderivt : ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (ShenWork.IntervalMildPicardRegularity.logisticSourceFun p.a p.b p.α
          (intervalDomainLift (D.u r))) k) (adott σ k) σ)
    (hadotcontt : ∀ k, Continuous (fun σ => adott σ k))
    (Mdott : ℝ)
    (hMdott : ∀ σ, 0 ≤ σ → ∀ k, |adott σ k| ≤ Mdott)
    -- shifted K1
    (adotS : ℝ → ℝ → ℕ → ℝ)
    (hderivS : ∀ t, ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (ShenWork.IntervalMildPicardRegularity.logisticSourceFun p.a p.b p.α
          (intervalDomainLift (D.u (t/2 + r)))) k) (adotS t σ k) σ)
    (hadotcontS : ∀ t, ∀ k, Continuous (fun σ => adotS t σ k))
    (MdotS : ℝ)
    (hMdotS : ∀ t, ∀ σ, 0 ≤ σ → ∀ k, |adotS t σ k| ≤ MdotS)
    -- slice continuity (subtype, per paper)
    (hLc : ∀ t, 0 < t → t < D.T →
      ∀ s, 0 < s → s ≤ t → Continuous (intervalLogisticSource p (D.u s))) :
    GradientMildHalfStepRestartData D := by
  sorry

end ShenWork.Paper2.ConstExtendAdapter
