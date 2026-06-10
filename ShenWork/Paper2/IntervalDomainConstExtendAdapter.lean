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
import ShenWork.Paper2.IntervalDomainRestartPackaging

open Set Filter Topology MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted intervalGradientDuhamelMap)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
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
    cosineCoeffs (intervalDomainLift f) n :=
  ShenWork.IntervalDomain.cosineCoeffs_constExtend_eq_lift f n

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
  apply constExtend_continuous
  -- intervalLogisticSource p (D.u s) = fun x => (D.u s x) * (p.a - p.b * (D.u s x) ^ p.α)
  have hcu : Continuous (D.u s) := D.hcont s hs hsT
  unfold intervalLogisticSource
  exact hcu.mul
    (continuous_const.sub (continuous_const.mul (hcu.rpow_const (fun _ => Or.inr p.hα.le))))

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
def hasRestartData_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- H1 datum (subtype continuity + bounded cosine coefficients)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    -- mild fixed-point (time-localized)
    (hfix : ∀ s, 0 < s → s < D.T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (D.u s) x = intervalGradientDuhamelMap p u₀ D.u s ⟨x, hx⟩)
    -- weak limit-source package (horizon-bounded)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (D.u s)) k) D.T)
    -- K2: per-slice cosine representation + sup/positivity bounds (time-localized)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T → Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Icc 0 1))
    (hpost : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Icc (0:ℝ) 1, 0 < intervalDomainLift (D.u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Icc (0:ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup)
    -- K2: gradient/Hessian bounds, PER-COMPACT (the satisfiable form)
    (hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Icc (0:ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Icc (0:ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2)
    -- K1: UNSHIFTED source-coefficient time-C¹ data on (0,T), per-compact bound
    (adott : ℝ → ℕ → ℝ)
    (hderivt : ∀ σ, 0 < σ → σ < D.T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (D.u r))) k) (adott σ k) σ)
    (hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 D.T))
    (hMdott : ∀ a' b', 0 < a' → b' < D.T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adott σ k| ≤ Mdot)
    -- slice continuity (subtype, per paper)
    (hLc : ∀ t, 0 < t → t < D.T →
      ∀ s, 0 < s → s ≤ t → Continuous (intervalLogisticSource p (D.u s))) :
    GradientMildHalfStepRestartData D :=
  -- Delegated to the time-localized subtype producer.  The original (pre-V2)
  -- hypothesis list — global-`σ` `bc/hbsum/hpost/hubt`, a global `D.M` sup bound,
  -- global-σ K1 with the `t/2`-shifted family, and a single `Continuous (fun σ =>
  -- adott σ k)` — was UNSATISFIABLE for positive data on `(0, D.T)` (the genuine
  -- families are regular only on compact windows; the `t/2`-shifted block is
  -- redundant — the clamped engine supplies the shift internally).  Retyped to the
  -- V2 ledger shapes (no callers; verified by grep), it is the same data
  -- `RestartPackaging.gradientMildHalfStepRestartData_localized_of_subtypeCont`
  -- consumes, bridging `hLc` to the constExtend slice-continuity form.
  RestartPackaging.gradientMildHalfStepRestartData_localized_of_subtypeCont
    hχ0 D hα ha hb hu₀_cont hu₀_bound hfix hsrc0
    bc hbsum hagree hpost hubt hG1t hG2t
    adott hderivt hadotcontt hMdott
    (fun t ht htT s hs hst =>
      constExtend_continuous (hLc t ht htT s hs hst))

end ShenWork.Paper2.ConstExtendAdapter
