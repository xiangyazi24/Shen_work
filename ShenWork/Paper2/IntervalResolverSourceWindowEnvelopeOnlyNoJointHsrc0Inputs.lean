/-
  ShenWork/Paper2/IntervalResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs.lean

  χ₀ = 0 resolver-source envelope/no-joint inputs whose representation
  coefficients and compact eigenvalue envelope are derived from the bounded
  patched-source package.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs
import ShenWork.Paper2.IntervalPicardLimitBddAdapterPatched

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift intervalDomainPoint
  intervalDomainConstExtend)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalPicardLimitRestart (limitCoeff)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalPicardLimitBddAdapter (windowEigEnv windowEigEnv_summable)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Source-only resolver-source inputs for the χ₀ = 0 branch.  The coefficient
family is fixed to the canonical `limitCoeff`, and both representation agreement
and compact-window eigenvalue envelopes are derived from `hsrc0`. -/
structure ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T

/-- The canonical `limitCoeff` package fills the no-K1 envelope/no-joint surface
from the bounded patched-source package in the χ₀ = 0 branch. -/
def resolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs_of_hsrc0Inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hχ0 : p.χ₀ = 0)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs p D) :
    ResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs p D := by
  let M₀ : ℝ := 2 * sSup (Set.range fun x => |u₀ x|)
  let hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀ :=
    initial_cosineCoeffs_bound_of_positiveInitialDatum hu₀
  have hM₀ : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  exact
    { bc := fun σ k => limitCoeff p u₀ D.u σ k
      hagree := by
        intro σ hσ hσT x hx
        exact ShenWork.Paper2.TimeNhdSubtype.limit_lift_eq_cosineSeries_of_subtypeCont_patched
          p hχ0 u₀ D.u hu₀.admissible.2 hu₀_bound H.hsrc0 hσ hσT.le
          (fun y hy => by
            simp only [intervalDomainLift, dif_pos hy]
            exact D.hmild σ hσ hσT.le ⟨y, hy⟩)
          (fun s hs hsσ =>
            ShenWork.Paper2.ConstExtendAdapter.logisticSource_constExtend_continuous
              D hs (hsσ.trans hσT.le))
          hx
      henv := by
        intro a b ha hb hab
        let E : ℕ → ℝ := windowEigEnv M₀ H.hsrc0.M a (H.hsrc0.env (a / 2))
        have ha2 : 0 < a / 2 := by linarith
        have ha2T : a / 2 ≤ D.T := by linarith
        refine ⟨E,
          windowEigEnv_summable ha
            (H.hsrc0.henv_summable (a / 2) ha2 ha2T),
          ?_, ?_⟩
        · intro n
          have hLambda : 0 ≤ unitIntervalCosineEigenvalue n := by
            unfold unitIntervalCosineEigenvalue
            positivity
          have htail_nn : 0 ≤ H.hsrc0.env (a / 2) n :=
            le_trans (abs_nonneg _)
              (H.hsrc0.henv_bound (a / 2) ha2 (a / 2) le_rfl ha2T n)
          unfold E windowEigEnv
          refine add_nonneg (add_nonneg ?_ ?_) htail_nn
          · exact mul_nonneg hM₀ (mul_nonneg hLambda (Real.exp_pos _).le)
          · exact mul_nonneg (mul_nonneg ha2.le H.hsrc0.hM_nonneg)
              (mul_nonneg hLambda (Real.exp_pos _).le)
        · intro σ hσ n
          exact
            ShenWork.Paper2.BddAdapterPatched.eigenvalue_mul_abs_limitCoeff_le_uniform_patched
              p u₀ D.u hM₀ hu₀_bound H.hsrc0 ha hσ.1
              (le_trans hσ.2 hb.le) n
      hsrc0 := H.hsrc0 }

/-- In the χ₀ = 0 branch, source-only inputs fill the Task268 envelope/no-joint
package after deriving both the canonical coefficients/envelope and the
power-source K1 fields. -/
def resolverSourceWindowEnvelopeOnlyNoJointInputs_of_hsrc0Inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs p D) :
    ResolverSourceWindowEnvelopeOnlyNoJointInputs p D :=
  resolverSourceWindowEnvelopeOnlyNoJointInputs_of_envelopeOnlyNoJointNoK1Inputs
    hχ0 hα ha hb hu₀
    (resolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs_of_hsrc0Inputs hχ0 hu₀ H)

end ShenWork.Paper2.ResolverSourceWindowInput
