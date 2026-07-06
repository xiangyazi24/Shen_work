/-
  ShenWork/Paper2/IntervalResolverSourceWindowHuCoeffNoK1Inputs.lean

  Chi-zero resolver-source inputs whose representation coefficients are chosen
  from `HasTimeNeighborhoodSpectralAgreement`, while the power-source K1 fields
  are still derived from the explicit bounded patched-source package.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs
import ShenWork.Paper2.IntervalResolverSourceWindowHuCoeffInputs

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Chi-zero no-K1 resolver-source inputs after also deleting the explicit
`bc/hagree` fields.  The coefficients are fixed canonically by `Hu`; the compact
coefficient envelope and the bounded patched-source package remain honest
producer inputs. -/
structure ResolverSourceWindowHuCoeffNoK1Inputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) where
  henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
    ∃ E : ℕ → ℝ,
      Summable E ∧
      (∀ n, 0 ≤ E n) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n,
        unitIntervalCosineEigenvalue n * |huRestartCoeff Hu σ n| ≤ E n)
  hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T

/-- Fill the Task269 chi-zero no-K1 package from the thinner Hu-coefficient
surface. -/
def resolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs_of_huCoeffNoK1Inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuCoeffNoK1Inputs p D Hu) :
    ResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs p D where
  bc := huRestartCoeff Hu
  hagree := huRestartCoeff_agree Hu
  henv := H.henv
  hsrc0 := H.hsrc0

/-- In the chi-zero branch, Hu-coefficient/no-K1 inputs fill the Task268
envelope/no-joint package: `bc/hagree` come from `Hu`, while the K1 fields come
from the bounded patched-source package as in Task269. -/
def resolverSourceWindowEnvelopeOnlyNoJointInputs_of_huCoeffNoK1Inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (H : ResolverSourceWindowHuCoeffNoK1Inputs p D Hu) :
    ResolverSourceWindowEnvelopeOnlyNoJointInputs p D :=
  resolverSourceWindowEnvelopeOnlyNoJointInputs_of_envelopeOnlyNoJointNoK1Inputs
    hχ0 hα ha hb hu₀
    (resolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs_of_huCoeffNoK1Inputs H)

end ShenWork.Paper2.ResolverSourceWindowInput
