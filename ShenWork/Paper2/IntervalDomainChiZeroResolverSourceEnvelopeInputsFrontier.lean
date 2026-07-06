/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceEnvelopeInputsFrontier.lean

  χ₀ = 0 headline wrappers from the envelope primitive resolver-source input
  frontier introduced in
  `IntervalDomainPPIDResolverSourceEnvelopeInputsFrontier`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceJointInputsFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceEnvelopeInputsFrontier

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with resolver-source spatial K2 reduced to a
compact-window coefficient envelope. -/
theorem paper2_theorem_1_1_chiZero_of_windowEnvelopeInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowJointInputsSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
        (hEnvelope u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
envelope primitive resolver-source inputs. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
        (hIterEnvelope u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowEnvelopeInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeInputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
