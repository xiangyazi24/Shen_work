/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointInputsFrontier.lean

  χ₀ = 0 headline wrappers from resolver-source envelope inputs carrying neither
  hbsum nor lifted joint continuity.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceEnvelopeOnlyInputsFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceEnvelopeOnlyNoJointInputsFrontier

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with resolver-source compact coefficient envelopes,
where per-time eigenvalue summability and lifted joint continuity are both
derived rather than carried as fields. -/
theorem paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
        (hThin u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
resolver-source envelope inputs carrying neither hbsum nor lifted joint
continuity. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
        (hIterThin u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
