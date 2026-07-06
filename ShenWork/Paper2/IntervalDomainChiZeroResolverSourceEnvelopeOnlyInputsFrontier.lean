/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceEnvelopeOnlyInputsFrontier.lean

  χ₀ = 0 headline wrappers from no-`hbsum` envelope primitive
  resolver-source inputs.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceEnvelopeInputsFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceEnvelopeOnlyInputsFrontier

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with resolver-source spatial K2 reduced to
compact-window coefficient envelopes, and per-time eigenvalue summability
derived from singleton envelopes. -/
theorem paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
        (hEnvelopeOnly u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
no-`hbsum` envelope primitive resolver-source inputs. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
        (hIterEnvelopeOnly u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
