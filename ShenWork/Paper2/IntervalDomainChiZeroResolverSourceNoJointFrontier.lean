/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceNoJointFrontier.lean

  χ₀ = 0 headline wrappers from the no-joint-continuity resolver-source input
  frontier introduced in `IntervalDomainPPIDResolverSourceNoJointFrontier`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceJointInputsFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceNoJointFrontier

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with lifted joint continuity removed from the
resolver-source input surface and supplied by the already-carried u-side
spectral agreement. -/
theorem paper2_theorem_1_1_chiZero_of_windowNoJointInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowJointInputsSourceSpectralFrontier_of_windowNoJointInputsSourceSpectralFrontier
        (hNoJoint u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
no-joint-continuity resolver-source inputs. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowNoJointInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier
        (hIterNoJoint u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowNoJointInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowNoJointInputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
