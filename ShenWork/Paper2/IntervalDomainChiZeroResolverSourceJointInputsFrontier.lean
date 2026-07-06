/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceJointInputsFrontier.lean

  χ₀ = 0 headline wrappers from the joint-continuity resolver-source input
  frontier introduced in `IntervalDomainPPIDResolverSourceJointInputsFrontier`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceInputsFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceJointInputsFrontier

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with primitive resolver-source input data reduced
to joint continuity of the lifted solution plus the spatial K2/power-source
fields. -/
theorem paper2_theorem_1_1_chiZero_of_windowJointInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowInputsSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
        (hJoint u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
joint-continuity resolver-source inputs. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowJointInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowInputsSourceSpectralFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
        (hIterJoint u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowJointInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowJointInputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
