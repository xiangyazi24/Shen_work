/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceInputsNoLowerFrontier.lean

  χ₀ = 0 headline wrappers from the no-lower primitive resolver-source input
  frontier introduced in `IntervalDomainPPIDResolverSourceInputsNoLowerFrontier`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceInputsFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceInputsNoLowerFrontier

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with the primitive resolver-source lower-bound
field supplied from the u-side time-neighborhood spectral agreement. -/
theorem paper2_theorem_1_1_chiZero_of_windowInputsNoLowerSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoLower : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowInputsNoLowerSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowInputsSourceSpectralFrontier_of_windowInputsNoLowerSourceSpectralFrontier
        (hNoLower u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
no-lower primitive resolver-source inputs. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowInputsNoLowerSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoLower : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowInputsNoLowerSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowInputsSourceSpectralFrontier_of_iterateWindowInputsNoLowerSourceSpectralFrontier
        (hIterNoLower u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowInputsNoLowerSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowInputsNoLowerSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
