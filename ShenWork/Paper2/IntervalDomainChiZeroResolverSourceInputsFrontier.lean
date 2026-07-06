/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceInputsFrontier.lean

  χ₀ = 0 headline wrappers from the primitive resolver-source window-input
  frontier introduced in `IntervalDomainPPIDResolverSourceInputsFrontier`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceInputsFrontier

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with resolver-source window data replaced by the
primitive global/per-compact input package. -/
theorem paper2_theorem_1_1_chiZero_of_windowInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_windowInputsSourceSpectralFrontier hInputs)

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
primitive resolver-source window inputs. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_iterateWindowInputsSourceSpectralFrontier
      hIterInputs)

#print axioms paper2_theorem_1_1_chiZero_of_windowInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowInputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
