/-
  ShenWork/Paper2/IntervalDomainChiZeroRestartCoreFrontier.lean

  χ₀ = 0 headline wrappers from the smaller PPID restart-core frontier
  surfaces introduced in `IntervalDomainPPIDRestartCoreFrontier`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDRestartCoreFrontier

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with the residual reduced to the smaller
restart/core spectral frontier package. -/
theorem paper2_theorem_1_1_chiZero_of_restartCoreSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hCore : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumRestartCoreSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_restartCoreSpectralFrontier hCore)

/-- The χ₀ = 0 headline route with the resolver direct spectral field replaced
by the source-witness package. -/
theorem paper2_theorem_1_1_chiZero_of_sourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_sourceSpectralFrontier hSource)

/-- The χ₀ = 0 headline route with the logistic source data replaced by
Picard-iterate convergence data and the resolver direct spectral field replaced
by the source-witness package. -/
theorem paper2_theorem_1_1_chiZero_of_iterateSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_iterateSourceSpectralFrontier hIterSource)

#print axioms paper2_theorem_1_1_chiZero_of_restartCoreSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_sourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
