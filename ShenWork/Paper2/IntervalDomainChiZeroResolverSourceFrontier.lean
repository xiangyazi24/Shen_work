/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceFrontier.lean

  χ₀ = 0 headline wrappers from the resolver-source window and spatial-K1
  frontiers introduced in the PPID resolver-source modules.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroRestartCoreFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceDecayFrontier
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceFrontier

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- The χ₀ = 0 headline route with the resolver-source witness replaced by the
windowed source data package. -/
theorem paper2_theorem_1_1_chiZero_of_windowSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_windowSourceSpectralFrontier hWindow)

/-- The χ₀ = 0 headline route with logistic source data replaced by
Picard-iterate convergence data and the resolver-source witness replaced by the
windowed source package. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_iterateWindowSourceSpectralFrontier hIterWindow)

/-- The χ₀ = 0 headline route with resolver-source decay lowered to the
spatial-K1 source package. -/
theorem paper2_theorem_1_1_chiZero_of_spatialK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSpatialK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_spatialK1SourceSpectralFrontier hSpatialK1)

/-- The χ₀ = 0 headline route with Picard-iterate convergence data and
resolver-source decay lowered to the spatial-K1 source package. -/
theorem paper2_theorem_1_1_chiZero_of_iterateSpatialK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSpatialK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_iterateSpatialK1SourceSpectralFrontier
      hIterSpatialK1)

#print axioms paper2_theorem_1_1_chiZero_of_windowSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_spatialK1SourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateSpatialK1SourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
