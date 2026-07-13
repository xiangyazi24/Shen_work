import ShenWork.Paper3.IntervalDomainTheorem23PositiveEventual
import ShenWork.Paper3.IntervalDomainMinimalChiZeroHeat
import ShenWork.Paper3.IntervalDomainMinimalEventualConvergenceUpgrade

/-!
# Faithful eventual Theorem 2.3 on the unit interval

This capstone joins the positive-logistic and neutral minimal branches.  The
minimal branch is restricted to the physical-mass hyperplane; its zeroth mode
is conserved rather than artificially assigned a positive spectral gap.
-/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Qualitative global attraction for the nonpositive-sensitivity minimal
model on its physical-mass hyperplane. -/
theorem intervalDomain_chiNonpos_globallyAsymptoticallyStableMinimal
    (p : CM2Params) (hm : p.m = 1)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hχ : p.χ₀ ≤ 0)
    {uStar : ℝ} (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    GloballyAsymptoticallyStableMinimalOnPhysicalMass
      intervalDomain p eq.1 eq.2 := by
  dsimp
  intro u v huv hmass
  exact intervalDomain_minimal_chiNonpos_uniform_u_converges
    p hm ha0 hb0 hχ huv huStar hmass

/-- Unconditional faithful eventual-exponential minimal branch of Paper 3
Theorem 2.3 for the implemented one-dimensional `m = 1` equation. -/
theorem intervalDomain_Theorem_2_3_minimalEventual
    (p : CM2Params) (hm : p.m = 1)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hχ : p.χ₀ ≤ 0) :
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      EventuallyGloballyExponentiallyStableMinimal
        intervalDomain p intervalDomainSectorialStabilityNorms
          eq.1 eq.2 := by
  intro uStar huStar
  let eq := minimalEquilibrium p uStar
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal
      p ha0 hb0 uStar huStar
  have hgap : UnitIntervalLinearMassSpectralGap p eq.1 eq.2
      unitIntervalNeumannSpectrum.firstNonzero := by
    simpa [eq] using
      minimalEquilibrium_UnitIntervalLinearMassSpectralGap_of_chi_nonpos
        p hχ ha0 huStar
  have hglobal :
      GloballyAsymptoticallyStableMinimalOnPhysicalMass
        intervalDomain p eq.1 eq.2 := by
    simpa [eq] using
      intervalDomain_chiNonpos_globallyAsymptoticallyStableMinimal
        p hm ha0 hb0 hχ huStar
  refine ⟨hglobal, ?_⟩
  intro u v huv hmass
  exact intervalDomain_minimal_eventualC1_of_uniformSup_of_massGap
    p hm ha0 hb0 heq hgap huv hmass (hglobal u v huv hmass)

/-- Package-free, unconditional faithful eventual form of Paper 3 Theorem 2.3
for the currently implemented unit-interval equation (`m = 1`). -/
theorem intervalDomain_Theorem_2_3_EventualGlobalStability
    (p : CM2Params) (hm : p.m = 1) :
    Theorem_2_3_EventualGlobalStability
      intervalDomain p intervalDomainSectorialStabilityNorms := by
  intro hχ _hmLower
  constructor
  · exact intervalDomain_Theorem_2_3_positiveEventual p hm hχ
  · intro ha0 hb0
    exact intervalDomain_Theorem_2_3_minimalEventual
      p hm ha0 hb0 hχ

#print axioms
  intervalDomain_chiNonpos_globallyAsymptoticallyStableMinimal
#print axioms intervalDomain_Theorem_2_3_minimalEventual
#print axioms intervalDomain_Theorem_2_3_EventualGlobalStability

end

end ShenWork.Paper3
