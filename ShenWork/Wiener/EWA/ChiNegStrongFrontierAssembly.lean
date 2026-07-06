import ShenWork.Wiener.EWA.SourceChiNegUncondFix
import ShenWork.Wiener.EWA.ChiNegUniformLifespan
import ShenWork.Paper2.IntervalDomainTheorem11StrongPath

/-!
  # χ₀<0 strong faithful frontier assembly

  This file is the PPID-typed analogue of the faithful no-`hfp` frontier:
  the realization residual is carried over `PaperPositiveInitialDatum`, matching
  the datum class consumed by `StrongPath.chiNeg_theorem_1_1_of_strong`.

  It is only a typing/quantifier bridge.  The analytic realization frontier
  remains the explicit hypothesis `ChiNegStrongFaithfulRealizationFrontier p`.
-/

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2 (PaperPositiveInitialDatum Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (CoupledDuhamelReducedClassicalCore)

noncomputable section

namespace ShenWork.EWA

/-- **Strong faithful realization frontier.**

Same no-`hfp` realization carrier as `ChiNegFaithfulRealizationFrontier`, but
typed over the paper-faithful datum class.  This is the exact frontier shape
feeding `ChiNegDatumUniformConstructionStrong`. -/
def ChiNegStrongFaithfulRealizationFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PaperPositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-- The strong datum-uniform construction follows from the strong faithful
frontier by the same lifespan-reordering argument as the weak faithful route. -/
theorem chiNeg_strongDatumUniform_of_faithfulFrontier (p : CM2Params)
    (hF : ChiNegStrongFaithfulRealizationFrontier p) :
    ChiNegDatumUniformConstructionStrong p := by
  intro M hM
  obtain ⟨δ, hδpos, _⟩ :=
    exists_uniform_EWA_lifespan (χ₀ := p.χ₀)
      (LQbar := 0) (LGbar := 0) (MQbar := 0) (MGbar := 0) (ρ := 1)
      le_rfl le_rfl le_rfl le_rfl one_pos
  refine ⟨δ, hδpos, ?_⟩
  intro u0 hu0 hbd
  exact hF M hM δ hδpos hu0 hbd

/-- Strong faithful frontier implies the PPID-typed Paper 2 theorem via the
strong χ₀<0 path. -/
theorem chiNeg_theorem_1_1_of_strongFaithfulFrontier
    (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hF : ChiNegStrongFaithfulRealizationFrontier p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.chiNeg_theorem_1_1_of_strong
    p hchi ha hb hα hγ
    (chiNeg_strongDatumUniform_of_faithfulFrontier p hF)

section AxiomAudit

#print axioms chiNeg_strongDatumUniform_of_faithfulFrontier
#print axioms chiNeg_theorem_1_1_of_strongFaithfulFrontier

end AxiomAudit

end ShenWork.EWA
