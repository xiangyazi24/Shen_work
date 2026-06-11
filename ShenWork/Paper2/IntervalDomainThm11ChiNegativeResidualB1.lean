import ShenWork.Paper2.IntervalDomainThm11ChiNegativeResidual
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ChiNegativeResidual

/-- B1 one-field residual after removing the separate global-existence field.

This is the coupled-flux, quantitative classical local Cauchy factory.  The
lifespan is uniform for all positive interval data whose absolute value is
bounded by the same `M`; this is the exact local input consumed by the
restart-and-glue continuation wiring. -/
structure ChiNegativeNonminimalCoupledLocalExistenceResidual
    (p : CM2Params) : Prop where
  localExistence :
    ∀ M : ℝ, 0 < M → ∃ delta : ℝ, 0 < delta ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
          ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p delta u v ∧
            InitialTrace intervalDomain u₀ u

/-- The B1 residual is definitionally the existing coupled-flux quantitative
local-existence residual used by the restart continuation theorem. -/
theorem coupledFluxResidual_of_coupledLocalResidual
    {p : CM2Params}
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual p :=
  H.localExistence

/-- The one-field quantitative residual still gives the old per-datum
`localExistence` field of the two-field residual. -/
theorem localExistence_of_coupledLocalResidual
    (p : CM2Params)
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u :=
  ChiNegResidual.localExistence_of_coupledFluxClassicalLocalExistenceResidual
    p H.localExistence

/-- B1 reduction: in the negative nonminimal interval-domain branch, the
separate global-existence field is replaced by the coupled-flux quantitative
local factory.  Lemma 3.1 is used downstream through
`ChiNegResidual.coupledFlux_interiorSupNorm_le_regimeBound`, which feeds the
uniform restart-and-glue continuation theorem. -/
theorem
    Theorem_1_1_intervalDomain_chiNegative_nonminimal_of_coupledLocalResidual
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    Theorem_1_1 intervalDomain p :=
  ChiNegResidual.theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ H.localExistence

/-- The old `globalSolutionExists` field is recovered from the one-field
quantitative local residual in the negative nonminimal regime.  This is an
extraction from the just-built one-field theorem, not an assumption of the old
two-field residual. -/
theorem globalSolutionExists_of_coupledLocalResidual
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        1 ≤ p.m →
          ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
            InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀ hm
  have hThm :
      Theorem_1_1 intervalDomain p :=
    Theorem_1_1_intervalDomain_chiNegative_nonminimal_of_coupledLocalResidual
      p hχ ha hb hα hγ H
  obtain ⟨_T, _hT, u, v, _hsol, htrace, _hbound, hglobal⟩ :=
    (hThm (le_of_lt hχ)).1 ha hb u₀ hu₀
  exact ⟨u, v, hglobal hm, htrace⟩

/-- Explicit 2-field-to-1-field reduction for the committed residual, under
the negative nonminimal regime. -/
theorem coupledResidual_of_coupledLocalResidual
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    ChiNegativeNonminimalCoupledExistenceResidual p where
  localExistence :=
    localExistence_of_coupledLocalResidual p H
  globalSolutionExists :=
    globalSolutionExists_of_coupledLocalResidual p hχ ha hb hα hγ H

#check ChiNegativeNonminimalCoupledExistenceResidual.localExistence
#check ChiNegativeNonminimalCoupledExistenceResidual.globalSolutionExists
#check ChiNegativeNonminimalCoupledLocalExistenceResidual.localExistence
#check ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual
#check Lemma31Closure.Lemma_3_1_intervalDomain
#check nonminimal_supNorm_bound_from_Lemma_3_1_intervalDomain_and_trace
#check ChiNegResidual.coupledFlux_interiorSupNorm_le_regimeBound
#check RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData

#print axioms nonminimal_supNorm_bound_from_Lemma_3_1_intervalDomain_and_trace
#print axioms ChiNegResidual.coupledFlux_interiorSupNorm_le_regimeBound
#print axioms globalSolutionExists_of_coupledLocalResidual
#print axioms coupledResidual_of_coupledLocalResidual
#print axioms Theorem_1_1_intervalDomain_chiNegative_nonminimal_of_coupledLocalResidual

end ShenWork.Paper2.ChiNegativeResidual
