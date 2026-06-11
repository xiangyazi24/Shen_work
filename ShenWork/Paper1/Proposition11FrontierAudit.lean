import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper2.IntervalDomainStatementAssembly
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual
import ShenWork.Paper2.IntervalDomainThm11ChiZeroCoreProvider

/-!
  Audit wrappers for the Paper1 Proposition 1.1 frontier and the interval-domain
  local-existence residual that previous attempts identified.

  This file is intentionally additive.  It does not prove the missing analytic
  Cauchy theory; it records the exact fields that existing assembly consumes and
  exposes the interval-domain local-existence field that can be reached from the
  existing conditional Picard surfaces.
-/

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardLimit)

noncomputable section

namespace ShenWork.Paper1.Proposition11FrontierAudit

/-- The Paper1 Proposition 1.1 global-existence field. -/
abbrev GlobalExistenceField : Prop :=
  ∀ p : CMParams,
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∃ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v

/-- The Paper1 Proposition 1.1 negative-sensitivity bound field. -/
abbrev MaxNegField : Prop :=
  ∀ p : CMParams, p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
    ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
      (∀ M, (∀ x, u₀ x ≤ M) →
        ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
      UniformLimsupLe u 1

/-- The Paper1 Proposition 1.1 positive-sensitivity bound field. -/
abbrev BoundPosField : Prop :=
  ∀ p : CMParams,
    (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
      (0 < p.χ ∧
        p.χ <
          min ((p.m + p.γ - 1) / (2 * p.m - 1))
            ((p.m + p.γ - 1) / (p.γ - 1)) ∧
        p.α = p.m + p.γ - 1) →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
    ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
      UniformEventuallyBounded u ∧
      (0 < p.χ → p.χ < 1 →
        UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α)))

/-- The exact three fields needed for Paper1 Proposition 1.1. -/
structure FrontierFields : Prop where
  existence : GlobalExistenceField
  max_neg : MaxNegField
  bound_pos : BoundPosField

/-- Paper1 Proposition 1.1 consumes only the first three proposition fields. -/
theorem proposition_1_1_of_frontierFields
    (h : FrontierFields) :
    Proposition_1_1 :=
  Proposition_1_1.of_global_existence_and_bounds
    h.existence h.max_neg h.bound_pos

/-- The full Paper1 proposition frontier has two extra convergence fields that
are not used by Proposition 1.1. -/
theorem proposition_1_1_of_paper1FrontierData
    (hData : Paper1PropositionFrontierData) :
    Proposition_1_1 :=
  proposition_1_1_of_frontierFields
    { existence := hData.existence
      max_neg := hData.max_neg
      bound_pos := hData.bound_pos }

#print axioms proposition_1_1_of_frontierFields
#print axioms proposition_1_1_of_paper1FrontierData

end ShenWork.Paper1.Proposition11FrontierAudit

namespace ShenWork.Paper2.IntervalDomainProposition11FrontierAudit

open ShenWork.Paper2.ChiNegResidual
open ShenWork.Paper2.ConeQuantBridge
open ShenWork.Paper2.HresWiring
open ShenWork.Paper2.Thm11ChiZeroCoreProvider

/-- The interval-domain Paper2 Proposition 1.1 local-existence field. -/
abbrev LocalExistenceField (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u

/-- The interval-domain Paper2 Proposition 1.1 finite-horizon alternative field. -/
abbrev FiniteHorizonAlternativeField (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v →
      InitialTrace intervalDomain u₀ u →
        FiniteHorizonAlternative intervalDomain Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)

/-- Paper2 interval-domain Proposition 1.1 from its two actual frontier fields. -/
theorem intervalDomain_proposition_1_1_of_fields
    (p : CM2Params)
    (hlocal : LocalExistenceField p)
    (halt : FiniteHorizonAlternativeField p) :
    Proposition_1_1 intervalDomain p :=
  intervalDomainPaper2_Proposition_1_1_of_frontierData p
    { localExistence := hlocal
      finiteHorizonAlternative := halt }

/-- The χ₀ = 0 Picard-limit restart frontier gives the interval local factory. -/
theorem localFactory_chiZero_of_picardLimitFrontier
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α)
    (hPLF : PicardLimitRestartFrontier p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  quantitativeLocalExistence_chiZero p hχ0 hα hPLF

/-- Per-datum local existence obtained from the χ₀ = 0 Picard-limit frontier. -/
theorem localExistence_chiZero_of_picardLimitFrontier
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α)
    (hPLF : PicardLimitRestartFrontier p) :
    LocalExistenceField p :=
  localExistence_of_coupledFluxClassicalLocalExistenceResidual p
    (localFactory_chiZero_of_picardLimitFrontier p hχ0 hα hPLF)

/-- The narrowed χ₀ = 0 Wdata surface also gives the interval local factory. -/
theorem localFactory_chiZero_of_wdata
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α)
    (Hiter : IterCoeffTimeContProvider p)
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        WdataProvider p u₀ D) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  quantitativeLocalExistence_chiZero_wdata p hχ0 ha hb hα Hiter HWdata

/-- Per-datum local existence obtained from the narrowed χ₀ = 0 Wdata surface. -/
theorem localExistence_chiZero_of_wdata
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α)
    (Hiter : IterCoeffTimeContProvider p)
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        WdataProvider p u₀ D) :
    LocalExistenceField p :=
  localExistence_of_coupledFluxClassicalLocalExistenceResidual p
    (localFactory_chiZero_of_wdata p hχ0 ha hb hα Hiter HWdata)

/-- The datum-owned χ₀ = 0 supply gives the same interval local factory. -/
theorem localFactory_chiZero_of_datumSupply
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α)
    (Hsupply : DatumProviderSupply p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  quantitativeLocalExistence_chiZero_datum p hχ0 ha hb hα Hsupply

/-- Per-datum local existence obtained from the datum-owned χ₀ = 0 supply. -/
theorem localExistence_chiZero_of_datumSupply
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α)
    (Hsupply : DatumProviderSupply p) :
    LocalExistenceField p :=
  localExistence_of_coupledFluxClassicalLocalExistenceResidual p
    (localFactory_chiZero_of_datumSupply p hχ0 ha hb hα Hsupply)

/-- Interval-domain Proposition 1.1 with local existence supplied by the
χ₀ = 0 Picard-limit frontier.  The finite-horizon alternative remains explicit. -/
theorem intervalDomain_proposition_1_1_of_chiZero_picardLimitFrontier
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α)
    (hPLF : PicardLimitRestartFrontier p)
    (halt : FiniteHorizonAlternativeField p) :
    Proposition_1_1 intervalDomain p :=
  intervalDomain_proposition_1_1_of_fields p
    (localExistence_chiZero_of_picardLimitFrontier p hχ0 hα hPLF) halt

#print axioms intervalDomain_proposition_1_1_of_fields
#print axioms localExistence_chiZero_of_picardLimitFrontier
#print axioms localExistence_chiZero_of_wdata
#print axioms localExistence_chiZero_of_datumSupply
#print axioms intervalDomain_proposition_1_1_of_chiZero_picardLimitFrontier

end ShenWork.Paper2.IntervalDomainProposition11FrontierAudit
