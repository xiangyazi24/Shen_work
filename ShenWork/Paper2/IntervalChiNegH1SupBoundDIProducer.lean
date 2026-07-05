import ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer

/-!
# H¹ sup-bound DI producer

This file removes a bookkeeping burden from `H1SupBoundDIDataBefore`: callers
may state the pointwise bounds using the canonical square-root witnesses for
`lapL2sq` and `2 * H1energy`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer

/-- Canonical nonnegative representative of the H¹ dissipation norm. -/
def H1lapL2Norm (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  Real.sqrt (lapL2sq u τ)

/-- Canonical nonnegative representative of the H¹ gradient norm. -/
def H1gradL2Norm (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  Real.sqrt (2 * H1energy u τ)

theorem H1lapL2Norm_sq (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    H1lapL2Norm u τ ^ 2 = lapL2sq u τ := by
  unfold H1lapL2Norm
  exact Real.sq_sqrt (lapL2sq_nonneg u τ)

theorem lapL2sq_eq_H1lapL2Norm_sq
    (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    lapL2sq u τ = H1lapL2Norm u τ ^ 2 :=
  (H1lapL2Norm_sq u τ).symm

theorem H1gradL2Norm_sq (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    H1gradL2Norm u τ ^ 2 = 2 * H1energy u τ := by
  unfold H1gradL2Norm
  have hnonneg : 0 ≤ 2 * H1energy u τ :=
    mul_nonneg (by norm_num) (H1energy_nonneg u τ)
  exact Real.sq_sqrt hnonneg

theorem H1lapL2Norm_nonneg (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    0 ≤ H1lapL2Norm u τ := by
  unfold H1lapL2Norm
  exact Real.sqrt_nonneg _

theorem H1gradL2Norm_nonneg (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    0 ≤ H1gradL2Norm u τ := by
  unfold H1gradL2Norm
  exact Real.sqrt_nonneg _

/-- Sup-bound H¹ DI data with the norm witnesses fixed to the canonical square
roots.  This is still a pointwise physical-split package; it only removes the
separate `X`/`Z` witness fields. -/
structure H1SupBoundSqrtDIDataBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ) : Prop where
  hchi : 0 ≤ -p.χ₀
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  hL : 0 ≤ L
  point : ∀ τ, 0 < τ → τ < T →
    H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ) ∧
      (-p.χ₀) * taxisX τ ≤
        (-p.χ₀) * (V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ)) ∧
      (-p.χ₀) * uvxx τ ≤
        (-p.χ₀) * (M * (V₂ * H1lapL2Norm u τ)) ∧
      reactX τ ≤ L * (H1gradL2Norm u τ) ^ 2

/-- Convert the canonical-square-root sup-bound package into the existing
`H1SupBoundDIDataBefore` shape. -/
theorem H1SupBoundDIDataBefore_of_sqrtData
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX) :
    H1SupBoundDIDataBefore p u T V₁ V₂ M L := by
  refine
    { hchi := hdata.hchi
      hV1 := hdata.hV1
      hV2 := hdata.hV2
      hM := hdata.hM
      hL := hdata.hL
      point := ?_ }
  intro τ hτ0 hτT
  rcases hdata.point τ hτ0 hτT with ⟨hEnergy, htaxis, huvxx, hreact⟩
  refine
    ⟨taxisX τ, uvxx τ, reactX τ, H1lapL2Norm u τ,
      H1gradL2Norm u τ, hEnergy, ?_, ?_, ?_,
      htaxis, huvxx, hreact⟩
  · exact lapL2sq_eq_H1lapL2Norm_sq u τ
  · exact H1gradL2Norm_sq u τ
  · exact H1lapL2Norm_nonneg u τ

/-- The square-root sup-bound package yields the compact RHS-bound package. -/
theorem H1IdentityRHSBoundBefore_of_supBoundSqrtDIData
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX) :
    H1IdentityRHSBoundBefore p u T
      (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L)
      ((-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2) :=
  H1IdentityRHSBoundBefore_of_supBoundDIData
    (H1SupBoundDIDataBefore_of_sqrtData hdata)

/-- Bounded-before route using square-root sup-bound data plus the already
separate explicit RHS-integrability and local-start carries. -/
theorem intervalDomain_boundedBefore_of_H1supBoundSqrtDI_integrableRHS_local_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1supBoundDI_integrableRHS_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 hcont0 hRHS
    (H1SupBoundDIDataBefore_of_sqrtData hdata)
    hlocal

/-- Bounded-before route using square-root sup-bound data, explicit
RHS-integrability, and the scalar-DI-produced local H¹ seed. -/
theorem intervalDomain_boundedBefore_of_H1supBoundSqrtDI_integrableRHS_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L : ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore params u T V₁ V₂ M L
      taxisX uvxx reactX) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1supBoundDI_integrableRHS_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 hcont0 hRHS
    (H1SupBoundDIDataBefore_of_sqrtData hdata)

/-- One explicit physical-split package carrying both square-root sup-bound
data and interval-integrability of the same RHS functions.  This is still a
frontier package: it does not prove the physical split estimates. -/
structure H1SupBoundSqrtRHSIntegrableBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ) : Prop where
  sqrtData : H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
    taxisX uvxx reactX
  rhs_intervalIntegrable : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b

/-- The combined sqrt/RHS package gives the explicit RHS-integrability package
using the identity field already contained in its square-root data. -/
theorem H1IdentityRHSIntegrableBefore_of_supBoundSqrtRHSData
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hdata : H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX := by
  refine
    { identity := ?_
      rhs_intervalIntegrable := hdata.rhs_intervalIntegrable }
  intro τ hτ
  exact (hdata.sqrtData.point τ hτ.1 hτ.2).1

/-- Square-root sup-bound data plus closed-window continuity of the same
explicit RHS gives the combined sqrt/RHS package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_continuousOn_Icc
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hRHSCont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn
        (H1IdentityRHSValue p u taxisX uvxx reactX) (Set.Icc a b)) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX := by
  refine
    { sqrtData := hdata
      rhs_intervalIntegrable := ?_ }
  have hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
    H1IdentityRHSIntegrableBefore_of_continuousOn_Icc
      (fun τ hτ => (hdata.point τ hτ.1 hτ.2).1) hRHSCont
  intro a b ha hab hbT
  exact hRHS.rhs_intervalIntegrable (a := a) (b := b) ha hab hbT

/-- Component continuity on closed time windows upgrades square-root sup-bound
data to the combined sqrt/RHS package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_component_continuousOn_Icc
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hLap : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX := by
  refine
    { sqrtData := hdata
      rhs_intervalIntegrable := ?_ }
  have hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
    H1IdentityRHSIntegrableBefore_of_component_continuousOn_Icc
      (fun τ hτ => (hdata.point τ hτ.1 hτ.2).1)
      hLap hTaxis hUvxx hReact
  intro a b ha hab hbT
  exact hRHS.rhs_intervalIntegrable (a := a) (b := b) ha hab hbT

/-- Bounded-before route from one explicit physical-split frontier package,
plus the remaining `u_xx` continuity and restricted local-start carries. -/
theorem intervalDomain_boundedBefore_of_H1supBoundSqrtRHS_local_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtRHSIntegrableBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1supBoundSqrtDI_integrableRHS_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 hcont0
    (H1IdentityRHSIntegrableBefore_of_supBoundSqrtRHSData hdata)
    hdata.sqrtData hlocal

/-- Bounded-before route from one explicit physical-split frontier package,
with the restricted local H¹ seed produced from the scalar differential
inequality. -/
theorem intervalDomain_boundedBefore_of_H1supBoundSqrtRHS_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    {V₁ V₂ M L : ℝ}
    (hdata : H1SupBoundSqrtRHSIntegrableBefore params u T V₁ V₂ M L
      taxisX uvxx reactX) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1supBoundSqrtDI_integrableRHS_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 hcont0
    (H1IdentityRHSIntegrableBefore_of_supBoundSqrtRHSData hdata)
    hdata.sqrtData

/-- Existential-only variant of `H1SupBoundSqrtDIDataBefore`.  This is useful
when a later proof naturally produces pointwise physical-split witnesses, but it
does not expose global RHS functions for `H1IdentityRHSIntegrableBefore`. -/
structure H1SupBoundSqrtDIDataBeforeExists
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  hchi : 0 ≤ -p.χ₀
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  hL : 0 ≤ L
  point : ∀ τ, 0 < τ → τ < T →
    ∃ taxisX uvxx reactX : ℝ,
      H1EnergyIdentity p u τ taxisX uvxx reactX ∧
      (-p.χ₀) * taxisX ≤
        (-p.χ₀) * (V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ)) ∧
      (-p.χ₀) * uvxx ≤
        (-p.χ₀) * (M * (V₂ * H1lapL2Norm u τ)) ∧
      reactX ≤ L * (H1gradL2Norm u τ) ^ 2

/-- Convert existential-only canonical-square-root sup-bound data into the
existing witness-heavy `H1SupBoundDIDataBefore` shape. -/
theorem H1SupBoundDIDataBefore_of_sqrtData_exists
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hdata : H1SupBoundSqrtDIDataBeforeExists p u T V₁ V₂ M L) :
    H1SupBoundDIDataBefore p u T V₁ V₂ M L := by
  refine
    { hchi := hdata.hchi
      hV1 := hdata.hV1
      hV2 := hdata.hV2
      hM := hdata.hM
      hL := hdata.hL
      point := ?_ }
  intro τ hτ0 hτT
  rcases hdata.point τ hτ0 hτT with
    ⟨taxisX, uvxx, reactX, hEnergy, htaxis, huvxx, hreact⟩
  refine
    ⟨taxisX, uvxx, reactX, H1lapL2Norm u τ, H1gradL2Norm u τ,
      hEnergy, ?_, ?_, ?_, htaxis, huvxx, hreact⟩
  · exact lapL2sq_eq_H1lapL2Norm_sq u τ
  · exact H1gradL2Norm_sq u τ
  · exact H1lapL2Norm_nonneg u τ

#print axioms H1SupBoundDIDataBefore_of_sqrtData
#print axioms H1IdentityRHSBoundBefore_of_supBoundSqrtDIData
#print axioms intervalDomain_boundedBefore_of_H1supBoundSqrtDI_integrableRHS_local_before
#print axioms intervalDomain_boundedBefore_of_H1supBoundSqrtDI_integrableRHS_before
#print axioms H1IdentityRHSIntegrableBefore_of_supBoundSqrtRHSData
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_continuousOn_Icc
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_component_continuousOn_Icc
#print axioms intervalDomain_boundedBefore_of_H1supBoundSqrtRHS_local_before
#print axioms intervalDomain_boundedBefore_of_H1supBoundSqrtRHS_before
#print axioms H1SupBoundDIDataBefore_of_sqrtData_exists

end ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
