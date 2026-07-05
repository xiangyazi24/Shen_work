import ShenWork.Paper2.IntervalChiNegH1AverageWiring
import ShenWork.Paper2.IntervalChiNegH1EnergyIdentity

/-!
# H¹ scalar differential-inequality producer

This file connects the pointwise H¹ energy identity and algebraic RHS bounds to
the scalar FTC package used by the H¹ averaging reducer.  It deliberately keeps
the scalar continuity/integrability data and the `u_xx` L¹-continuity frontier
upstream.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1AverageWiring

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer

/-- Scalar regularity fields needed by interval FTC on `H1energy u`. -/
structure H1ScalarRegularityBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  hcont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    ContinuousOn (H1energy u) (Set.Icc a b)
  hderivInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b

/-- Pointwise H¹ energy identity plus an `A * y + B` bound for its RHS. -/
structure H1IdentityRHSBoundBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T A B : ℝ) : Prop where
  hA : 0 ≤ A
  hB : 0 ≤ B
  bound : ∀ τ, 0 < τ → τ < T →
    ∃ taxisX uvxx reactX : ℝ,
      H1EnergyIdentity p u τ taxisX uvxx reactX ∧
        (-(lapL2sq u τ) + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX ≤
          A * H1energy u τ + B)

/-- Produce the scalar H¹ differential-inequality package from scalar FTC
regularity and a pointwise H¹ identity/RHS bound. -/
theorem H1ScalarDIOnBefore_of_identityRHSBound
    {p : CM2Params} {T A B : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hreg : H1ScalarRegularityBefore u T)
    (hId : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B := by
  refine
    { hA := hId.hA
      hB := hId.hB
      hcont := ?_
      hderivInt := ?_
      hhasDerivRight := ?_
      hDI := ?_ }
  · intro a b ha hab hb
    exact hreg.hcont ha hab hb
  · intro a b ha hab hb
    exact hreg.hderivInt ha hab hb
  · intro a b r ha _hab hb hr
    have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
    have hrT : r < T := lt_trans hr.2 hb
    rcases hId.bound r hr0 hrT with ⟨taxisX, uvxx, reactX, hEnergy, _hrhs⟩
    unfold H1EnergyIdentity at hEnergy
    have hderiv_eq :
        deriv (H1energy u) r =
          (-(lapL2sq u r) + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX) :=
      hEnergy.deriv
    simpa [hderiv_eq] using hEnergy.hasDerivWithinAt (s := Set.Ioi r)
  · intro r hr0 hrT
    rcases hId.bound r hr0 hrT with ⟨taxisX, uvxx, reactX, hEnergy, hrhs⟩
    unfold H1EnergyIdentity at hEnergy
    have hderiv_eq :
        deriv (H1energy u) r =
          (-(lapL2sq u r) + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX) :=
      hEnergy.deriv
    calc
      deriv (H1energy u) r
          = (-(lapL2sq u r) + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX) :=
            hderiv_eq
      _ ≤ A * H1energy u r + B := hrhs

/-- Pointwise data needed by `h1_diffIneq_of_sup_bounds` at every time. -/
structure H1SupBoundDIDataBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  hchi : 0 ≤ -p.χ₀
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  hL : 0 ≤ L
  point : ∀ τ, 0 < τ → τ < T →
    ∃ taxisX uvxx reactX X Z : ℝ,
      H1EnergyIdentity p u τ taxisX uvxx reactX ∧
      lapL2sq u τ = X ^ 2 ∧
      Z ^ 2 = 2 * H1energy u τ ∧
      0 ≤ X ∧
      (-p.χ₀) * taxisX ≤ (-p.χ₀) * (V₁ * (X * Z)) ∧
      (-p.χ₀) * uvxx ≤ (-p.χ₀) * (M * (V₂ * X)) ∧
      reactX ≤ L * Z ^ 2

/-- Convert the existing sup-bound algebraic DI hypotheses into the compact
identity/RHS-bound package used by the scalar reducer. -/
theorem H1IdentityRHSBoundBefore_of_supBoundDIData
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hdata : H1SupBoundDIDataBefore p u T V₁ V₂ M L) :
    H1IdentityRHSBoundBefore p u T
      (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L)
      ((-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2) := by
  refine
    { hA := ?_
      hB := ?_
      bound := ?_ }
  · have hterm : 0 ≤ 2 * (-p.χ₀) ^ 2 * V₁ ^ 2 := by positivity
    have hLterm : 0 ≤ 2 * L := mul_nonneg (by norm_num) hdata.hL
    linarith
  · positivity
  · intro τ hτ0 hτT
    rcases hdata.point τ hτ0 hτT with
      ⟨taxisX, uvxx, reactX, X, Z, hEnergy, hXsq, hZsq, hXnn,
        htaxis, huvxx, hreact⟩
    refine ⟨taxisX, uvxx, reactX, hEnergy, ?_⟩
    exact h1_diffIneq_of_sup_bounds
      hdata.hchi hdata.hV1 hdata.hV2 hdata.hM hdata.hL
      hXsq hZsq hXnn htaxis huvxx hreact

/-- Sup-bound H¹ differential-inequality data plus scalar FTC regularity close
the paper-positive bounded-before route through the 1D P3 bypass. -/
theorem intervalDomain_boundedBefore_of_paperPositive_H1supBoundDI_local
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
    {V₁ V₂ M L Ylocal : ℝ}
    (hreg : H1ScalarRegularityBefore u T)
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  let A : ℝ := 2 * (-params.χ₀) ^ 2 * V₁ ^ 2 + 2 * L
  let B : ℝ := (-params.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2
  have hId : H1IdentityRHSBoundBefore params u T A B := by
    simpa [A, B] using H1IdentityRHSBoundBefore_of_supBoundDIData hdata
  have hDI : H1ScalarDIOnBefore u T A B :=
    H1ScalarDIOnBefore_of_identityRHSBound hreg hId
  exact intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local
    hbounded ha hu₀ hT hsol htrace hfrontier hDI hlocal

/-- Restricted-time variant of
`intervalDomain_boundedBefore_of_paperPositive_H1supBoundDI_local`.

The local H¹ start is only required where the solution is in force (`τ < T`);
the L²/window inputs are produced internally by the 1D bypass. -/
theorem intervalDomain_boundedBefore_of_paperPositive_H1supBoundDI_local_before
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
    {V₁ V₂ M L Ylocal : ℝ}
    (hreg : H1ScalarRegularityBefore u T)
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  let A : ℝ := 2 * (-params.χ₀) ^ 2 * V₁ ^ 2 + 2 * L
  let B : ℝ := (-params.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2
  have hId : H1IdentityRHSBoundBefore params u T A B := by
    simpa [A, B] using H1IdentityRHSBoundBefore_of_supBoundDIData hdata
  have hDI : H1ScalarDIOnBefore u T A B :=
    H1ScalarDIOnBefore_of_identityRHSBound hreg hId
  exact intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier hDI hlocal

/-- Upstream `u_xx` L¹-continuity shape for the finite-difference H¹ identity
producer.  This file records the interface only; it does not prove it. -/
def H1UxxL1ContBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∀ τ, 0 < τ → τ < T → ∀ ε > 0, ∃ δ > 0,
    ∀ s, |s - τ| < δ → s ∈ Set.Ioo (0 : ℝ) T →
      ∫ x in (0 : ℝ)..1,
        ‖deriv (fun y : ℝ => deriv (intervalDomainLift (u s)) y) x -
          deriv (fun y : ℝ => deriv (intervalDomainLift (u τ)) y) x‖ ≤ ε

/-- The `H1UxxL1ContBefore` frontier is exactly the pointwise L¹-continuity
input expected by the finite-difference H¹ identity producer. -/
theorem H1EnergyIdentity_of_classicalSolution_and_H1UxxL1ContBefore
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hUxx : H1UxxL1ContBefore u T) :
    ∃ taxisX uvxx reactX,
      H1EnergyIdentity p u τ taxisX uvxx reactX :=
  ShenWork.Paper2.IntervalChiNegH1EnergyIdentity.H1EnergyIdentity_of_classicalSolution_and_uxxL1Cont
    hsol hτ (hUxx τ hτ.1 hτ.2)

#print axioms H1ScalarDIOnBefore_of_identityRHSBound
#print axioms H1IdentityRHSBoundBefore_of_supBoundDIData
#print axioms intervalDomain_boundedBefore_of_paperPositive_H1supBoundDI_local
#print axioms intervalDomain_boundedBefore_of_paperPositive_H1supBoundDI_local_before
#print axioms H1EnergyIdentity_of_classicalSolution_and_H1UxxL1ContBefore

end ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
