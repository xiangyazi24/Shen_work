import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

/-!
# H¹ derivative-integrability producer

This file closes the scalar FTC integrability input for `H1energy` from an
explicit integrable right-hand side of the H¹ identity. It deliberately does
not try to infer interval-integrability from a pointwise derivative identity
alone.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1AverageWiring
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability

/-- The scalar right-hand side value appearing in the packaged H¹ identity. -/
def H1IdentityRHSValue (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) (τ : ℝ) : ℝ :=
  -(lapL2sq u τ) + (-p.χ₀) * taxisX τ + (-p.χ₀) * uvxx τ + reactX τ

/-- Transfer interval-integrability from an explicitly integrable RHS to
`deriv (H1energy u)` when the two agree on the unordered integration interval.
-/
theorem H1_deriv_intervalIntegrable_of_eq_on_uIoc
    {u : ℝ → intervalDomainPoint → ℝ} {D : ℝ → ℝ} {a b : ℝ}
    (hD : IntervalIntegrable D volume a b)
    (heq : ∀ r, r ∈ Set.uIoc a b → deriv (H1energy u) r = D r) :
    IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b := by
  exact hD.congr (fun r hr => (heq r hr).symm)

/-- Ordered-interval version of
`H1_deriv_intervalIntegrable_of_eq_on_uIoc`. -/
theorem H1_deriv_intervalIntegrable_of_eq_on_Ioc
    {u : ℝ → intervalDomainPoint → ℝ} {D : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hD : IntervalIntegrable D volume a b)
    (heq : ∀ r, r ∈ Set.Ioc a b → deriv (H1energy u) r = D r) :
    IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b := by
  refine H1_deriv_intervalIntegrable_of_eq_on_uIoc (u := u) (D := D) hD ?_
  intro r hr
  exact heq r (by simpa [Set.uIoc_of_le hab] using hr)

/-- If the explicit H¹ identity RHS is interval-integrable on every
pre-horizon window, then the scalar derivative of `H1energy` is
interval-integrable on every such window. -/
theorem H1_derivInt_of_identityRHS_intervalIntegrable
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hRHSInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable
        (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b := by
  intro a b ha hab hbT
  refine H1_deriv_intervalIntegrable_of_eq_on_Ioc (u := u)
    (D := H1IdentityRHSValue p u taxisX uvxx reactX)
    hab (hRHSInt ha hab hbT) ?_
  intro r hr
  have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
  have hrT : r < T := lt_of_le_of_lt hr.2 hbT
  have hEnergy := hId r ⟨hr0, hrT⟩
  unfold H1EnergyIdentity at hEnergy
  simpa [H1IdentityRHSValue] using hEnergy.deriv

/-- Explicit pre-horizon H¹ identity RHS together with its interval
integrability on every closed subwindow before `T`. -/
structure H1IdentityRHSIntegrableBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) : Prop where
  identity : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ)
  rhs_intervalIntegrable : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b

/-- Extract the scalar derivative-integrability field from the explicit
identity/RHS-integrability package. -/
theorem H1_derivInt_of_identityRHSIntegrableBefore
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b :=
  H1_derivInt_of_identityRHS_intervalIntegrable
    hRHS.identity hRHS.rhs_intervalIntegrable

/-- Continuous explicit H¹ identity RHS on unordered closed windows is enough
for the RHS interval-integrability field. -/
theorem H1IdentityRHS_intervalIntegrable_of_continuousOn_uIcc
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hRHSCont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn
        (H1IdentityRHSValue p u taxisX uvxx reactX) (Set.uIcc a b)) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable
        (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b := by
  intro a b ha hab hbT
  exact (hRHSCont ha hab hbT).intervalIntegrable

/-- Ordered-closed-window continuity is also enough for the explicit RHS
interval-integrability field. -/
theorem H1IdentityRHS_intervalIntegrable_of_continuousOn_Icc
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hRHSCont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn
        (H1IdentityRHSValue p u taxisX uvxx reactX) (Set.Icc a b)) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable
        (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b := by
  intro a b ha hab hbT
  exact (hRHSCont ha hab hbT).intervalIntegrable_of_Icc hab

/-- Package scalar continuity with explicit RHS integrability into the H¹
scalar regularity record. -/
theorem H1ScalarRegularityBefore_of_hcont_and_identityRHSIntegrable
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hcont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (H1energy u) (Set.Icc a b))
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_hcont_and_hderivInt hcont
    (H1_derivInt_of_identityRHSIntegrableBefore hRHS)

/-- H¹ scalar regularity from the `u_xx` L¹-continuity bridge plus explicit
RHS integrability. -/
theorem H1ScalarRegularityBefore_of_uxxL1Cont_and_identityRHSIntegrable
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_uxxL1Cont_and_hderivInt
    hsol hUxxL1 hcont0
    (H1_derivInt_of_identityRHSIntegrableBefore hRHS)

/-- H¹ scalar regularity from a classical solution via the concrete
chemotaxis-divergence representative, plus explicit RHS integrability. -/
theorem H1ScalarRegularityBefore_of_classicalChemRep_identityRHSIntegrable
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_uxxL1Cont_and_identityRHSIntegrable
    hsol
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    hcont0 hRHS

/-- Direct scalar-DI producer from `u_xx` L¹-continuity, explicit RHS
integrability, and the pointwise RHS-bound package. -/
theorem H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont_integrableRHS
    {p : CM2Params} {T A B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX)
    (hBound : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B :=
  H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont
    hsol hUxxL1 hcont0
    (H1_derivInt_of_identityRHSIntegrableBefore hRHS)
    hBound

/-- Direct scalar-DI producer from a classical solution via the concrete
chemotaxis-divergence representative, explicit RHS integrability, and the
pointwise RHS-bound package. -/
theorem H1ScalarDIOnBefore_of_identityRHSBound_classicalChemRep_integrableRHS
    {p : CM2Params} {T A B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX)
    (hBound : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B :=
  H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont_integrableRHS
    hsol
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    hcont0 hRHS hBound

/-- Paper-positive bounded-before route using the compact identity/RHS-bound
package directly, with scalar regularity produced from `u_xx` L¹-continuity
and explicit RHS integrability. The local H¹ start is required only while
`τ < T`. -/
theorem intervalDomain_boundedBefore_of_H1identityRHS_integrableRHS_local_before
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
    {A B Ylocal : ℝ}
    (hBound : H1IdentityRHSBoundBefore params u T A B)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hDI : H1ScalarDIOnBefore u T A B :=
    H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont_integrableRHS
      hsol hUxxL1 hcont0 hRHS hBound
  exact intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier hDI hlocal

/-- Paper-positive bounded-before route using the concrete classical
chemotaxis-divergence representative to produce the `u_xx` L¹-continuity input.
The local H¹ start is required only while `τ < T`. -/
theorem boundedBefore_of_H1identityRHS_classicalChemRep_local_before
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
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {A B Ylocal : ℝ}
    (hBound : H1IdentityRHSBoundBefore params u T A B)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1identityRHS_integrableRHS_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    hcont0 hRHS hBound hlocal

/-- Paper-positive bounded-before route using sup-bound DI data, with the
scalar regularity field produced from `u_xx` L¹-continuity and explicit RHS
integrability. The local H¹ start is required only while `τ < T`. -/
theorem intervalDomain_boundedBefore_of_H1supBoundDI_integrableRHS_local_before
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
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  let A : ℝ := 2 * (-params.χ₀) ^ 2 * V₁ ^ 2 + 2 * L
  let B : ℝ := (-params.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2
  have hBound : H1IdentityRHSBoundBefore params u T A B := by
    simpa [A, B] using H1IdentityRHSBoundBefore_of_supBoundDIData hdata
  exact intervalDomain_boundedBefore_of_H1identityRHS_integrableRHS_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1 hcont0 hRHS
    hBound hlocal

/-- Sup-bound DI variant using the concrete classical chemotaxis-divergence
representative to produce the `u_xx` L¹-continuity input. -/
theorem boundedBefore_of_H1supBoundDI_classicalChemRep_local_before
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
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1supBoundDI_integrableRHS_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    hcont0 hRHS hdata hlocal

#print axioms H1_deriv_intervalIntegrable_of_eq_on_uIoc
#print axioms H1_deriv_intervalIntegrable_of_eq_on_Ioc
#print axioms H1_derivInt_of_identityRHS_intervalIntegrable
#print axioms H1_derivInt_of_identityRHSIntegrableBefore
#print axioms H1IdentityRHS_intervalIntegrable_of_continuousOn_uIcc
#print axioms H1IdentityRHS_intervalIntegrable_of_continuousOn_Icc
#print axioms H1ScalarRegularityBefore_of_hcont_and_identityRHSIntegrable
#print axioms H1ScalarRegularityBefore_of_uxxL1Cont_and_identityRHSIntegrable
#print axioms H1ScalarRegularityBefore_of_classicalChemRep_identityRHSIntegrable
#print axioms H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont_integrableRHS
#print axioms H1ScalarDIOnBefore_of_identityRHSBound_classicalChemRep_integrableRHS
#print axioms intervalDomain_boundedBefore_of_H1identityRHS_integrableRHS_local_before
#print axioms boundedBefore_of_H1identityRHS_classicalChemRep_local_before
#print axioms intervalDomain_boundedBefore_of_H1supBoundDI_integrableRHS_local_before
#print axioms boundedBefore_of_H1supBoundDI_classicalChemRep_local_before

end ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
