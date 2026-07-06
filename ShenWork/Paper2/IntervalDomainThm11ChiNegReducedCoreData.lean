import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual
import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge

/-!
  # χ₀<0 coupled-flux residual with reduced-core regularization data

  `CoupledFluxResolverAnalyticData` asks each Duhamel fixed point to produce
  `RegularityBootstrap`.  Existing infrastructure already proves
  `CoupledDuhamelReducedClassicalCore → RegularityBootstrap`, so the genuinely
  smaller regularization field is a reduced-core producer.
-/

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalCoupledRegularityBootstrap
  (CoupledDuhamelReducedClassicalCore
   regularityBootstrap_of_coupledDuhamel_reducedClassicalCore)
open ShenWork.PDE

noncomputable section

namespace ShenWork.Paper2.ChiNegResidual

/-- Resolver analytic data with the regularization field reduced to the
already-minimized coupled-Duhamel classical core. -/
def CoupledFluxResolverReducedCoreData (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M →
    ∃ Mball : ℝ, 0 < Mball ∧ M ≤ Mball ∧
      ∀ L : ℝ, 0 < L →
        ∃ T A K : ℝ, 0 < T ∧ 0 < A ∧ 0 ≤ K ∧ A * T < 1 ∧
          |p.χ₀| * K + L ≤ A ∧
            ∀ {u0 : intervalDomain.Point → ℝ},
              PositiveInitialDatum intervalDomain u0 →
              (∀ x, |u0 x| ≤ M) →
                IntervalCoupledResolverBallEstimates p
                  (intervalNeumannResolverR p) u0 T Mball K ∧
                ∀ u : ℝ → intervalDomain.Point → ℝ,
                  intervalTrajectoryBoundedOn T Mball u →
                  (∀ t x, 0 ≤ t → t ≤ T →
                    u t x = intervalCoupledDuhamelOperator p
                      (intervalNeumannResolverR p) u0 u t x) →
                    CoupledDuhamelReducedClassicalCore p T u0 u

/-- Reduced-core data recover the existing resolver analytic residual by the
banked reduced-core-to-regularity bridge. -/
theorem coupledFluxResolverAnalyticData_of_reducedCoreData
    (p : CM2Params)
    (H : CoupledFluxResolverReducedCoreData p) :
    CoupledFluxResolverAnalyticData p := by
  intro M hM
  obtain ⟨Mball, hMball, hM_le, Hlocal⟩ := H M hM
  refine ⟨Mball, hMball, hM_le, ?_⟩
  intro L hL
  obtain ⟨T, A, K, hT, hA, hK, hAT, hA_bound, Hdatum⟩ := Hlocal L hL
  refine ⟨T, A, K, hT, hA, hK, hAT, hA_bound, ?_⟩
  intro u0 hu0 hbound
  obtain ⟨hest, hcore⟩ := Hdatum hu0 hbound
  refine ⟨hest, ?_⟩
  intro u _v hu_bound hfp _hv
  exact regularityBootstrap_of_coupledDuhamel_reducedClassicalCore p
    (hcore u hu_bound hfp)

/-- Reduced-core resolver data close the quantitative coupled-flux local
existence residual. -/
theorem coupledFluxClassicalLocalExistenceResidual_of_reducedCoreData
    (p : CM2Params) (hα : 1 ≤ p.α)
    (H : CoupledFluxResolverReducedCoreData p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
    p hα (coupledFluxResolverAnalyticData_of_reducedCoreData p H)

/-- χ₀<0 Theorem 1.1 from the reduced-core resolver analytic data. -/
theorem theorem_1_1_intervalDomain_chiNeg_of_reducedCoreData
    (p : CM2Params) (hchi_neg : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : CoupledFluxResolverReducedCoreData p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hchi_neg ha hb hα hγ
    (coupledFluxClassicalLocalExistenceResidual_of_reducedCoreData p hα H)

section AxiomAudit

#print axioms coupledFluxResolverAnalyticData_of_reducedCoreData
#print axioms coupledFluxClassicalLocalExistenceResidual_of_reducedCoreData
#print axioms theorem_1_1_intervalDomain_chiNeg_of_reducedCoreData

end AxiomAudit

end ShenWork.Paper2.ChiNegResidual
