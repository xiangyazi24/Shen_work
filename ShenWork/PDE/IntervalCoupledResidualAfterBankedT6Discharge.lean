import ShenWork.PDE.IntervalCoupledRegularityBanked
import ShenWork.Paper2.IntervalMildPicardThreshold
import ShenWork.Paper2.IntervalDomainPdeUProducer

open scoped Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalDomainPdeUProducer
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDuhamelClosedC2

/-- The residual after Picard positivity and the initial trace have been wired
into `CoupledDuhamelResidualAfterBankedT6`.  The T6 slice pack supplies spatial
closed-`C²`/Neumann data, but not the time derivative identity. -/
structure CoupledDuhamelBankedT6Frontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop where
  pde_u : ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv D.u t x =
      intervalDomain.laplacian (D.u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
            (coupledChemicalConcentration p D.u t) x
        + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)
  classicalResidual : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u

/-- Picard strict positivity and the banked initial-approach theorem discharge
`u_pos` and `initialTrace`; only the named frontier remains. -/
theorem coupledDuhamelResidualAfterBankedT6_of_gradientMild_frontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    (F : CoupledDuhamelBankedT6Frontier p D) :
    CoupledDuhamelResidualAfterBankedT6 p D.T u₀ D.u := by
  refine
    { u_pos := ?_
      pde_u := F.pde_u
      classicalResidual := F.classicalResidual
      initialTrace := ?_ }
  · intro t x ht htT
    exact D.hpos t ht (le_of_lt htT) x
  · exact mildSolution_initialTrace p D
      (gradientMildSolutionData_initialApproach p hu₀_cont D)

/-- In the `χ₀ = 0` regime, the existing spectral producer closes `pde_u`; the
remaining coupled data is exactly the classical residual after T6. -/
structure CoupledDuhamelBankedT6ChiZeroFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop where
  hpde : HasSpectralPdeAgreement p D.T D.u
  classicalResidual : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u

theorem coupledDuhamelBankedT6Frontier_of_chiZero_spectral
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) (hχ0 : p.χ₀ = 0)
    (F : CoupledDuhamelBankedT6ChiZeroFrontier p D) :
    CoupledDuhamelBankedT6Frontier p D := by
  refine
    { pde_u := ?_
      classicalResidual := F.classicalResidual }
  intro t x ht htT hx
  have h := mildSolution_pde_u_of_spectral p hχ0 D F.hpde t x ht htT hx
  simpa [coupledChemicalConcentration, mildChemicalConcentration] using h

theorem coupledDuhamelResidualAfterBankedT6_of_gradientMild_chiZero_spectral
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    (hχ0 : p.χ₀ = 0) (F : CoupledDuhamelBankedT6ChiZeroFrontier p D) :
    CoupledDuhamelResidualAfterBankedT6 p D.T u₀ D.u :=
  coupledDuhamelResidualAfterBankedT6_of_gradientMild_frontier p hu₀_cont D
    (coupledDuhamelBankedT6Frontier_of_chiZero_spectral p D hχ0 F)

theorem regularityBootstrap_of_gradientMild_bankedT6_chiZero_spectral
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    (hχ0 : p.χ₀ = 0)
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p D.u))
    (hagree : CoupledDuhamelT6SliceAgreement p D.T D.u)
    (F : CoupledDuhamelBankedT6ChiZeroFrontier p D) :
    RegularityBootstrap p D.T u₀ D.u :=
  regularityBootstrap_of_coupledDuhamel_bankedT6_source_and_residual p hsrc
    hagree
    (coupledDuhamelResidualAfterBankedT6_of_gradientMild_chiZero_spectral
      p hu₀_cont D hχ0 F)

#print axioms coupledDuhamelResidualAfterBankedT6_of_gradientMild_frontier
#print axioms coupledDuhamelBankedT6Frontier_of_chiZero_spectral
#print axioms coupledDuhamelResidualAfterBankedT6_of_gradientMild_chiZero_spectral
#print axioms regularityBootstrap_of_gradientMild_bankedT6_chiZero_spectral

end ShenWork.IntervalCoupledRegularityBootstrap
