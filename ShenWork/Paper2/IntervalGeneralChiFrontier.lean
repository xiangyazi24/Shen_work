import ShenWork.PDE.IntervalCoupledResidualAfterBankedT6Discharge
import ShenWork.Wiener.EWA.SourcePdeU
import ShenWork.PDE.IntervalFullSemigroupNeumann
import ShenWork.Paper2.Statements

open scoped Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildPicard
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.EWA
open ShenWork.Paper2

/-- General-`χ₀` banked-T6 frontier from the source-form spectral identities.

This closes the `pde_u` field without assuming `χ₀ = 0`: the time series,
laplacian series, chem-div inversion, logistic inversion, and the three
summability facts are exactly the inputs consumed by
`EWA.fullSourceCoeff_pde_u`. -/
theorem coupledDuhamelBankedT6Frontier_of_fullSourceCoeff_pde
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) (u₀cos : ℕ → ℝ)
    (htime : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      intervalDomain.timeDeriv D.u t x
        = ∑' n, fullSourceCoeffDot p D.u u₀cos t n * cosineMode n x.1)
    (hlap : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      intervalDomain.laplacian (D.u t) x
        = ∑' n, (-(unitIntervalCosineEigenvalue n))
            * fullSourceCoeff p D.u u₀cos t n * cosineMode n x.1)
    (hchemInv : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledChemDivSourceCoeffs p D.u t n * cosineMode n x.1)
        = intervalDomainChemotaxisDiv p (D.u t)
            (coupledChemicalConcentration p D.u t) x)
    (hlogInv : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledLogisticSourceCoeffs p D.u t n * cosineMode n x.1)
        = D.u t x * (p.a - p.b * (D.u t x) ^ p.α))
    (hsum_lap : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n => unitIntervalCosineEigenvalue n
        * fullSourceCoeff p D.u u₀cos t n * cosineMode n x.1))
    (hsum_chem : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledChemDivSourceCoeffs p D.u t n * cosineMode n x.1))
    (hsum_log : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledLogisticSourceCoeffs p D.u t n * cosineMode n x.1))
    (R : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u) :
    CoupledDuhamelBankedT6Frontier p D := by
  refine
    { pde_u := ?_
      classicalResidual := R }
  intro t x ht htT hx
  have hxIoo : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
  have htIoo : t ∈ Set.Ioo (0 : ℝ) D.T := ⟨ht, htT⟩
  exact fullSourceCoeff_pde_u p D.u u₀cos hxIoo
    (htime t htIoo x hxIoo) (hlap t htIoo x hxIoo)
    (hchemInv t htIoo x hxIoo) (hlogInv t htIoo x hxIoo)
    (hsum_lap t htIoo x hxIoo) (hsum_chem t htIoo x hxIoo)
    (hsum_log t htIoo x hxIoo)

/-- General-`χ₀` regularity bootstrap once the banked source/T6 slice agreement
and source-form spectral `pde_u` identities are available. -/
theorem regularityBootstrap_of_gradientMild_bankedT6_fullSourceCoeff
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p D.u))
    (hagree : CoupledDuhamelT6SliceAgreement p D.T D.u)
    (u₀cos : ℕ → ℝ)
    (htime : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      intervalDomain.timeDeriv D.u t x
        = ∑' n, fullSourceCoeffDot p D.u u₀cos t n * cosineMode n x.1)
    (hlap : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      intervalDomain.laplacian (D.u t) x
        = ∑' n, (-(unitIntervalCosineEigenvalue n))
            * fullSourceCoeff p D.u u₀cos t n * cosineMode n x.1)
    (hchemInv : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledChemDivSourceCoeffs p D.u t n * cosineMode n x.1)
        = intervalDomainChemotaxisDiv p (D.u t)
            (coupledChemicalConcentration p D.u t) x)
    (hlogInv : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledLogisticSourceCoeffs p D.u t n * cosineMode n x.1)
        = D.u t x * (p.a - p.b * (D.u t x) ^ p.α))
    (hsum_lap : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n => unitIntervalCosineEigenvalue n
        * fullSourceCoeff p D.u u₀cos t n * cosineMode n x.1))
    (hsum_chem : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledChemDivSourceCoeffs p D.u t n * cosineMode n x.1))
    (hsum_log : ∀ t ∈ Set.Ioo (0 : ℝ) D.T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledLogisticSourceCoeffs p D.u t n * cosineMode n x.1))
    (R : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u) :
    RegularityBootstrap p D.T u₀ D.u :=
  regularityBootstrap_of_coupledDuhamel_bankedT6_source_and_residual p hsrc hagree
    (coupledDuhamelResidualAfterBankedT6_of_gradientMild_frontier p hu₀_cont D
      (coupledDuhamelBankedT6Frontier_of_fullSourceCoeff_pde p D u₀cos
        htime hlap hchemInv hlogInv hsum_lap hsum_chem hsum_log R))

/-- General-`χ₀` local existence from the banked-T6 frontier plus the
`intervalDuhamelOperator` fixed-point identity expected by the existing local
existence bridge. -/
theorem localExistence_of_gradientMild_bankedT6_frontier_and_fp
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hu₀_cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u₀ D.u t x)
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p D.u))
    (hagree : CoupledDuhamelT6SliceAgreement p D.T D.u)
    (F : CoupledDuhamelBankedT6Frontier p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  have hres : CoupledDuhamelResidualAfterBankedT6 p D.T u₀ D.u :=
    coupledDuhamelResidualAfterBankedT6_of_gradientMild_frontier p hu₀_cont D F
  have hreg : RegularityBootstrap p D.T u₀ D.u :=
    regularityBootstrap_of_coupledDuhamel_bankedT6_source_and_residual p
      hsrc hagree hres
  exact localExistence_of_fp_and_regularity p u₀ hu₀ D.hT hfp hreg

end ShenWork.IntervalCoupledRegularityBootstrap

namespace ShenWork.IntervalGeneralChiFrontier

open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalDomain (intervalDomainPoint)

/-- Endpoint obstruction for the proposed gradient-to-Neumann-source bridge.

For the current code's gradient mild term, the left side is always the spatial
derivative of the full Neumann semigroup.  Hence at either endpoint it is zero.
Any equality with a Neumann source profile would therefore force that source
profile to vanish at the endpoint.  This is not a valid generic consequence for
`chemDiv = ∂x Q`, and is the precise endpoint mismatch in the current route. -/
theorem gradient_source_bridge_forces_left_endpoint_zero
    (t : ℝ) (flux source : ℝ → ℝ)
    (hbridge : deriv (fun z => intervalFullSemigroupOperator t flux z) 0
      = intervalFullSemigroupOperator t source 0) :
    intervalFullSemigroupOperator t source 0 = 0 := by
  rw [← hbridge]
  exact ShenWork.intervalFullSemigroupOperator_deriv_at_zero_eq_zero t flux

/-- Right-endpoint version of
`gradient_source_bridge_forces_left_endpoint_zero`. -/
theorem gradient_source_bridge_forces_right_endpoint_zero
    (t : ℝ) (flux source : ℝ → ℝ)
    (hbridge : deriv (fun z => intervalFullSemigroupOperator t flux z) 1
      = intervalFullSemigroupOperator t source 1) :
    intervalFullSemigroupOperator t source 1 = 0 := by
  rw [← hbridge]
  exact ShenWork.intervalFullSemigroupOperator_deriv_at_one_eq_zero t flux

end ShenWork.IntervalGeneralChiFrontier

namespace ShenWork.IntervalCoupledRegularityBootstrap

#print axioms coupledDuhamelBankedT6Frontier_of_fullSourceCoeff_pde
#print axioms regularityBootstrap_of_gradientMild_bankedT6_fullSourceCoeff
#print axioms localExistence_of_gradientMild_bankedT6_frontier_and_fp

end ShenWork.IntervalCoupledRegularityBootstrap

namespace ShenWork.IntervalGeneralChiFrontier

#print axioms gradient_source_bridge_forces_left_endpoint_zero
#print axioms gradient_source_bridge_forces_right_endpoint_zero

end ShenWork.IntervalGeneralChiFrontier
