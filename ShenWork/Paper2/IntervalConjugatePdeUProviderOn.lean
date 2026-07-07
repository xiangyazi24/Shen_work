/-
  Direct `hpde_u` provider for the conjugate/B-form Picard route with
  bank-shaped source and initial-continuity inputs.

  This composes the On/constant-extension B-form global cosine producer with
  the window-local general-chi `hpde_u` producer.  It removes the two old
  direct-provider mismatches: global source time-C1 and global continuity of
  the zero extension of the initial datum.
-/
import ShenWork.Paper2.IntervalSourceBridgeOpenRepresentativeOn
import ShenWork.Paper2.IntervalDomainPdeUGeneralChiProviderOn

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace ShenWork.IntervalDomainPdeUGeneralChi

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs LogisticCosineFourierData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.Paper2.IntervalSourceBridgeOpen
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs coupledChemDivSourceLift)
open ShenWork.Paper2.BankChemSliceFix (ChemDivCosineFourierDataIoo)

/-- Direct conjugate/B-form `hpde_u` from bank-shaped source data.

Compared with
`hpde_u_of_conjugatePicardLimit_open_sourceBridgeRepresentativeSubtypeLogisticData`,
this theorem consumes `DuhamelSourceTimeC1On ... 0 T` and `Continuous u₀`,
matching the B-form bank surface. -/
theorem hpde_u_of_conjugatePicardLimit_open_sourceBridgeRepresentativeSubtypeLogisticDataOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (conjugatePicardLimit p u₀ T))
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB_on : DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T)
    (hB_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p ((conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p ((conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hchem_cont : ∀ s, 0 < s → s < T →
      Continuous (chemFluxLifted p ((conjugatePicardLimit p u₀ T) s)))
    (hlog_cont : ∀ s, 0 < s → s < T →
      Continuous (intervalLogisticSource p ((conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s, 0 < s → s < T →
      ∃ Mlog : ℝ, ∀ n,
        |cosineCoeffs
          (logisticLifted p ((conjugatePicardLimit p u₀ T) s)) n| ≤ Mlog)
    (hchem_bound : ∀ s, 0 < s → s < T →
      ∃ Mchem : ℝ, ∀ n,
        |coupledChemDivSourceCoeffs p
          (conjugatePicardLimit p u₀ T) s n| ≤ Mchem)
    (hQderiv : ∀ s, 0 < s → s < T → ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (chemFluxLifted p ((conjugatePicardLimit p u₀ T) s))
        (coupledChemDivSourceLift p (conjugatePicardLimit p u₀ T) s y)
        (Set.Ioi y) y)
    (hdiv_rep : ∀ s, 0 < s → s < T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn
          (coupledChemDivSourceLift p (conjugatePicardLimit p u₀ T) s)
          Gdiv (Set.Ioo (0 : ℝ) 1))
    (hlogData : ∀ t, 0 < t → t < T →
      LogisticCosineFourierData p (conjugatePicardLimit p u₀ T) t)
    (hchemData : ∀ t, 0 < t → t < T →
      ChemDivCosineFourierDataIoo p
        ((conjugatePicardLimit p u₀ T) t)
        (coupledChemicalConcentration p (conjugatePicardLimit p u₀ T) t)) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ T) t x =
        intervalDomain.laplacian ((conjugatePicardLimit p u₀ T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ T) t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration p
                (conjugatePicardLimit p u₀ T) t) x
          + (conjugatePicardLimit p u₀ T) t x *
              (p.a - p.b * ((conjugatePicardLimit p u₀ T) t x) ^ p.α) := by
  let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardLimit p u₀ T
  have hB_global : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p u) t n *
            ShenWork.CosineSpectrum.cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
    simpa [u] using
      conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeSubtypeLogisticDataOn
        (p := p) (u₀ := u₀) (T := T) (M₀ := M₀)
        hfix hu₀_cont hu₀_bound hsrcB_on hB_int hlog_int
        hchem_cont hlog_cont hlog_bound hchem_bound hQderiv hdiv_rep
  have hsource_split : ∀ σ, 0 < σ → σ < T → ∀ n,
      bFormSourceCoeffs p u σ n =
        coupledLogisticSourceCoeffs p u σ n
          - p.χ₀ * coupledChemDivSourceCoeffs p u σ n := by
    intro σ _hσ _hσT n
    rfl
  simpa [u] using
    hpde_u_of_bForm_global_generalChiOn
      (p := p) (T := T) (u := u)
      (cosineCoeffs (intervalDomainLift u₀))
      (bFormSourceCoeffs p u)
      M₀ hu₀_bound hsrcB_on hB_global hsource_split hlogData hchemData

#print axioms hpde_u_of_conjugatePicardLimit_open_sourceBridgeRepresentativeSubtypeLogisticDataOn

end ShenWork.IntervalDomainPdeUGeneralChi
