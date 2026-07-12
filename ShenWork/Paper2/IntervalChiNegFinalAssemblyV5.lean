import ShenWork.Paper2.IntervalChiNegFinalAssemblyV4
import ShenWork.Paper2.IntervalBFormCron2AllInputDataWiring
import ShenWork.Paper2.IntervalBFormCron2TruncatedCoefficientWeakTest
import ShenWork.Paper2.Batch2RemainingSubfields
import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPosProducer

/-!
  V5 final close for the chi-negative interval branch.

  The only explicit frontier carried by the final theorem is the spectral
  classical bootstrap.  The remaining regular negative-part/Jensen atoms are
  supplied as an implicit instance and are immediately assembled into the V4
  `UniformTruncatedJensenAssemblyInputs`.
-/

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData UniformConjugateMildExistenceCore)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (TruncatedNegativePartCoefficientWeakTestData
   TruncatedPicardNegativePartEnergyEstimateA2Data
   TruncatedPicardNegativePartEnergyA3Data
   TruncatedPicardNegativePartEnergyCoreRegularData
   UniformTruncatedConjugateMildExistenceCore
   truncatedPicardEnergyCoreRegularData_of_atomData
   truncatedConjugatePicardLimit_initialTrace_of_truncated_data
   truncatedConjugatePicardLimit
   uniformTruncatedConjugateMildExistenceCore_of_uniformCore)
open ShenWork.Paper2.IntervalChiNegFinalAssemblyV4
  (JensenBypassStrictPosDataFor UniformTruncatedJensenAssemblyInputs
   UniformTruncatedJensenEnergyData
   coupledFluxClassicalLocalExistenceResidual_v4)
open ShenWork.Paper2.ChiNegResidual
  (CoupledFluxClassicalLocalExistenceResidual
   theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegFinalAssemblyV5

/-- A1/A2/A3 atom package at one uniform core. -/
structure V5EnergyAtoms
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) where
  E' : ℝ → ℝ
  A1 : ∀ t, 0 < t → t < C.T →
    TruncatedNegativePartCoefficientWeakTestData p
      (uniformTruncatedConjugateMildExistenceCore_of_uniformCore C).toData t
  A2 : TruncatedPicardNegativePartEnergyEstimateA2Data
    p (u₀ := u₀) C.T E'
  A3 : TruncatedPicardNegativePartEnergyA3Data
    p (u₀ := u₀) C.T E'

/-- The non-spectral V5 atom supply, indexed uniformly over the chosen core.
`energyAtoms` is exactly the A1/A2/A3 package: A1 is coefficient weak-test data,
A2 is the regular energy estimate package, and A3 is the Picard side-data plus
energy continuity/chain rule package. -/
class Paper2ChiNegV5AtomSupply (p : CM2Params) where
  energyAtoms :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        V5EnergyAtoms p C
  jensenStrictPos :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        JensenBypassStrictPosDataFor C.T
          (truncatedConjugatePicardLimit p u₀ C.T)
  fullAgreement :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        truncatedConjugatePicardLimit p u₀ C.T =
          ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ C.T

def truncatedPicardEnergyCoreRegularData_v5
    {p : CM2Params} [Paper2ChiNegV5AtomSupply p]
    {M : ℝ} (hM : 0 < M) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    (C : UniformConjugateMildExistenceCore p u₀) :
    TruncatedPicardNegativePartEnergyCoreRegularData
      p (u₀ := u₀) C.T := by
  let HA := Paper2ChiNegV5AtomSupply.energyAtoms
      (p := p) hM hu₀ hbound C
  let DT := (uniformTruncatedConjugateMildExistenceCore_of_uniformCore C).toData
  simpa [DT, UniformTruncatedConjugateMildExistenceCore.toData] using
    truncatedPicardEnergyCoreRegularData_of_atomData
      DT HA.A1 HA.A2 HA.A3

def uniformTruncatedJensenEnergyData_v5
    (p : CM2Params) [Paper2ChiNegV5AtomSupply p] :
    UniformTruncatedJensenEnergyData p := by
  intro _M hM _u₀ hu₀ hbound C
  exact truncatedPicardEnergyCoreRegularData_v5 hM hu₀ hbound C

def uniformTruncatedJensenAssemblyInputs_v5
    (p : CM2Params) [Paper2ChiNegV5AtomSupply p] :
    UniformTruncatedJensenAssemblyInputs p where
  energy := uniformTruncatedJensenEnergyData_v5 p
  jensenStrictPos := by
    intro _M hM _u₀ hu₀ hbound C
    exact Paper2ChiNegV5AtomSupply.jensenStrictPos
      (p := p) hM hu₀ hbound C
  initialTrace := by
    intro _M _hM _u₀ _hu₀ _hbound C
    let HT := uniformTruncatedConjugateMildExistenceCore_of_uniformCore C
    simpa [UniformTruncatedConjugateMildExistenceCore.toData] using
      truncatedConjugatePicardLimit_initialTrace_of_truncated_data
        p C.hbase_cont HT.toData
  fullAgreement := by
    intro _M hM _u₀ hu₀ hbound C
    exact Paper2ChiNegV5AtomSupply.fullAgreement
      (p := p) hM hu₀ hbound C

theorem coupledFluxClassicalLocalExistenceResidual_v5
    (p : CM2Params) [Paper2ChiNegV5AtomSupply p]
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀),
      BFormMildSpectralBootstrapData p S) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  coupledFluxClassicalLocalExistenceResidual_v4
    p hα hγ (uniformTruncatedJensenAssemblyInputs_v5 p) HSpectral

theorem paper2_chiNeg_v5
    (p : CM2Params) [Paper2ChiNegV5AtomSupply p]
    (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀),
      BFormMildSpectralBootstrapData p S) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ
    (coupledFluxClassicalLocalExistenceResidual_v5 p hα hγ HSpectral)

#print axioms truncatedPicardEnergyCoreRegularData_v5
#print axioms uniformTruncatedJensenAssemblyInputs_v5
#print axioms coupledFluxClassicalLocalExistenceResidual_v5
#print axioms paper2_chiNeg_v5

end ShenWork.Paper2.IntervalChiNegFinalAssemblyV5
