import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.Paper2.IntervalBFormJensenBarrierBypass
import ShenWork.Paper2.IntervalBFormTruncatedBridgeProducerData
import ShenWork.Paper2.IntervalBFormMildClassicalBootstrap
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

/-!
Option B assembly for the chi-negative interval branch.

The solution carried through the final assembly is the faithful truncated
Picard limit itself.  Energy gives nonnegativity, the truncated Duhamel map is
then the interval Duhamel map on that trajectory, Jensen gives strict
positivity, and the spectral bootstrap upgrades the packaged mild solution.
-/

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData UniformConjugateMildExistenceCore
   uniformConjugateMildExistenceCore_exists)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_of_mem)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (FullKernelJensenInequality ReactionDiscountedMildLower
   TruncatedNegativePartEnergyCoreRegularData
   UniformTruncatedConjugateMapCertificate
   UniformTruncatedConjugateMapCertificateData
   UniformTruncatedConjugateMildExistenceCore
   truncatedConjugateDuhamelMap
   truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg
   truncatedConjugatePicardLimit
   truncatedConjugatePicardLimit_initialTrace_of_truncated_data
   truncatedConjugatePicardLimit_nonneg_global
   truncatedConjugatePicardLimit_nonneg_of_truncated_regular_energyCore
   strict_pos_of_jensen_discounted_bypass
   uniformTruncatedConjugateMildExistenceCore_of_uniformCore)
open ShenWork.Paper2.ChiNegResidual
  (CoupledFluxClassicalLocalExistenceResidual
   theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegAssembly

/-- Positive-time Jensen data for the faithful truncated limit. -/
structure TruncatedJensenStrictPosDataFor
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  witness :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      ∃ D s σ : ℝ, ∃ f : ℝ → ℝ,
        0 < σ ∧
        s + σ = t ∧
        FullKernelJensenInequality f ∧
        intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x.1 ≤
          intervalFullSemigroupOperator σ
            (fun y => u s (unitClip y)) x.1 ∧
        Real.exp (-D * σ) *
            intervalFullSemigroupOperator σ
              (fun y => u s (unitClip y)) x.1 ≤
          u t x ∧
        0 < intervalFullSemigroupOperator σ f x.1

theorem strictPos_of_truncatedJensenStrictPosDataFor
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : TruncatedJensenStrictPosDataFor T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 < u t x := by
  intro t ht htT x
  rcases H.witness t ht htT x with
    ⟨D, s, σ, f, hσ, htime, hjensen, hseed, hmild, hSpos⟩
  have hJ := hjensen hσ (x := x.1)
  have hheat :
      (intervalFullSemigroupOperator σ f x.1) ^ 2 ≤
        intervalFullSemigroupOperator σ
          (fun y => u s (unitClip y)) x.1 :=
    hJ.trans hseed
  have hdiscount :
      Real.exp (-D * σ) *
          (intervalFullSemigroupOperator σ f x.1) ^ 2 ≤
        u t x :=
    (mul_le_mul_of_nonneg_left hheat (Real.exp_pos _).le).trans hmild
  exact lt_of_lt_of_le
    (mul_pos (Real.exp_pos _) (sq_pos_of_pos hSpos)) hdiscount

abbrev UniformTruncatedEnergyData (p : CM2Params) : Type :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      ∀ A : UniformTruncatedConjugateMapCertificate p C,
      TruncatedNegativePartEnergyCoreRegularData p
        (uniformTruncatedConjugateMildExistenceCore_of_uniformCore C A).toData

/-- The only non-spectral V6 inputs: energy and Jensen strict positivity. -/
structure UniformTruncatedAssemblyInputs (p : CM2Params) where
  mapCertificate : UniformTruncatedConjugateMapCertificateData p
  energy : UniformTruncatedEnergyData p
  jensenStrictPos :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        TruncatedJensenStrictPosDataFor C.T
          (truncatedConjugatePicardLimit p u₀ C.T)

/-- Once energy proves nonnegativity, the truncated mild equation is the
interval conjugate mild equation for the same truncated limit. -/
theorem intervalConjugateMildSolution_of_truncatedEnergy
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HT : UniformTruncatedConjugateMildExistenceCore p C)
    (Henergy :
      TruncatedNegativePartEnergyCoreRegularData p HT.toData) :
    IntervalConjugateMildSolution p C.T u₀
      (truncatedConjugatePicardLimit p u₀ C.T) := by
  let uT : ℝ → intervalDomainPoint → ℝ :=
    truncatedConjugatePicardLimit p u₀ C.T
  have hnonneg_window :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint, 0 ≤ uT t x := by
    intro t ht htT x
    simpa [uT, UniformTruncatedConjugateMildExistenceCore.toData]
      using truncatedConjugatePicardLimit_nonneg_of_truncated_regular_energyCore
        Henergy t ht
          (by
            simpa [UniformTruncatedConjugateMildExistenceCore.toData]
              using htT)
          x
  have hnonneg_global : ∀ t : ℝ, ∀ x : intervalDomainPoint, 0 ≤ uT t x := by
    intro t x
    exact truncatedConjugatePicardLimit_nonneg_global
      (DT := HT.toData)
      (by
        intro s hs hsT y
        exact hnonneg_window s hs
          (by
            simpa [UniformTruncatedConjugateMildExistenceCore.toData]
              using hsT)
          y)
      t x
  intro t ht htT x
  calc
    uT t x = truncatedConjugateDuhamelMap p u₀ uT t x := by
      simpa [uT, UniformTruncatedConjugateMildExistenceCore.toData]
        using (HT.solutionData).hmild t ht htT x
    _ = intervalConjugateDuhamelMap p u₀ uT t x :=
      truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg
        p u₀ hnonneg_global t x

def conjugateMildSolutionData_of_truncatedEnergyJensen
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {C : UniformConjugateMildExistenceCore p u₀}
    (HT : UniformTruncatedConjugateMildExistenceCore p C)
    (Henergy :
      TruncatedNegativePartEnergyCoreRegularData p HT.toData)
    (HJensen :
      TruncatedJensenStrictPosDataFor C.T
        (truncatedConjugatePicardLimit p u₀ C.T)) :
    ConjugateMildSolutionData p u₀ where
  T := C.T
  hT := C.hT
  M := C.R
  hM := C.hR
  u := truncatedConjugatePicardLimit p u₀ C.T
  hmild := intervalConjugateMildSolution_of_truncatedEnergy HT Henergy
  hbound := by
    intro t ht htT x
    simpa [UniformTruncatedConjugateMildExistenceCore.toData]
      using (HT.solutionData).hbound t ht htT x
  hnonneg := by
    intro t ht htT x
    simpa [UniformTruncatedConjugateMildExistenceCore.toData]
      using truncatedConjugatePicardLimit_nonneg_of_truncated_regular_energyCore
        Henergy t ht
          (by
            simpa [UniformTruncatedConjugateMildExistenceCore.toData]
              using htT)
          x
  hpos := strictPos_of_truncatedJensenStrictPosDataFor HJensen
  hcont := by
    simpa [UniformTruncatedConjugateMildExistenceCore.toData]
      using (HT.solutionData).hcont
  hmeas := by
    simpa [UniformTruncatedConjugateMildExistenceCore.toData]
      using (HT.solutionData).hmeas

theorem initialTrace_of_truncatedEnergyJensen
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {C : UniformConjugateMildExistenceCore p u₀}
    (HT : UniformTruncatedConjugateMildExistenceCore p C)
    (Henergy :
      TruncatedNegativePartEnergyCoreRegularData p HT.toData)
    (HJensen :
      TruncatedJensenStrictPosDataFor C.T
        (truncatedConjugatePicardLimit p u₀ C.T)) :
    InitialTrace intervalDomain u₀
      (conjugateMildSolutionData_of_truncatedEnergyJensen
        HT Henergy HJensen).u := by
  dsimp [conjugateMildSolutionData_of_truncatedEnergyJensen]
  exact truncatedConjugatePicardLimit_initialTrace_of_truncated_data
    p hu₀.admissible.2 HT.toData

theorem coupledFluxClassicalLocalExistenceResidual
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : UniformTruncatedAssemblyInputs p)
    (HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀),
      BFormMildSpectralBootstrapData p S) :
    CoupledFluxClassicalLocalExistenceResidual p := by
  intro M hM
  obtain ⟨T, hT, Huniform⟩ :=
    uniformConjugateMildExistenceCore_exists p hα hγ M hM
  refine ⟨T, hT, ?_⟩
  intro u₀ hu₀ hbound
  let u₀I : intervalDomainPoint → ℝ := u₀
  have hu₀I : PositiveInitialDatum intervalDomain u₀I := by
    simpa [u₀I] using hu₀
  have hboundI : ∀ x : intervalDomainPoint, |u₀I x| ≤ M := by
    intro x
    simpa [u₀I] using hbound x
  have hu₀_cont : Continuous u₀I := hu₀I.admissible.2
  obtain ⟨C, hCT⟩ := Huniform hu₀_cont hboundI
  let A := H.mapCertificate hM hu₀I hboundI C
  let HT := uniformTruncatedConjugateMildExistenceCore_of_uniformCore C A
  let Henergy := H.energy hM hu₀I hboundI C A
  let HJensen := H.jensenStrictPos hM hu₀I hboundI C
  let S : ConjugateMildSolutionData p u₀I :=
    conjugateMildSolutionData_of_truncatedEnergyJensen
      HT Henergy HJensen
  have hTrace : InitialTrace intervalDomain u₀I S.u := by
    simpa [S] using
      initialTrace_of_truncatedEnergyJensen
        hu₀I HT Henergy HJensen
  obtain ⟨u, v, hclass, htrace⟩ :=
    localClassicalSolution_of_conjugateMild_spectral
      S (HSpectral S) hTrace
  refine ⟨u, v, ?_, htrace⟩
  have hST : S.T = T := by
    dsimp [S, conjugateMildSolutionData_of_truncatedEnergyJensen]
    exact hCT
  simpa [hST] using hclass

theorem paper2_chiNeg_spectral
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : UniformTruncatedAssemblyInputs p)
    (HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀),
      BFormMildSpectralBootstrapData p S) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ
    (coupledFluxClassicalLocalExistenceResidual p hα hγ H HSpectral)

#print axioms intervalConjugateMildSolution_of_truncatedEnergy
#print axioms conjugateMildSolutionData_of_truncatedEnergyJensen
#print axioms coupledFluxClassicalLocalExistenceResidual
#print axioms paper2_chiNeg_spectral

end ShenWork.Paper2.IntervalChiNegAssembly
