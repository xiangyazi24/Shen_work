import ShenWork.Paper2.IntervalBFormJensenBarrierBypass
import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.Paper2.IntervalBFormMildClassicalBootstrap
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

/-!
  V4 direct assembly for the chi-negative interval branch.

  The mild package is built from the uniform floor-free core through the
  faithful truncated Picard core.  Nonnegativity comes from Stampacchia energy,
  strict positivity from the Jensen positive-time bypass, and the resulting
  `ConjugateMildSolutionData` is fed directly to the spectral bootstrap.
-/

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData UniformConjugateMildExistenceCore
   conjugatePicardLimit uniformConjugateMildExistenceCore_exists)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_of_mem)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (FullKernelJensenInequality ReactionDiscountedMildLower
   TruncatedPicardNegativePartEnergyCoreRegularData
   UniformTruncatedConjugateMildExistenceCore
   conjugateMildSolutionData_of_uniformTruncatedCore
   strict_pos_of_jensen_discounted_bypass
   truncatedConjugatePicardLimit
   truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore
   uniformTruncatedConjugateMildExistenceCore_of_uniformCore)
open ShenWork.Paper2.ChiNegResidual
  (CoupledFluxClassicalLocalExistenceResidual
   theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegFinalAssemblyV4

/-- Positive-time Jensen data for one trajectory.  The real-line trajectory is
the unit-clipped lift of the interval trajectory. -/
structure JensenBypassStrictPosDataFor
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  witness :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      ∃ D s σ : ℝ, ∃ f : ℝ → ℝ,
        0 < σ ∧
        s + σ = t ∧
        ReactionDiscountedMildLower D
          (fun r y => u r (unitClip y)) ∧
        FullKernelJensenInequality f ∧
        intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x.1 ≤
          intervalFullSemigroupOperator σ
            (fun y => u s (unitClip y)) x.1 ∧
        0 < intervalFullSemigroupOperator σ f x.1

theorem strictPos_of_jensenBypassStrictPosDataFor
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : JensenBypassStrictPosDataFor T u) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 < u t x := by
  intro t ht htT x
  rcases H.witness t ht htT x with
    ⟨D, s, σ, f, hσ, htime, hmild, hjensen, hseed, hSpos⟩
  have hreal :
      0 < (fun r y => u r (unitClip y)) (s + σ) x.1 :=
    strict_pos_of_jensen_discounted_bypass
      (D := D) (s := s) (σ := σ) (x := x.1)
      (u := fun r y => u r (unitClip y)) (f := f)
      hσ hmild hjensen hseed hSpos
  simpa [htime, unitClip_of_mem x.2] using hreal

abbrev UniformTruncatedJensenEnergyData (p : CM2Params) : Type :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      TruncatedPicardNegativePartEnergyCoreRegularData p (u₀ := u₀) C.T

/-- Analytic inputs for V4.  The contraction/truncated core is not a field:
it is built unconditionally from the uniform core. -/
structure UniformTruncatedJensenAssemblyInputs (p : CM2Params) where
  energy : UniformTruncatedJensenEnergyData p
  jensenStrictPos :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        JensenBypassStrictPosDataFor C.T
          (truncatedConjugatePicardLimit p u₀ C.T)
  initialTrace :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        InitialTrace intervalDomain u₀
          (truncatedConjugatePicardLimit p u₀ C.T)
  fullAgreement :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        truncatedConjugatePicardLimit p u₀ C.T =
          conjugatePicardLimit p u₀ C.T

def truncatedCore_of_uniformCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (C : UniformConjugateMildExistenceCore p u₀) :
    UniformTruncatedConjugateMildExistenceCore p C :=
  uniformTruncatedConjugateMildExistenceCore_of_uniformCore C

def conjugateMildSolutionData_of_uniformTruncatedJensen
    {p : CM2Params} (H : UniformTruncatedJensenAssemblyInputs p)
    {M : ℝ} (hM : 0 < M) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    (C : UniformConjugateMildExistenceCore p u₀) :
    ConjugateMildSolutionData p u₀ := by
  let HT := truncatedCore_of_uniformCore C
  have hnonneg :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ C.T t x :=
    truncatedConjugatePicardLimit_nonneg_of_bare_regular_energyCore
      (H.energy hM hu₀ hbound C)
  have hpos :
      ∀ t, 0 < t → t ≤ C.T → ∀ x : intervalDomainPoint,
        0 < truncatedConjugatePicardLimit p u₀ C.T t x :=
    strictPos_of_jensenBypassStrictPosDataFor
      (H.jensenStrictPos hM hu₀ hbound C)
  exact conjugateMildSolutionData_of_uniformTruncatedCore HT hnonneg hpos

theorem uniformTruncatedJensen_initialTrace
    {p : CM2Params} (H : UniformTruncatedJensenAssemblyInputs p)
    {M : ℝ} (hM : 0 < M) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    (C : UniformConjugateMildExistenceCore p u₀) :
    InitialTrace intervalDomain u₀
      (conjugateMildSolutionData_of_uniformTruncatedJensen
        H hM hu₀ hbound C).u := by
  dsimp [conjugateMildSolutionData_of_uniformTruncatedJensen,
    conjugateMildSolutionData_of_uniformTruncatedCore]
  exact H.initialTrace hM hu₀ hbound C

theorem uniformTruncatedJensen_fullAgreement
    {p : CM2Params} (H : UniformTruncatedJensenAssemblyInputs p)
    {M : ℝ} (hM : 0 < M) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    (C : UniformConjugateMildExistenceCore p u₀) :
    (conjugateMildSolutionData_of_uniformTruncatedJensen
      H hM hu₀ hbound C).u =
        conjugatePicardLimit p u₀ C.T := by
  dsimp [conjugateMildSolutionData_of_uniformTruncatedJensen,
    conjugateMildSolutionData_of_uniformTruncatedCore]
  exact H.fullAgreement hM hu₀ hbound C

theorem coupledFluxClassicalLocalExistenceResidual_v4
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : UniformTruncatedJensenAssemblyInputs p)
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
  have hu₀_cont : Continuous u₀I :=
    (PositiveInitialDatum.admissible hu₀I).2
  obtain ⟨C, hCT⟩ := Huniform hu₀_cont hboundI
  let S : ConjugateMildSolutionData p u₀I :=
    conjugateMildSolutionData_of_uniformTruncatedJensen
      H hM hu₀I hboundI C
  have hTrace : InitialTrace intervalDomain u₀I S.u := by
    simpa [S] using
      uniformTruncatedJensen_initialTrace H hM hu₀I hboundI C
  obtain ⟨u, v, hclass, htrace⟩ :=
    localClassicalSolution_of_conjugateMild_spectral
      S (HSpectral S) hTrace
  refine ⟨u, v, ?_, htrace⟩
  have hST : S.T = T := by
    dsimp [S, conjugateMildSolutionData_of_uniformTruncatedJensen,
      conjugateMildSolutionData_of_uniformTruncatedCore]
    exact hCT
  simpa [hST] using hclass

theorem theorem_1_1_intervalDomain_chiNeg_v4
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : UniformTruncatedJensenAssemblyInputs p)
    (HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀),
      BFormMildSpectralBootstrapData p S) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ
    (coupledFluxClassicalLocalExistenceResidual_v4 p hα hγ H HSpectral)

#print axioms strictPos_of_jensenBypassStrictPosDataFor
#print axioms conjugateMildSolutionData_of_uniformTruncatedJensen
#print axioms coupledFluxClassicalLocalExistenceResidual_v4
#print axioms theorem_1_1_intervalDomain_chiNeg_v4

end ShenWork.Paper2.IntervalChiNegFinalAssemblyV4
