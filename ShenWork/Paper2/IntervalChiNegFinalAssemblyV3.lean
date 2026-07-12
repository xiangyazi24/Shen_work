import ShenWork.Paper2.IntervalBFormMildClassicalBootstrap
import ShenWork.Paper2.IntervalResolverBootstrapFromMild
import ShenWork.Paper2.IntervalCoeffLadderFull
import ShenWork.Paper2.Brick2ShiftedGlobalize
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual
import ShenWork.Paper2.IntervalUniformConjugateCore
import ShenWork.PDE.IntervalHeatSemigroupStrictPositivity

/-!
  V3 no-patch assembly for the chi-negative interval branch.

  The single solution produced from the uniform conjugate core is fed directly
  to the positive-time spectral bootstrap and then to the landed
  mild-to-classical theorem.  No restart or patch frontier appears here.
-/

open Set Filter
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData UniformConjugateMildExistenceCore
   conjugatePicardLimit uniformConjugateMildExistenceCore_exists)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement LogisticCosineFourierData
   ChemDivCosineFourierData bFormSourceCoeffs)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.Paper2.IntervalCoeffLadderFull
  (WindowCoefficientEnvelope eigenvalue_weighted_summable_of_pass4)
open ShenWork.Paper2.IntervalResolverBootstrapFromMild
  (ResolverSourceWitnessFromMild hResolverData_of_sourceWitness
   hResolverPos_of_conjugateMild)
open ShenWork.Paper2.ChiNegResidual
  (CoupledFluxClassicalLocalExistenceResidual)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegFinalAssemblyV3

/-- Positive-time spectral data for the single uniform-core mild solution. -/
structure PositiveTimeSpectralBootstrapFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop where
  hTimeNhd : HasTimeNeighborhoodSpectralAgreement S.T S.u
  hResolverData : HasResolverDirectSpectralData S.T
    (mildChemicalConcentration p S.u) p
  hPdeAgreement : HasBFormSpectralPdeAgreement p S.T S.u

/-- The clamped B-form source used to globalize a positive-time window source. -/
def clampedBFormSource
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (offset cLow c d dHigh : ℝ) : ℝ → ℕ → ℝ :=
  fun σ n =>
    bFormSourceCoeffs p u
      (ShenWork.IntervalTimeSoftClamp.φ cLow c d dHigh (offset + σ)) n

/-- Per-interior-time delivered ladder/source data used by the V3 frontier. -/
structure LadderOutput
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) (t₀ : ℝ) : Type where
  offset : ℝ
  cLow : ℝ
  c : ℝ
  d : ℝ
  dHigh : ℝ
  hcLow : cLow < c
  hcd : c ≤ d
  hdHigh : d < dHigh
  hcLow_pos : 0 < cLow
  hdHigh_lt : dHigh < S.T
  hoff : 0 < t₀ - offset
  ht_active : offset + (t₀ - offset) ∈ Set.Icc c d
  aInit : ℕ → ℝ
  MInit : ℝ
  hMInit : 0 ≤ MInit
  haInit : ∀ n, |aInit n| ≤ MInit
  env4 : WindowCoefficientEnvelope 4 (t₀ - offset) (t₀ - offset)
    (fun σ n => localRestartCoeff aInit
      (clampedBFormSource p S.u offset cLow c d dHigh) σ n)
  hrep : ∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
    S.u s x = ∑' n, localRestartCoeff aInit
      (clampedBFormSource p S.u offset cLow c d dHigh) (s - offset) n *
        cosineMode n x.1
  hlogData : LogisticCosineFourierData p S.u t₀
  hchemData : ChemDivCosineFourierData p (S.u t₀)
    (coupledChemicalConcentration p S.u t₀)
  resolverSource : ℝ → ℕ → ℝ
  resolverSrc : DuhamelSourceTimeC1 resolverSource
  resolverSet : Set ℝ
  resolverSet_mem : resolverSet ∈ 𝓝 t₀
  resolver_agree : ∀ s ∈ resolverSet, ∀ k,
    resolverSource s k =
      (ShenWork.PDE.intervalNeumannResolverSourceCoeff p (S.u s) k).re

/-- The delivered positive-time ladder and source packages assemble the three
spectral fields required by the V3 frontier. -/
theorem positiveTimeSpectralBootstrapFrontier_of_delivered
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hLadder : ∀ t₀, 0 < t₀ → t₀ < S.T → LadderOutput p S t₀)
    (hSourceTimeC1 : ∀ c T', 0 < c → T' < S.T →
      DuhamelSourceTimeC1On (bFormSourceCoeffs p S.u) c T') :
    PositiveTimeSpectralBootstrapFrontier p S := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    intro t₀ ht₀ ht₀T
    let L := hLadder t₀ ht₀ ht₀T
    let a := clampedBFormSource p S.u L.offset L.cLow L.c L.d L.dHigh
    have src : DuhamelSourceTimeC1 a := by
      have srcOn := hSourceTimeC1 L.cLow L.dHigh L.hcLow_pos L.hdHigh_lt
      simpa [a, clampedBFormSource] using
        ShenWork.IntervalDuhamelSourceTimeC1On.duhamelSourceTimeC1_of_shifted_On
          (τ := L.offset) srcOn L.hcLow L.hcd L.hdHigh
    exact ⟨L.aInit, L.MInit, L.hMInit, L.haInit, a, src, L.offset,
      L.hoff, by simpa [a] using L.hrep⟩
  · refine hResolverData_of_sourceWitness ?_
    intro t₀ ht₀ ht₀T
    let L := hLadder t₀ ht₀ ht₀T
    exact ⟨L.resolverSource, L.resolverSrc, L.resolverSet,
      L.resolverSet_mem, L.resolver_agree⟩
  · constructor
    intro t₀ ht₀ ht₀T x hx
    let L := hLadder t₀ ht₀ ht₀T
    let a := clampedBFormSource p S.u L.offset L.cLow L.c L.d L.dHigh
    have src : DuhamelSourceTimeC1 a := by
      have srcOn := hSourceTimeC1 L.cLow L.dHigh L.hcLow_pos L.hdHigh_lt
      simpa [a, clampedBFormSource] using
        ShenWork.IntervalDuhamelSourceTimeC1On.duhamelSourceTimeC1_of_shifted_On
          (τ := L.offset) srcOn L.hcLow L.hcd L.hdHigh
    have hsource_at : ∀ n, a (t₀ - L.offset) n =
        coupledLogisticSourceCoeffs p S.u t₀ n
          - p.χ₀ * coupledChemDivSourceCoeffs p S.u t₀ n := by
      intro n
      have hclamp :=
        ShenWork.IntervalDuhamelSourceTimeC1On.shiftedClamped_eq_on
          (a := bFormSourceCoeffs p S.u) (τ := L.offset)
          L.hcLow L.hdHigh L.ht_active n
      have harg : L.offset + (t₀ - L.offset) = t₀ := by ring
      simpa [a, clampedBFormSource, bFormSourceCoeffs, harg] using hclamp
    have hsum : Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |localRestartCoeff L.aInit a (t₀ - L.offset) n|) := by
      have hmem : t₀ - L.offset ∈ Set.Icc (t₀ - L.offset) (t₀ - L.offset) :=
        ⟨le_rfl, le_rfl⟩
      simpa [a] using
        eigenvalue_weighted_summable_of_pass4 L.env4 hmem
    exact ⟨L.aInit, L.MInit, L.hMInit, L.haInit, a, src, L.offset,
      L.hoff, L.hlogData, L.hchemData, by simpa [a] using L.hrep,
      hsource_at, hsum⟩

/-- The non-spectral V3 core frontier: the uniform core really yields the
single conjugate mild solution, with the Picard-limit identity and initial
trace on the same horizon. -/
structure UniformCoreMildSolutionFrontier (p : CM2Params) : Prop where
  exists_solution :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        ∃ S : ConjugateMildSolutionData p u₀,
          S.T = C.T ∧
          S.M = C.R ∧
          S.u = conjugatePicardLimit p u₀ C.T ∧
          InitialTrace intervalDomain u₀ S.u

/-- Conditional inputs for the weak-PID uniform core.  Cron2 does not yet apply
to `UniformConjugateMildExistenceCore`: its certificate is for old
`ConjugateMildExistenceData`, whose constructors use the PPID floor via
`hbase_nonneg`/`hmapsTo_nn`/`hmapsTo_pos`, and still require truncated data,
bridge, mild-to-weak, and the negative-part energy core. -/
structure UniformCoreMildSolutionConditionalInputs (p : CM2Params) : Prop where
  hnonneg : ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ}, PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) → ∀ C : UniformConjugateMildExistenceCore p u₀, ∀ t, 0 < t → t ≤ C.T → ∀ x, 0 ≤ conjugatePicardLimit p u₀ C.T t x
  hpos : ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ}, PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) → ∀ C : UniformConjugateMildExistenceCore p u₀, ∀ t, 0 < t → t ≤ C.T → ∀ x, 0 < conjugatePicardLimit p u₀ C.T t x
  package : ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ}, PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) → ∀ C : UniformConjugateMildExistenceCore p u₀, (∀ t, 0 < t → t ≤ C.T → ∀ x, 0 ≤ conjugatePicardLimit p u₀ C.T t x) → (∀ t, 0 < t → t ≤ C.T → ∀ x, 0 < conjugatePicardLimit p u₀ C.T t x) → ∃ S : ConjugateMildSolutionData p u₀, S.T = C.T ∧ S.M = C.R ∧ S.u = conjugatePicardLimit p u₀ C.T ∧ InitialTrace intervalDomain u₀ S.u

/-- Conditional closure of the V3 uniform-core mild-solution frontier. -/
theorem uniformCoreMildSolutionFrontier_of_conditionalInputs
    {p : CM2Params} (H : UniformCoreMildSolutionConditionalInputs p) :
    UniformCoreMildSolutionFrontier p where
  exists_solution := by
    intro M hM u₀ hu₀ hu₀_bound C
    exact H.package hM hu₀ hu₀_bound C
      (H.hnonneg hM hu₀ hu₀_bound C) (H.hpos hM hu₀ hu₀_bound C)

/-- The positive-time frontier supplies the exact bootstrap record consumed by
the landed mild-to-classical theorem; resolver strict positivity is already
available for every conjugate mild solution. -/
def bootstrapData_of_positiveTime_frontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (F : PositiveTimeSpectralBootstrapFrontier p S) :
    BFormMildSpectralBootstrapData p S where
  hPdeAgreement := F.hPdeAgreement
  hTimeNhd := F.hTimeNhd
  hResolverData := F.hResolverData
  hResolverPos := hResolverPos_of_conjugateMild p S

/-- V3 no-patch assembly: the uniform-core solution itself is the classical
solution on positive time. -/
theorem coupledFluxClassicalLocalExistenceResidual_v3
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (HCore : UniformCoreMildSolutionFrontier p)
    (HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀),
      PositiveTimeSpectralBootstrapFrontier p S) :
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
  obtain ⟨S, hST, _hSM, _hSu, hTrace⟩ :=
    HCore.exists_solution hM hu₀I hboundI C
  have Hboot : BFormMildSpectralBootstrapData p S :=
    bootstrapData_of_positiveTime_frontier S (HSpectral S)
  obtain ⟨u, v, hclass, htrace⟩ :=
    localClassicalSolution_of_conjugateMild_spectral S Hboot hTrace
  refine ⟨u, v, ?_, htrace⟩
  have hST' : S.T = T := hST.trans hCT
  simpa [hST'] using hclass

#print axioms bootstrapData_of_positiveTime_frontier
#print axioms uniformCoreMildSolutionFrontier_of_conditionalInputs
#print axioms coupledFluxClassicalLocalExistenceResidual_v3
end ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
