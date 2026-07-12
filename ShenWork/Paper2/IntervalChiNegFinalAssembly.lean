import ShenWork.Paper2.IntervalBFormMildClassicalBootstrap
import ShenWork.Paper2.IntervalResolverBootstrapFromMild
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalLogisticSourceTimeC1OnFromMild
import ShenWork.Paper2.IntervalConjugateChemDivSourceTimeC1On
import ShenWork.Paper2.IntervalConjugatePicardCoreInhabit
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual
import ShenWork.Paper2.IntervalUniformConjugateCore
import ShenWork.PDE.IntervalHeatSemigroupStrictPositivity

/-!
  Final B-form spectral assembly for the chi-negative interval branch.

  The file does not invent analytic input.  It wires the landed classical
  bootstrap from a conjugate mild solution and records the remaining frontiers
  explicitly:

  * `FinalPerDatumSpectralFrontier`: the local B-form spectral PDE agreement,
    the time-neighborhood restart agreement, and the resolver source witness.
    This is where the chem-div/Fourier and eigenvalue-ladder data live.
  * `PPIDSpectralBootstrapFrontier`: the spectral/bootstrap theorem only for
    restarted paper-positive data.
  * `HeatRestartPatchFrontier`: the weak-PID-to-restarted-PPID heat smoothing
    and the short initial-time patching.  This is intentionally separate from
    the PPID spectral frontier, so weak input data are never required to be
    paper-positive at time zero.
-/

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceCore ConjugateMildSolutionData
   UniformConjugateMildExistenceCore conjugateMildExistenceCore_exists
   uniformConjugateMildExistenceCore_exists conjugateMildSolutionData_of_data
   conjugatePicardLimit)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement bFormSourceCoeffs
   bFormSource_duhamelSourceTimeC1On)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2.IntervalResolverBootstrapFromMild
  (ResolverSourceWitnessFromMild hResolverData_of_sourceWitness
   hResolverPos_of_conjugateMild)
open ShenWork.Paper2.ChiNegResidual
  (CoupledFluxClassicalLocalExistenceResidual)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegFinalAssembly

/-- Step 1 of the final chain: combine logistic and chem-div coefficient
regularity on the same positive time window into the B-form source package. -/
def bFormSource_timeC1On_of_logistic_chemDiv
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {c T' : ℝ}
    (hlog : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p S.u) c T')
    (hchem : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p S.u) c T') :
    DuhamelSourceTimeC1On (bFormSourceCoeffs p S.u) c T' :=
  bFormSource_duhamelSourceTimeC1On hlog hchem

/-- The conjugate mild solution supplied by the landed Picard core. -/
def finalConjugateMildCore
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ConjugateMildExistenceCore p u₀ :=
  Classical.choice
    (conjugateMildExistenceCore_exists p hα hγ hu₀).choose_spec.1

/-- Pack the landed Picard core as `ConjugateMildSolutionData`. -/
def finalConjugateMildData
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ConjugateMildSolutionData p u₀ :=
  conjugateMildSolutionData_of_data
    (finalConjugateMildCore p hα hγ hu₀).toData

/-- Initial trace for the chosen final conjugate mild solution. -/
theorem finalConjugateMildData_initialTrace
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    InitialTrace intervalDomain u₀
      (finalConjugateMildData p hα hγ hu₀).u := by
  simpa [finalConjugateMildData] using
    ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
        p (PaperPositiveInitialDatum.admissible hu₀).2
        (finalConjugateMildCore p hα hγ hu₀).toData

/-- Per-datum spectral frontiers needed by
`BFormMildSpectralBootstrapData`.  The first field contains the B-form PDE
source split, logistic/chem-div Fourier data, and the eigenvalue-weighted
restart summability; the third field is the resolver time-regular source
witness. -/
structure FinalPerDatumSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop where
  hPdeAgreement : HasBFormSpectralPdeAgreement p S.T S.u
  hTimeNhd : HasTimeNeighborhoodSpectralAgreement S.T S.u
  hResolverWitness : ResolverSourceWitnessFromMild p S

/-- Assemble the four fields consumed by the landed mild-to-classical theorem. -/
def bootstrapData_of_final_frontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (F : FinalPerDatumSpectralFrontier p S) :
    BFormMildSpectralBootstrapData p S where
  hPdeAgreement := F.hPdeAgreement
  hTimeNhd := F.hTimeNhd
  hResolverData := hResolverData_of_sourceWitness F.hResolverWitness
  hResolverPos := hResolverPos_of_conjugateMild p S

/-- Per-paper-positive datum local classical solution from the final frontier. -/
theorem paperPositive_localClassicalSolution_of_final_frontier
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (F : FinalPerDatumSpectralFrontier p
      (finalConjugateMildData p hα hγ hu₀)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  let S := finalConjugateMildData p hα hγ hu₀
  have Hboot : BFormMildSpectralBootstrapData p S :=
    bootstrapData_of_final_frontier S (by simpa [S] using F)
  have hTrace : InitialTrace intervalDomain u₀ S.u := by
    simpa [S] using finalConjugateMildData_initialTrace p hα hγ hu₀
  obtain ⟨u, v, hclass, htrace⟩ :=
    localClassicalSolution_of_conjugateMild_spectral S Hboot hTrace
  exact ⟨S.T, S.hT, u, v, hclass, htrace⟩

/-- The internal restart datum obtained from the floor-free Picard limit. -/
def weakRestartDatum
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T ε : ℝ) :
    intervalDomainPoint → ℝ :=
  conjugatePicardLimit p u₀ T ε

/-- Spectral/bootstrap frontier for paper-positive restart data only.  The
interface deliberately says nothing about weak positive data at time zero. -/
def PPIDSpectralBootstrapFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ {w : intervalDomainPoint → ℝ},
    PaperPositiveInitialDatum intervalDomain w →
    (∀ x, |w x| ≤ M) →
      ∃ S : ConjugateMildSolutionData p w,
        BFormMildSpectralBootstrapData p S ∧
          InitialTrace intervalDomain w S.u

/-- Heat-smoothing and patching frontier for weak positive input data.

The first field records a posteriori nonnegativity of the uniform Picard limit.
The second field is the weak-PID to PPID restart bridge at a positive time.
The last field patches the initial weak mild segment to the restarted classical
solution supplied by `PPIDSpectralBootstrapFrontier`. -/
structure HeatRestartPatchFrontier (p : CM2Params) : Prop where
  uniform_nonneg :
    ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        ∀ t x, 0 < t → t ≤ C.T →
          0 ≤ conjugatePicardLimit p u₀ C.T t x
  restart_ppid :
    ∀ {M T : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        C.T = T →
          ∃ ε : ℝ, 0 < ε ∧ ε < T ∧
            PaperPositiveInitialDatum intervalDomain
              (weakRestartDatum p u₀ T ε) ∧
            (∀ x, |weakRestartDatum p u₀ T ε x| ≤ C.R)
  patch_from_restart :
    ∀ {M T ε : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
      ∀ C : UniformConjugateMildExistenceCore p u₀,
        C.T = T →
        0 < ε →
        ε < T →
        PaperPositiveInitialDatum intervalDomain
          (weakRestartDatum p u₀ T ε) →
        (∀ x, |weakRestartDatum p u₀ T ε x| ≤ C.R) →
        ∀ {S : ConjugateMildSolutionData p
            (weakRestartDatum p u₀ T ε)},
          BFormMildSpectralBootstrapData p S →
          InitialTrace intervalDomain (weakRestartDatum p u₀ T ε) S.u →
            ∃ u v : ℝ → intervalDomainPoint → ℝ,
              IsPaper2ClassicalSolution intervalDomain p (T / 2) u v ∧
              InitialTrace intervalDomain u₀ u

/-- Corrected final assembly.  Weak PID data enter the uniform floor-free core;
PPID appears only for the internal positive-time restart datum. -/
theorem coupledFluxClassicalLocalExistenceResidual_v2
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hppid : PPIDSpectralBootstrapFrontier p)
    (Hrestart : HeatRestartPatchFrontier p) :
    CoupledFluxClassicalLocalExistenceResidual p := by
  intro M hM
  obtain ⟨T, hT, Hcore⟩ :=
    uniformConjugateMildExistenceCore_exists p hα hγ M hM
  refine ⟨T / 2, by linarith, ?_⟩
  intro u₀ hu₀ hbound
  have hu₀_cont : Continuous u₀ :=
    (PositiveInitialDatum.admissible hu₀).2
  obtain ⟨C, hCT⟩ := Hcore hu₀_cont hbound
  obtain ⟨ε, hε, hεT, hwPaper, hwBound⟩ :=
    Hrestart.restart_ppid hM hu₀ hbound C hCT
  obtain ⟨S, Hboot, hTrace_w⟩ :=
    Hppid C.R C.hR hwPaper hwBound
  exact
    Hrestart.patch_from_restart hM hu₀ hbound C hCT hε hεT
      hwPaper hwBound Hboot hTrace_w

#print axioms bFormSource_timeC1On_of_logistic_chemDiv
#print axioms bootstrapData_of_final_frontier
#print axioms paperPositive_localClassicalSolution_of_final_frontier
#print axioms coupledFluxClassicalLocalExistenceResidual_v2

end ShenWork.Paper2.IntervalChiNegFinalAssembly
