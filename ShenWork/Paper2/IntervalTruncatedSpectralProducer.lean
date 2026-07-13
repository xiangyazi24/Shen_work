import ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
import ShenWork.Paper2.IntervalResolverBootstrapFromMild
import ShenWork.Paper2.IntervalBFormSpectralProviderDischarge
import ShenWork.Paper2.IntervalMildPositiveTimeRegularity

/-!
# HSpectral producer for the χ₀<0 V6 assembly — generic-`S` assembler

The V6 assembly consumes
`HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀), BFormMildSpectralBootstrapData p S`.
`BFormMildSpectralBootstrapData` mentions only `S.T` and `S.u`, so it is built
generically from a `ConjugateMildSolutionData` — no reference to how `S.u` was
constructed, and in particular no dependence on the truncated Picard limit.

This file assembles the four bootstrap fields from analytic *leaves* on `S.u`:

* `hResolverPos` is **free** — `hResolverPos_of_conjugateMild` derives resolver
  strict positivity from `S.hcont`/`S.hpos`/`S.hbound`.
* `hTimeNhd` is **derived** from `hPdeAgreement`: the time-neighbourhood
  spectral witness is exactly the restart-representation part of the PDE
  agreement's data, read off at the interior midpoint `x = 1/2`.
* `hResolverData` comes from a `ResolverSourceWitnessFromMild` leaf.
* `hPdeAgreement` is produced by `hasBFormSpectralPdeAgreement_of_leaves`
  (the generic-`S` port of the conjugate-route localized provider), which
  reduces it to the atomic leaves: a per-slice cosine realization of `S.u`
  (`bc`/`hbsum`/`hagree`), the B-form source `DuhamelSourceTimeC1` (`hsrcB`),
  the restart cosine representation (`hB_restart`), and the logistic/chem-div
  Fourier data.  `hpost` is discharged from `S.hpos`, the source-split from the
  definition of `bFormSourceCoeffs`, and the eigenvalue-weighted summability
  from the generic engine `localRestartCoeff_eigenvalue_summable` — bypassing
  the dead `LadderOutput`/`env4` pointwise ladder.
-/

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral
  (HasBFormSpectralPdeAgreement LogisticCosineFourierData
   ChemDivCosineFourierData bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.Paper2.IntervalResolverBootstrapFromMild
  (ResolverSourceWitnessFromMild hResolverData_of_sourceWitness
   hResolverPos_of_conjugateMild)
open ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
  (PositiveTimeSpectralBootstrapFrontier bootstrapData_of_positiveTime_frontier)
open ShenWork.Paper2.IntervalMildPositiveTimeRegularity
  (RestartRepresentation restartSliceCoeff restartSliceCoeff_eigenvalueSummable
   restartSliceCoeff_realization)

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedSpectralProducer

/-- Interior midpoint of `[0,1]`, used to read the restart representation off
the PDE-agreement data. -/
def spectralMidpoint : intervalDomainPoint :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

theorem spectralMidpoint_mem_Ioo :
    (spectralMidpoint : intervalDomainPoint).1 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> norm_num [spectralMidpoint]

/-- The time-neighbourhood spectral agreement is the restart-representation
sub-datum of the B-form PDE agreement: at each interior time, evaluate the
agreement's `exists_data` at the interior midpoint and forget the Fourier /
source-split / eigenvalue-summability parts. -/
theorem hasTimeNeighborhoodSpectralAgreement_of_pdeAgreement
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u) :
    HasTimeNeighborhoodSpectralAgreement T u := by
  constructor
  intro t₀ ht₀ ht₀T
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hoff,
      _hlogData, _hchemData, hrep, _hsource_split, _hsum_b⟩ :=
    Hpde.exists_data t₀ ht₀ ht₀T spectralMidpoint_mem_Ioo
  exact ⟨a₀, M, hM, ha₀, a, src, offset, hoff, hrep⟩

/-- Positivity of a lifted slice from the strict-positivity field of the
`ConjugateMildSolutionData`. -/
theorem lift_pos_of_hpos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < S.T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (S.u σ) x := by
  intro x hx
  rw [intervalDomainLift, dif_pos hx]
  exact S.hpos σ hσ hσT.le ⟨x, hx⟩

/-- Upper bound of a lifted slice from the boundedness field. -/
theorem lift_le_of_hbound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < S.T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (S.u σ) x ≤ S.M := by
  intro x hx
  rw [intervalDomainLift, dif_pos hx]
  exact (abs_le.mp (S.hbound σ hσ hσT.le ⟨x, hx⟩)).2

/-- Generic-`S` B-form spectral PDE agreement from the atomic analytic leaves.

This is the port of
`hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_localized_data_with_hpost`
to a generic `ConjugateMildSolutionData`: `hpost`/`hubt` are supplied by
`S.hpos`/`S.hbound`, the source family is fixed to `bFormSourceCoeffs p S.u`
(so the source-split is definitional), and the eigenvalue-weighted summability
is the generic engine `localRestartCoeff_eigenvalue_summable`. -/
theorem hasBFormSpectralPdeAgreement_of_leaves
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < S.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < S.T →
      Set.EqOn (intervalDomainLift (S.u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p S.u))
    (hB_restart : ∀ t₀, 0 < t₀ → t₀ < S.T →
      ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        S.u s y =
          ∑' n,
            localRestartCoeff
              (cosineCoeffs (intervalDomainLift (S.u (t₀ / 2))))
              (fun σ n => bFormSourceCoeffs p S.u (t₀ / 2 + σ) n)
              (s - t₀ / 2) n * cosineMode n y.1)
    (hlogData : ∀ t, 0 < t → t < S.T →
      LogisticCosineFourierData p S.u t)
    (hchemData : ∀ t, 0 < t → t < S.T →
      ChemDivCosineFourierData p (S.u t)
        (coupledChemicalConcentration p S.u t)) :
    HasBFormSpectralPdeAgreement p S.T S.u := by
  constructor
  intro t₀ ht₀ ht₀T x _hx
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < S.T := by rw [hτdef]; linarith
  have htmτ : t₀ - τ = τ := by rw [hτdef]; ring
  have hMnn : 0 ≤ S.M := S.hM.le
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (S.u τ)) with ha₀def
  set aB : ℝ → ℕ → ℝ := bFormSourceCoeffs p S.u with haBdef
  set a : ℝ → ℕ → ℝ := fun σ n => aB (τ + σ) n with hadef
  have ha₀_bd : ∀ k, |a₀ k| ≤ 2 * S.M := by
    intro k
    refine ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) hMnn ?_ k
    intro y hy
    rw [abs_of_pos (lift_pos_of_hpos S hτpos hτT y hy)]
    have hyb := lift_le_of_hbound S hτpos hτT y hy
    linarith
  have srcShift : DuhamelSourceTimeC1 a := by
    simpa [a, aB, add_comm] using
      ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
        hsrcB hτpos.le
  have hoff : 0 < t₀ - τ := by rw [htmτ]; exact hτpos
  have hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      S.u s y = ∑' n, localRestartCoeff a₀ a (s - τ) n * cosineMode n y.1 := by
    have h := hB_restart t₀ ht₀ ht₀T
    simpa [a₀, a, aB, τ, hτdef] using h
  have hsource_at : ∀ n, a (t₀ - τ) n =
      coupledLogisticSourceCoeffs p S.u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p S.u t₀ n := by
    intro n
    have harg : τ + (t₀ - τ) = t₀ := by ring
    show aB (τ + (t₀ - τ)) n =
      coupledLogisticSourceCoeffs p S.u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p S.u t₀ n
    rw [harg]
    rfl
  have hsum_b : Summable (fun n =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (t₀ - τ) n|) := by
    rw [htmτ]
    exact ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      (τ := τ) (M := 2 * S.M) (a₀ := a₀) (a := a) hτpos ha₀_bd srcShift
  exact ⟨a₀, 2 * S.M, by nlinarith [S.hM.le], ha₀_bd,
    a, srcShift, τ, hoff, hlogData t₀ ht₀ ht₀T,
    hchemData t₀ ht₀ ht₀T, hrep, hsource_at, hsum_b⟩

/-- B-form spectral PDE agreement from the *reduced* leaf set: the per-slice
cosine realization (`bc`/`hbsum`/`hagree`) is derived from the restart
representation and the source `DuhamelSourceTimeC1` via the shared `(C1)`
regularity file (`restartSliceCoeff` and its summability/realization). -/
theorem hasBFormSpectralPdeAgreement_of_restart
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p S.u))
    (hB_restart : RestartRepresentation S)
    (hlogData : ∀ t, 0 < t → t < S.T →
      LogisticCosineFourierData p S.u t)
    (hchemData : ∀ t, 0 < t → t < S.T →
      ChemDivCosineFourierData p (S.u t)
        (coupledChemicalConcentration p S.u t)) :
    HasBFormSpectralPdeAgreement p S.T S.u :=
  hasBFormSpectralPdeAgreement_of_leaves S (restartSliceCoeff S)
    (fun σ hσ hσT => restartSliceCoeff_eigenvalueSummable S hsrcB hσ hσT)
    (fun σ hσ hσT => restartSliceCoeff_realization S hB_restart hσ hσT)
    hsrcB hB_restart hlogData hchemData

/-- The reduced analytic leaf bundle from which `HSpectral` is assembled for a
generic `ConjugateMildSolutionData`.  The per-slice cosine realization is no
longer a leaf — it is wired from `hB_restart` + `hsrcB` in the shared `(C1)`
file.  Every field is a statement about the slices of `S.u`; none refers to the
construction of `S.u`. -/
structure BFormMildSpectralLeaves
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) where
  /-- The B-form source `DuhamelSourceTimeC1` (the source ladder, facet C2a). -/
  hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p S.u)
  /-- The restart cosine representation of `S.u` near each interior time
  (facet C2b). -/
  hB_restart : RestartRepresentation S
  /-- Logistic Fourier data at each interior time. -/
  hlogData : ∀ t, 0 < t → t < S.T → LogisticCosineFourierData p S.u t
  /-- Chem-div Fourier data at each interior time. -/
  hchemData : ∀ t, 0 < t → t < S.T →
    ChemDivCosineFourierData p (S.u t)
      (coupledChemicalConcentration p S.u t)
  /-- The per-interior-time resolver source witness. -/
  hResolverWitness : ResolverSourceWitnessFromMild p S

/-- Assemble the positive-time spectral frontier from the reduced leaf bundle,
without touching the dead `LadderOutput` interface. -/
def spectralFrontier_of_leaves
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀}
    (H : BFormMildSpectralLeaves p S) :
    PositiveTimeSpectralBootstrapFrontier p S where
  hTimeNhd :=
    hasTimeNeighborhoodSpectralAgreement_of_pdeAgreement
      (hasBFormSpectralPdeAgreement_of_restart S H.hsrcB H.hB_restart
        H.hlogData H.hchemData)
  hResolverData := hResolverData_of_sourceWitness H.hResolverWitness
  hPdeAgreement :=
    hasBFormSpectralPdeAgreement_of_restart S H.hsrcB H.hB_restart
      H.hlogData H.hchemData

/-- The generic-`S` `HSpectral` producer, reduced to the atomic leaf bundle. -/
def bFormMildSpectralBootstrapData_of_leaves
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀}
    (H : BFormMildSpectralLeaves p S) :
    ShenWork.Paper2.BFormMildSpectralBootstrapData p S :=
  bootstrapData_of_positiveTime_frontier S (spectralFrontier_of_leaves H)

#print axioms bFormMildSpectralBootstrapData_of_leaves

end ShenWork.Paper2.IntervalTruncatedSpectralProducer
