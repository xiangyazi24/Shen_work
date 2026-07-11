import ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
import ShenWork.Paper2.IntervalResolverBootstrapFromMild

/-!
# HSpectral producer for the χ₀<0 V6 assembly — generic-`S` assembler

The V6 assembly consumes
`HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀), BFormMildSpectralBootstrapData p S`.
`BFormMildSpectralBootstrapData` mentions only `S.T` and `S.u`, so it is built
generically from a `ConjugateMildSolutionData` — no reference to how `S.u` was
constructed, and in particular no dependence on the truncated Picard limit.

This file assembles the four bootstrap fields from a minimal *leaf bundle* on
`S.u`:

* `hResolverPos` is **free** — `hResolverPos_of_conjugateMild` derives resolver
  strict positivity from `S.hcont`/`S.hpos`/`S.hbound`.
* `hTimeNhd` is **derived** from `hPdeAgreement`: the time-neighbourhood
  spectral witness is exactly the restart-representation part of the PDE
  agreement's data, read off at the interior midpoint `x = 1/2`.
* `hResolverData` comes from a `ResolverSourceWitnessFromMild` leaf via
  `hResolverData_of_sourceWitness`.
* `hPdeAgreement` is itself carried as a leaf (`HasBFormSpectralPdeAgreement`),
  a Prop about the slices of `S.u`.

The remaining genuinely-analytic content — the eigenvalue-weighted source
ladder producing `HasBFormSpectralPdeAgreement` and the resolver source witness
— is isolated as the leaf fields below and discharged separately.
-/

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalBFormSpectral (HasBFormSpectralPdeAgreement)
open ShenWork.Paper2.IntervalResolverBootstrapFromMild
  (ResolverSourceWitnessFromMild hResolverData_of_sourceWitness
   hResolverPos_of_conjugateMild)
open ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
  (PositiveTimeSpectralBootstrapFrontier bootstrapData_of_positiveTime_frontier)

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedSpectralProducerV6

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

/-- The minimal analytic leaf bundle from which `HSpectral` is assembled for a
generic `ConjugateMildSolutionData`.  Both fields are statements about the
slices of `S.u`; neither refers to the construction of `S.u`. -/
structure BFormMildSpectralLeaves
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop where
  /-- The eigenvalue-weighted B-form spectral PDE agreement (the source ladder
  output). -/
  hPdeAgreement : HasBFormSpectralPdeAgreement p S.T S.u
  /-- The per-interior-time resolver source witness. -/
  hResolverWitness : ResolverSourceWitnessFromMild p S

/-- Assemble the positive-time spectral frontier from the leaf bundle, without
touching the dead `LadderOutput` interface: `hResolverData` from the witness,
`hResolverPos` for free, and `hTimeNhd` derived from `hPdeAgreement`. -/
def spectralFrontier_of_leaves
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀}
    (H : BFormMildSpectralLeaves p S) :
    PositiveTimeSpectralBootstrapFrontier p S where
  hTimeNhd :=
    hasTimeNeighborhoodSpectralAgreement_of_pdeAgreement H.hPdeAgreement
  hResolverData := hResolverData_of_sourceWitness H.hResolverWitness
  hPdeAgreement := H.hPdeAgreement

/-- The generic-`S` `HSpectral` producer, reduced to the leaf bundle. -/
def bFormMildSpectralBootstrapData_of_leaves
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀}
    (H : BFormMildSpectralLeaves p S) :
    ShenWork.Paper2.BFormMildSpectralBootstrapData p S :=
  bootstrapData_of_positiveTime_frontier S (spectralFrontier_of_leaves H)

#print axioms bFormMildSpectralBootstrapData_of_leaves

end ShenWork.Paper2.IntervalTruncatedSpectralProducerV6
