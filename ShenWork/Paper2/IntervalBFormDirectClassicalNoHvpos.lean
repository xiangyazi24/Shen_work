/-
  ShenWork/Paper2/IntervalBFormDirectClassicalNoHvpos.lean

  Direct B-form frontier with the resolver strict-positivity field filled from
  the conjugate-data strict positivity producer.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalBFormDirectClassical
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqBankedConcrete
import ShenWork.Paper2.IntervalDomainTheorem11StrongPath

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.Paper2
open ShenWork.Paper2.BFormDirectClassical

noncomputable section

namespace ShenWork.Paper2.BFormDirectClassical

/-- Direct B-form frontier with the resolver strict-positivity field removed. -/
structure BFormDirectFrontierNoHvpos
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p

/-- Fill the original direct B-form `hVpos` field using the conjugate-data
strict resolver positivity producer. -/
def bFormDirectFrontier_of_noHvpos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontierNoHvpos p DB) :
    BFormDirectFrontier p DB where
  bank := F.bank
  hTimeNhd := F.hTimeNhd
  hResolverData := F.hResolverData
  hVpos :=
    ShenWork.Paper2.BFormPositiveDatumLocalSq.bform_mildChemicalConcentration_pos_of_conjugate_data
      p DB

/-- Local classical existence from the direct B-form frontier with `hVpos`
discharged internally. -/
theorem localClassicalSolution_of_BFormDirectFrontier_noHvpos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontierNoHvpos p DB) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u :=
  localClassicalSolution_of_BFormDirectFrontier
    (bFormDirectFrontier_of_noHvpos F)

/-- Per-datum direct B-form frontier for paper-positive data with `hVpos`
removed. -/
def BFormPaperLocalFrontierNoHvpos (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (BFormDirectFrontierNoHvpos p DB)

/-- The no-`hVpos` direct frontier implies the original direct frontier. -/
theorem bFormPaperLocalFrontier_of_noHvpos
    {p : CM2Params}
    (hPerDatum : BFormPaperLocalFrontierNoHvpos p) :
    BFormPaperLocalFrontier p := by
  intro u₀ hu₀
  obtain ⟨DB, ⟨F⟩⟩ := hPerDatum u₀ hu₀
  exact ⟨DB, ⟨bFormDirectFrontier_of_noHvpos F⟩⟩

/-- Paper-positive local existence from the direct B-form frontier with `hVpos`
discharged internally. -/
theorem paperPositive_localExistence_of_BFormDirect_noHvpos
    {p : CM2Params}
    (hPerDatum : BFormPaperLocalFrontierNoHvpos p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u :=
  paperPositive_localExistence_of_BFormDirect
    (bFormPaperLocalFrontier_of_noHvpos hPerDatum)

/-- Direct B-form no-`hVpos` headline through the PPID-typed strong path. -/
theorem paper2_theorem_1_1_general_chi_bformDirect_noHvpos_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPaperLocalFrontierNoHvpos p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one
    (paperPositive_localExistence_of_BFormDirect_noHvpos hPerDatum)
    hQuant

#print axioms bFormDirectFrontier_of_noHvpos
#print axioms localClassicalSolution_of_BFormDirectFrontier_noHvpos
#print axioms bFormPaperLocalFrontier_of_noHvpos
#print axioms paperPositive_localExistence_of_BFormDirect_noHvpos
#print axioms paper2_theorem_1_1_general_chi_bformDirect_noHvpos_from_ppid_quant

end ShenWork.Paper2.BFormDirectClassical
