import ShenWork.Paper2.IntervalBFormPositiveDatumQuantWiring
import ShenWork.Paper2.IntervalDomainTheorem11StrongPath

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.BFormPositiveDatumNegPart

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Paper-positive negative-part B-form headline through the PPID-typed strong
path. -/
theorem paper2_theorem_1_1_general_chi_bform_paper_negpart_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPaperPositiveLocalFrontier p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one
    (paperPositiveDatum_localExistence_of_BForm hPerDatum)
    hQuant

section AxiomAudit

#print axioms paper2_theorem_1_1_general_chi_bform_paper_negpart_from_ppid_quant

end AxiomAudit

end ShenWork.Paper2.BFormPositiveDatumNegPart

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- Squared-barrier B-form headline through the PPID-typed strong path.

Unlike the older `from_quant` wrappers in `IntervalBFormPositiveDatumQuantWiring`,
the quantitative factory here is typed over `PaperPositiveInitialDatum`, matching
the actual datum class of `Theorem_1_1`. -/
theorem paper2_theorem_1_1_general_chi_bformSq_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one
    (positiveDatum_localExistence_of_BFormSq hBForm)
    hQuant

/-- Squared-barrier B-form headline through the paper-positive negative-part
frontier and PPID-typed strong path. -/
theorem paper2_theorem_1_1_general_chi_bformSq_negpart_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_paper_negpart_from_ppid_quant
    p hχ ha hb hγ_ge_one
    (bFormPaperPositiveLocalFrontier_of_sq hBForm)
    hQuant

/-- Banked squared-barrier B-form headline through the PPID-typed strong path. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_banked_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hbanked :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedPlumbing p DB))
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one
    (positiveDatum_localExistence_of_BFormSq
      (positiveDatumBFormLocalHypSq_of_banked hbanked))
    hQuant

/-- Concrete-banked squared-barrier B-form headline through the PPID-typed
strong path. -/
theorem
    paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hdeep :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData p u₀,
            Nonempty (PositiveDatumBFormSqBankedConcreteHypotheses p DB))
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bformSq_of_banked_from_ppid_quant
    p hχ ha hb hγ_ge_one
    (hbanked_concrete_of_deep_hypotheses hdeep)
    hQuant

/-- Regular squared-barrier B-form headline through the PPID-typed strong path. -/
theorem paper2_theorem_1_1_general_chi_bformSq_regular_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one
    (positiveDatum_localExistence_of_BFormSqRegular hBForm)
    hQuant

/-- Regular squared-barrier B-form headline through the paper-positive
negative-part frontier and PPID-typed strong path. -/
theorem paper2_theorem_1_1_general_chi_bformSq_regular_negpart_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_paper_negpart_from_ppid_quant
    p hχ ha hb hγ_ge_one
    (bFormPaperPositiveLocalFrontier_of_sqRegular hBForm)
    hQuant

/-- Deepest squared-barrier B-form headline through the PPID-typed strong path. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one
    (positiveDatum_localExistence_of_BFormSq_deepest hdeepest)
    hQuant

/-- Deepest squared-barrier B-form headline through the paper-positive
negative-part frontier and PPID-typed strong path. -/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest_negpart_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_general_chi_bform_paper_negpart_from_ppid_quant
    p hχ ha hb hγ_ge_one
    (bFormPaperPositiveLocalFrontier_of_sqDeepest hdeepest)
    hQuant

section AxiomAudit

#print axioms paper2_theorem_1_1_general_chi_bformSq_from_ppid_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_negpart_from_ppid_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_of_banked_from_ppid_quant
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_concrete_banked_from_ppid_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_regular_from_ppid_quant
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_regular_negpart_from_ppid_quant
#print axioms paper2_theorem_1_1_general_chi_bformSq_of_deepest_from_ppid_quant
#print axioms
  paper2_theorem_1_1_general_chi_bformSq_of_deepest_negpart_from_ppid_quant

end AxiomAudit

end ShenWork.Paper2.BFormPositiveDatumLocalSq
