import ShenWork.Paper2.IntervalChiNegV6DirectClassical
import ShenWork.Paper2.IntervalTruncatedEnergyProducerV6
import ShenWork.Paper2.IntervalTruncatedStrictPositivityProducerV6
import ShenWork.Paper2.IntervalUniformTruncatedMapCertificateDatum
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional

/-!
# Unconditional chi-negative and chi-nonpositive V6 headlines

This is the final producer wiring: the faithful truncated map certificate,
negative-part energy, and matched-divergence Jensen producer feed the direct
classical V6 closure.  The nonpositive headline then splits between this
strict-negative result and the existing unconditional zero-sensitivity branch.
-/

open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (UniformTruncatedConjugateMapCertificateData
   uniformTruncatedConjugateMapCertificateData_producer)
open ShenWork.Paper2.IntervalTruncatedEnergyProducerV6
  (uniformTruncatedEnergyDataV6_producer)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegV6Assembly

/-- The three independently verified faithful V6 producers in their common
assembly record. -/
def uniformTruncatedV6AssemblyInputs_producer
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    UniformTruncatedV6AssemblyInputs p := by
  let Hmap : UniformTruncatedConjugateMapCertificateData p :=
    uniformTruncatedConjugateMapCertificateData_producer hα hγ
  refine
    { mapCertificate := Hmap
      energy := ?_
      jensenStrictPos := ?_ }
  · exact uniformTruncatedEnergyDataV6_producer p
  · exact uniformTruncatedJensenStrictPosDataV6_producer p Hmap

/-- Fully produced strict-negative interval-domain Theorem 1.1. -/
theorem paper2_chiNeg_v6_unconditional
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  paper2_chiNeg_v6 p hχ ha hb hα hγ
    (uniformTruncatedV6AssemblyInputs_producer p hα hγ)

/-- Fully produced nonpositive-sensitivity interval-domain Theorem 1.1. -/
theorem paper2_chiNonpos_v6
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p := by
  rcases lt_or_eq_of_le hχ with hneg | hzero
  · exact paper2_chiNeg_v6_unconditional p hneg ha hb hα hγ
  · exact ShenWork.Paper2.intervalDomain_theorem_1_1_chiZero_unconditional
      p hzero ha hb hα hγ

#print axioms uniformTruncatedV6AssemblyInputs_producer
#print axioms paper2_chiNeg_v6_unconditional
#print axioms paper2_chiNonpos_v6

end ShenWork.Paper2.IntervalChiNegV6Assembly
