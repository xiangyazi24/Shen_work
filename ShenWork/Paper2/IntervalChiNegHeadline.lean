import ShenWork.Paper2.IntervalChiNegDirectClassical
import ShenWork.Paper2.IntervalTruncatedEnergyProducer
import ShenWork.Paper2.IntervalTruncatedStrictPositivityProducer
import ShenWork.Paper2.IntervalUniformTruncatedMapCertificateDatum
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional

/-!
# Unconditional chi-negative and chi-nonpositive headlines

This is the final producer wiring: the faithful truncated map certificate,
negative-part energy, and matched-divergence Jensen producer feed the direct
classical closure.  The nonpositive headline then splits between this
strict-negative result and the existing unconditional zero-sensitivity branch.
-/

open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (UniformTruncatedConjugateMapCertificateData
   uniformTruncatedConjugateMapCertificateData_producer)
open ShenWork.Paper2.IntervalTruncatedEnergyProducer
  (uniformTruncatedEnergyData_producer)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegAssembly

/-- The three independently verified faithful producers in their common
assembly record. -/
def uniformTruncatedAssemblyInputs_producer
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    UniformTruncatedAssemblyInputs p := by
  let Hmap : UniformTruncatedConjugateMapCertificateData p :=
    uniformTruncatedConjugateMapCertificateData_producer hα hγ
  refine
    { mapCertificate := Hmap
      energy := ?_
      jensenStrictPos := ?_ }
  · exact uniformTruncatedEnergyData_producer p
  · exact uniformTruncatedJensenStrictPosData_producer p Hmap

/-- Fully produced strict-negative interval-domain Theorem 1.1. -/
theorem paper2_chiNeg_unconditional
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  paper2_chiNeg p hχ ha hb hα hγ
    (uniformTruncatedAssemblyInputs_producer p hα hγ)

/-- Fully produced nonpositive-sensitivity interval-domain Theorem 1.1. -/
theorem paper2_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p := by
  rcases lt_or_eq_of_le hχ with hneg | hzero
  · exact paper2_chiNeg_unconditional p hneg ha hb hα hγ
  · exact ShenWork.Paper2.intervalDomain_theorem_1_1_chiZero_unconditional
      p hzero ha hb hα hγ

#print axioms uniformTruncatedAssemblyInputs_producer
#print axioms paper2_chiNeg_unconditional
#print axioms paper2_chiNonpos

end ShenWork.Paper2.IntervalChiNegAssembly
