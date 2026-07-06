/-
  Phase C: unconditional `ClassicalMinPersistence` for `χ₀ ≤ 0`.

  The endpoint chemotaxis-divergence factor/limit bounds are proved in
  `IntervalDomainBoundaryChemDivLimit`.  This file gives the direct named
  consumer needed by the threshold anti-Zeno route, then applies it to the
  PPID Picard-frontier Theorem 1.1 bridge.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainBoundaryChemDivLimit
import ShenWork.Paper2.IntervalDomainPPIDPicardFrontierSeed

open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **`ClassicalMinPersistence` for the interval domain when `χ₀ ≤ 0`.** -/
theorem classicalMinPersistence_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ) :
    QuantFromThreshold.ClassicalMinPersistence p :=
  ShenWork.Paper2.BFormPositiveDatumLocal.classicalMinPersistence_of_boundary_window_regime
    p hχ ha hb hγ_ge_one
    (ShenWork.Paper2.BFormPositiveDatumLocal.boundaryMinPersistenceWindowBound_chiNonpos
      p hχ ha hb)

/-- Strict-negative specialization of `classicalMinPersistence_chiNonpos`. -/
theorem classicalMinPersistence_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ) :
    QuantFromThreshold.ClassicalMinPersistence p :=
  classicalMinPersistence_chiNonpos p (le_of_lt hχ) ha hb hγ_ge_one

#print axioms classicalMinPersistence_chiNonpos
#print axioms classicalMinPersistence_chiNeg

end ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID-typed Theorem 1.1 bridge for `χ₀ ≤ 0`, with min-persistence discharged.

The remaining construction input is the canonical Picard restart frontier. -/
theorem theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence
    p hχ ha hb hα_ge hγ_ge_one hPF
    (ShenWork.MinPersistenceAtoms.classicalMinPersistence_chiNonpos
      p hχ ha hb hγ_ge_one)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hPF

#print axioms theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNeg

end ShenWork.Paper2.PPIDThresholdReachability
