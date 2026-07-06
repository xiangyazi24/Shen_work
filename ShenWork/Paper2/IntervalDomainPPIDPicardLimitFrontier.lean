/-
  ShenWork/Paper2/IntervalDomainPPIDPicardLimitFrontier.lean

  PPID Theorem 1.1 wrappers that replace the threshold-route restart frontier
  by the unified Picard-limit restart frontier, and then by the per-datum
  spectral frontier.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistChiNonpos
import ShenWork.Paper2.IntervalDomainPicardLimitSpectralFrontier

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced from the threshold-route
`PicardRestartFrontier` residual to the unified `PicardLimitRestartFrontier`
residual. -/
theorem theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hPLF

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, with the unified Picard-limit frontier
discharged by the per-datum spectral frontier package. -/
theorem theorem_1_1_intervalDomain_of_ppid_spectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardLimitRestartFrontier_of_spectralFrontier hPerDatum)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_spectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_spectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_spectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hPerDatum

#print axioms theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNeg
#print axioms theorem_1_1_intervalDomain_of_ppid_spectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_spectralFrontier_chiNeg

end ShenWork.Paper2.PPIDThresholdReachability
