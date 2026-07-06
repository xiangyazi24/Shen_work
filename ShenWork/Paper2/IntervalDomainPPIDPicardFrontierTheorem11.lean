/-
  ShenWork/Paper2/IntervalDomainPPIDPicardFrontierTheorem11.lean

  PPID-typed Theorem 1.1 bridge with the threshold-local hypothesis lowered to
  the existing Picard restart frontier interface.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDThresholdTheorem11
import ShenWork.Paper2.IntervalDomainThresholdQuantBridge

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.QuantFromThreshold

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID-typed conditional Theorem 1.1 bridge from Picard restart frontier,
classical min-persistence, and per-datum PPID seed local existence.

This lowers the Task240 threshold-local input using the already proved
`ThresholdQuantBridge.thresholdQuantitativeLocalExistence_of_picardFrontier`. -/
theorem theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence_seed
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : ClassicalMinPersistence p)
    (hlocalPPID : ∀ u₀ : intervalDomain.Point → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_threshold_persistence_seed
    p hχ ha hb hγ_ge_one
    (ThresholdQuantBridge.thresholdQuantitativeLocalExistence_of_picardFrontier
      p hα_ge hγ_ge_one hPF)
    hPersist hlocalPPID

#print axioms theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence_seed

end ShenWork.Paper2.PPIDThresholdReachability
