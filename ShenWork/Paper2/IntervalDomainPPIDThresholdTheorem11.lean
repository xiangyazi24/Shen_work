/-
  ShenWork/Paper2/IntervalDomainPPIDThresholdTheorem11.lean

  PPID-typed Theorem 1.1 bridge from threshold local existence, classical
  min-persistence, and per-datum PPID seed local existence.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDThresholdReachability

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.QuantFromThreshold

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- Threshold local existence plus min-persistence and PPID seed local existence
give the PPID quantitative-local input used by the strong-path Theorem 1.1
wrapper.  The uniform horizon is chosen as `1`; the restart count may depend on
the datum, so no all-PPID common floor is required. -/
theorem quantitativeLocalExistence_ppid_of_threshold_persistence_seed
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hThreshold : ThresholdQuantitativeLocalExistence p)
    (hPersist : ClassicalMinPersistence p)
    (hlocalPPID : ∀ u₀ : intervalDomain.Point → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PaperPositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro M _hM
  refine ⟨1, one_pos, ?_⟩
  intro u₀ hu₀ _hbound
  have hreach :=
    reachableArbitrarilyLong_ppid_of_threshold_persistence_seed
      p hχ ha hb hγ_ge_one hThreshold hPersist hlocalPPID hu₀
  obtain ⟨_hT, u, v, hsol, htrace⟩ := hreach 1 one_pos
  exact ⟨u, v, hsol, htrace⟩

/-- PPID-typed conditional Theorem 1.1 bridge from the threshold/min-persistence
route.  This replaces the refuted all-PPID common-floor route with a per-datum
restart construction. -/
theorem theorem_1_1_intervalDomain_of_ppid_threshold_persistence_seed
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hThreshold : ThresholdQuantitativeLocalExistence p)
    (hPersist : ClassicalMinPersistence p)
    (hlocalPPID : ∀ u₀ : intervalDomain.Point → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one hlocalPPID
    (quantitativeLocalExistence_ppid_of_threshold_persistence_seed
      p hχ ha hb hγ_ge_one hThreshold hPersist hlocalPPID)

#print axioms quantitativeLocalExistence_ppid_of_threshold_persistence_seed
#print axioms theorem_1_1_intervalDomain_of_ppid_threshold_persistence_seed

end ShenWork.Paper2.PPIDThresholdReachability
