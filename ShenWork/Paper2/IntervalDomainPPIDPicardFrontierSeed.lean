/-
  ShenWork/Paper2/IntervalDomainPPIDPicardFrontierSeed.lean

  PPID seed local existence from the Picard restart frontier, using the
  per-datum positive floor carried by `PaperPositiveInitialDatum`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDPicardFrontierTheorem11

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.QuantFromThreshold

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

private lemma exists_supBound_ppid
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := hu₀.admissible.1
  refine ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have hx_mem : |u₀ x| ∈ Set.range (fun y : intervalDomain.Point => |u₀ y|) :=
    ⟨x, rfl⟩
  exact (hM₀ hx_mem).trans (le_max_left _ _)

/-- The Picard restart frontier gives per-datum PPID seed local existence:
each PPID datum has its own positive lower floor, so it belongs to one
threshold class. -/
theorem localExistencePPID_of_picardFrontier
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨M, hM, hbound⟩ := exists_supBound_ppid hu₀
  obtain ⟨c, hc, hfloor⟩ := hu₀.floor
  obtain ⟨δ, hδ, hfactory⟩ :=
    ThresholdQuantBridge.thresholdQuantitativeLocalExistence_of_picardFrontier
      p hα_ge hγ_ge_one hPF M c hM hc
  obtain ⟨u, v, hsol, htrace⟩ :=
    hfactory u₀ hu₀.toPositive hbound hfloor
  exact ⟨δ, hδ, u, v, hsol, htrace⟩

/-- PPID-typed conditional Theorem 1.1 bridge from Picard restart frontier and
classical min-persistence.  The PPID seed local-existence input from Task241 is
discharged internally using the datum's own positive floor. -/
theorem theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPersist : ClassicalMinPersistence p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence_seed
    p hχ ha hb hα_ge hγ_ge_one hPF hPersist
    (localExistencePPID_of_picardFrontier p hα_ge hγ_ge_one hPF)

#print axioms localExistencePPID_of_picardFrontier
#print axioms theorem_1_1_intervalDomain_of_ppid_picardFrontier_persistence

end ShenWork.Paper2.PPIDThresholdReachability
