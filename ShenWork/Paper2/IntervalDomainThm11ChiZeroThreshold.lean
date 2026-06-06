/-
  Paper 2 Theorem 1.1 for **χ₀ = 0**, threshold route, with
  `ClassicalMinPersistence` fully discharged.

  `paper2_theorem_1_1_of_picardFrontier_persistence` reduces Theorem 1.1 to
  three inputs: the Picard restart frontier `hPF`, the quantitative minimum
  principle `hPersist`, and per-datum local existence `hlocal`.  At χ₀ = 0 the
  middle input is now PROVED (`classicalMinPersistence_chiZero`), and the
  cross-solution overlap uniqueness `hOverlap` it needs is supplied by the
  regime L²-energy method.  So Theorem 1.1 (χ₀ = 0) reduces to exactly the two
  construction frontiers `hPF` + `hlocal` (the F2/S-construction residuals).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainThresholdQuantBridge
import ShenWork.Paper2.IntervalDomainMinPersistChiZero

open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.Paper2.ThresholdQuantBridge
  Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.ThresholdQuantBridge

/-- **Theorem 1.1 (χ₀ = 0), threshold route, MinPersistence discharged.** -/
theorem paper2_theorem_1_1_chiZero_of_picardFrontier_hlocal
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : PicardRestartFrontier p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p := by
  have hOverlap : GlueExtension.OverlapUniqueForPID p :=
    GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
      (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
        (intervalDomainL2UBoundedDatumUniform_of_bounded
          (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
            (uniformLiftBoundZeroM_of_regime p (le_of_eq hχ0) ha hb))))
  exact paper2_theorem_1_1_of_picardFrontier_persistence
    p (le_of_eq hχ0) ha hb hα_ge hγ_ge_one hPF
    (ShenWork.MinPersistenceAtoms.classicalMinPersistence_chiZero p hχ0 ha hb hOverlap)
    hlocal

end ShenWork.Paper2.ThresholdQuantBridge
