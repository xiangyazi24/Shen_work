/-
  Paper 2 Theorem 1.1 for **χ₀ = 0**, threshold route, reduced to the SINGLE
  unified residual `PicardLimitRestartFrontier` (hPLF).

  With `ClassicalMinPersistence` now proved (`classicalMinPersistence_chiZero`),
  the threshold-route reduction `paper2_theorem_1_1_chiZero_of_picardFrontier_hlocal`
  needs only `hPF` (PicardRestartFrontier) + `hlocal` (per-datum local existence).
  Both are derivable from the single Picard-limit restart frontier `hPLF`:
    * `hPF`     = `picardRestartFrontier_of_picardLimitFrontier hPLF`;
    * `hlocal`  = bound the datum, then `quantitativeLocalExistence_chiZero hPLF`.

  Hence χ₀ = 0 Theorem 1.1 reduces — via the MinPersistence-discharged threshold
  route — to exactly `hPLF`, the same S-construction residual that closes the
  cone route.  This is the cleanest statement of the χ₀ = 0 frontier.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiZeroThreshold
import ShenWork.Paper2.IntervalDomainConeQuantBridge

open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.Paper2.ThresholdQuantBridge
  Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.ThresholdQuantBridge

/-- **Theorem 1.1 (χ₀ = 0), threshold route, reduced to `PicardLimitRestartFrontier`
alone** (MinPersistence + hQuant-min-principle + hPF + hlocal all discharged). -/
theorem paper2_theorem_1_1_chiZero_of_picardLimitFrontier
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p) :
    Theorem_1_1 intervalDomain p := by
  -- The threshold-route Picard restart frontier from the unified frontier.
  have hPF : PicardRestartFrontier p :=
    ConeQuantBridge.picardRestartFrontier_of_picardLimitFrontier hPLF
  -- Per-datum local existence from the χ₀ = 0 quantitative local existence.
  have hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
    intro u₀ hu₀
    obtain ⟨B, hB⟩ := hu₀.admissible.1
    set M := max B 1 with hMdef
    have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right B 1)
    have hbound : ∀ x, |u₀ x| ≤ M := fun x =>
      le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)
    obtain ⟨δ, hδ, hex⟩ :=
      ConeQuantBridge.quantitativeLocalExistence_chiZero p hχ0 hα_ge hPLF M hM
    obtain ⟨u, v, hsol, htr⟩ := hex hu₀ hbound
    exact ⟨δ, hδ, u, v, hsol, htr⟩
  exact paper2_theorem_1_1_chiZero_of_picardFrontier_hlocal
    p hχ0 ha hb hα_ge hγ_ge_one hPF hlocal

end ShenWork.Paper2.ThresholdQuantBridge
