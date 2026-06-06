/-
  Paper 2 Theorem 1.1 for **χ₀ = 0**, threshold route, reduced to the explicit
  `LimitRegularityInputs` ledger ALONE.

  The unified frontier `hPLF` (`PicardLimitRestartFrontier`) is itself produced
  from the named ledger `H` (`∀ u₀ PID, ∀ D, LimitRegularityInputs p u₀ D`) via
  the proved packaging `restartData_of_inputs` + `frontierCore_of_inputs`.  So,
  composing with the MinPersistence-discharged threshold-route capstone
  `paper2_theorem_1_1_chiZero_of_picardLimitFrontier`, χ₀ = 0 Theorem 1.1 reduces
  — entirely through the threshold route — to exactly the five genuine analytic
  residuals carried by `LimitRegularityInputs`:
    `hpde_u`, `Hu`, `Hvsrc`, `HsupNorm`, `Hvpos`.

  Everything else along this route is now PROVED and axiom-clean: the Picard
  threshold contraction `δ(M, c)`, the quantitative strong minimum principle
  (`classicalMinPersistence_chiZero`), the overlap uniqueness, hPCW, the
  restart-and-glue machinery, the per-datum local existence, and the
  initial-approach correction.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiZeroFrontier
import ShenWork.Paper2.IntervalDomainMildLocalChi0

open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.Paper2.ThresholdQuantBridge
  ShenWork.IntervalMildPicard Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.ThresholdQuantBridge

/-- **Theorem 1.1 (χ₀ = 0), threshold route, reduced to the `LimitRegularityInputs`
ledger alone** — the cleanest statement of the χ₀ = 0 frontier through the
MinPersistence-discharged Q-line. -/
theorem paper2_theorem_1_1_chiZero_threshold_of_ledger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        MildLocalChi0.LimitRegularityInputs p u₀ D) :
    Theorem_1_1 intervalDomain p := by
  have hPLF : ConeQuantBridge.PicardLimitRestartFrontier p := by
    intro u₀ hu₀ D _hDu
    exact ⟨MildLocalChi0.restartData_of_inputs hχ0 (H u₀ hu₀ D),
      MildLocalChi0.frontierCore_of_inputs hχ0 (H u₀ hu₀ D)⟩
  exact paper2_theorem_1_1_chiZero_of_picardLimitFrontier
    p hχ0 ha hb hα_ge hγ_ge_one hPLF

end ShenWork.Paper2.ThresholdQuantBridge
