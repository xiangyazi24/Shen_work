import ShenWork.Paper1.WaveStabilityUpgrade
import ShenWork.Paper1.Theorem12CoordinateAudit

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Left-tail bridge for Step 4

The PDE assertion that the canonical solution approaches the left equilibrium
is kept separate.  This file records the exact, elementary bridge from that
assertion to the moving-frame error tail required by `WaveStabilityUpgrade`.
-/

def UniformCoMovingLeftEquilibriumConvergence
    (c : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ R T : ℝ, ∀ t z : ℝ,
    T ≤ t → z ≤ -R → |coMovingPath c u t z - 1| < ε

theorem uniformMovingFrameLeftTailConvergence_of_leftEquilibrium
    {c : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu : UniformCoMovingLeftEquilibriumConvergence c u)
    (hU : Tendsto U atBot (𝓝 1)) :
    UniformMovingFrameLeftTailConvergence 0 (coMovingPath c u) U := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hu (ε / 2) hε2 with ⟨Ru, T, hu⟩
  have hUev : ∀ᶠ z in atBot, |U z - 1| < ε / 2 := by
    have hball : Metric.ball (1 : ℝ) (ε / 2) ∈ 𝓝 (1 : ℝ) :=
      Metric.ball_mem_nhds _ hε2
    have hev := hU hball
    filter_upwards [hev] with z hz
    simpa [Metric.mem_ball, Real.dist_eq] using hz
  rcases eventually_atBot.1 hUev with ⟨A, hA⟩
  refine ⟨max Ru (-A), T, ?_⟩
  intro t z ht hz
  have hz0 : z ≤ -max Ru (-A) := by simpa using hz
  have hzRu : z ≤ -Ru := by
    exact hz0.trans (neg_le_neg (le_max_left Ru (-A)))
  have hcut : -(max Ru (-A)) ≤ A := by
    have h := neg_le_neg (le_max_right Ru (-A))
    simpa using h
  have hzA : z ≤ A := hz0.trans hcut
  have hu' := hu t z ht hzRu
  have hU' := hA z hzA
  have htriangle :
      |coMovingPath c u t z - U z| ≤
        |coMovingPath c u t z - 1| + |U z - 1| := by
    calc
      |coMovingPath c u t z - U z| =
          |(coMovingPath c u t z - 1) + (1 - U z)| := by
            congr 1
            ring
      _ ≤ |coMovingPath c u t z - 1| + |1 - U z| :=
        abs_add_le _ _
      _ = |coMovingPath c u t z - 1| + |U z - 1| := by
        rw [abs_sub_comm 1 (U z)]
  have hfinal : |coMovingPath c u t z - U z| < ε := by
    calc
      |coMovingPath c u t z - U z| ≤
          |coMovingPath c u t z - 1| + |U z - 1| := htriangle
      _ < ε / 2 + ε / 2 := add_lt_add hu' hU'
      _ = ε := by ring
  simpa [movingFrameError] using hfinal

end ShenWork.Paper1

#print axioms ShenWork.Paper1.uniformMovingFrameLeftTailConvergence_of_leftEquilibrium
