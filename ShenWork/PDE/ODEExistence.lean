/-
  ShenWork/PDE/ODEExistence.lean

  ODE existence for the logistic equation via Picard-Lindelöf.
-/
import ShenWork.Defs
import ShenWork.PDE.SuperSolution
import Mathlib.Analysis.ODE.PicardLindelof

open MeasureTheory Filter Topology Real Set

noncomputable section

/-- The logistic vector field f(t, u) = u*(1-u^α) is time-independent. -/
def logisticField (α : ℝ) : ℝ → ℝ → ℝ := fun _ u => logisticRHS α u

/-- The logistic field is continuous in u (since rpow is continuous for u > 0). -/
lemma logisticField_continuous_u (α : ℝ) (hα : 0 < α) :
    ∀ t : ℝ, Continuous (logisticField α t) := by
  intro t
  unfold logisticField logisticRHS
  sorry

/-- Local existence of the logistic ODE solution on [0, T] via Picard-Lindelöf.
    For any M > 0, there exists T > 0 and a solution ū : [0,T] → ℝ with ū(0) = M. -/
theorem logistic_ode_local_existence (α : ℝ) (hα : 1 ≤ α) (M : ℝ) (hM : 0 < M) :
    ∃ T > 0, ∃ ū : ℝ → ℝ, ū 0 = M ∧
    ∀ t ∈ Icc (0:ℝ) T, HasDerivWithinAt ū (logisticRHS α (ū t)) (Icc 0 T) t := by
  sorry

end
