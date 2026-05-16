/-
  ShenWork/PDE/ODEExistence.lean

  ODE existence for the logistic equation via Picard-Lindelöf.
-/
import ShenWork.Defs
import ShenWork.PDE.SuperSolution
import Mathlib.Analysis.ODE.PicardLindelof

open MeasureTheory Filter Topology Real Set Metric
open scoped NNReal

noncomputable section

/-- Local existence of the logistic ODE solution via Picard-Lindelöf. -/
theorem logistic_ode_local_existence (α : ℝ) (hα : 1 ≤ α) (M : ℝ) (hM : 0 < M) :
    ∃ T > 0, ∃ ū : ℝ → ℝ, ū 0 = M ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt ū (ū t * (1 - (ū t) ^ α)) (Set.Icc 0 T) t := by
  let g : ℝ → ℝ := fun u => u * (1 - u ^ α)
  let f : ℝ → ℝ → ℝ := fun _ u => g u
  let a : ℝ≥0 := ⟨M + 1, by linarith [hM]⟩
  let L : ℝ≥0 :=
    ⟨max (1 : ℝ) ((2 * M + 1) * (1 + (2 * M + 1) ^ α)), by
      exact (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)⟩
  let K : ℝ≥0 := 1
  let T : ℝ := (M + 1) / (L : ℝ)
  have hLpos : 0 < (L : ℝ) := by
    dsimp [L]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT : 0 < T := div_pos (by linarith [hM]) hLpos
  refine ⟨T, hT, ?_⟩
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, ⟨le_refl _, le_of_lt hT⟩⟩
  have htime :
      (L : ℝ) * max (T - (t₀ : ℝ)) ((t₀ : ℝ) - (0 : ℝ)) ≤ (a : ℝ) - (0 : ℝ) := by
    dsimp [T, t₀, a]; simp only [sub_zero, sub_self]
    rw [max_eq_left (le_of_lt (div_pos (by linarith [hM]) hLpos))]
    rw [show (L : ℝ) * ((M + 1) / (L : ℝ)) = M + 1 from by field_simp [hLpos.ne']]
  have hb : ∀ x ∈ closedBall M (a : ℝ), ‖g x‖ ≤ (L : ℝ) := by
    sorry -- |g(x)| ≤ L on closedBall M (M+1), i.e., for |x-M| ≤ M+1
  have hl : LipschitzOnWith K g (closedBall M (a : ℝ)) := by
    sorry -- g is Lipschitz on bounded set
  have hf : IsPicardLindelof f t₀ M a (0 : ℝ≥0) L K := by
    sorry -- assemble IsPicardLindelof from hb, hl, htime
  obtain ⟨ū, hū0, hūderiv⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf
  exact ⟨ū, by simpa [t₀] using hū0, fun t ht => by simpa [f, g] using hūderiv t ht⟩

end
