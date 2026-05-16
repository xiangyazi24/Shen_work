/-
  ShenWork/PDE/ODEExistence.lean
  ODE existence for the logistic equation via Picard-Lindelöf.
-/
import ShenWork.Defs
import ShenWork.PDE.SuperSolution
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set Metric
open scoped NNReal

noncomputable section

theorem logistic_ode_local_existence (α : ℝ) (_hα : 1 ≤ α) (M : ℝ) (hM : 0 < M) :
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
  have hT : 0 < T := by dsimp [T]; exact div_pos (by linarith [hM]) hLpos
  refine ⟨T, hT, ?_⟩
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, ⟨le_refl _, le_of_lt hT⟩⟩
  have htime :
      (L : ℝ) * max (T - (t₀ : ℝ)) ((t₀ : ℝ) - (0 : ℝ)) ≤ (a : ℝ) - (0 : ℝ) := by
    have hTnonneg : 0 ≤ (M + 1) / (L : ℝ) := le_of_lt (div_pos (by linarith [hM]) hLpos)
    dsimp [T, t₀, a]; simp only [sub_zero, sub_self]
    rw [max_eq_left hTnonneg]
    exact le_of_eq (mul_div_cancel₀ _ (ne_of_gt hLpos))
  have hb : ∀ x ∈ Metric.closedBall M (a : ℝ), ‖g x‖ ≤ (L : ℝ) := by
    intro x _hx; sorry
  have hl : LipschitzOnWith K g (Metric.closedBall M (a : ℝ)) := by sorry
  have hf : IsPicardLindelof f t₀ M a (0 : ℝ≥0) L K := by
    simpa [f] using
      (IsPicardLindelof.of_time_independent (f := g) (t₀ := t₀) (x₀ := M) (a := a)
        (r := (0 : ℝ≥0)) (L := L) (K := K) hb hl htime)
  obtain ⟨ū, hū0, hūderiv⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf
  refine ⟨ū, ?_, ?_⟩
  · simpa [t₀] using hū0
  · intro t ht; simpa [f, g] using hūderiv t ht

end
