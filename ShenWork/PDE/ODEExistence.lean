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
  let K : ℝ≥0 := ⟨1 + (1 + α) * (2 * M + 1) ^ α, by positivity⟩
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
    intro x hx
    show ‖x * (1 - x ^ α)‖ ≤ (L : ℝ)
    have hx_dist : dist x M ≤ M + 1 := Metric.mem_closedBall.mp hx
    have hx_abs : |x| ≤ 2 * M + 1 := by
      rw [Real.dist_eq] at hx_dist
      exact abs_le.mpr ⟨by linarith [abs_le.mp hx_dist |>.1],
                         by linarith [abs_le.mp hx_dist |>.2]⟩
    have hα_nn : (0 : ℝ) ≤ α := le_trans zero_le_one _hα
    have h2M1_nn : (0 : ℝ) ≤ 2 * M + 1 := by linarith
    have h_abs_rpow : |x ^ α| ≤ (2 * M + 1) ^ α :=
      (Real.abs_rpow_le_abs_rpow x α).trans (Real.rpow_le_rpow (abs_nonneg x) hx_abs hα_nn)
    have h_sub : |1 - x ^ α| ≤ 1 + |x ^ α| := by
      have := norm_sub_le (1 : ℝ) (x ^ α)
      simp only [Real.norm_eq_abs, abs_one] at this; exact this
    rw [Real.norm_eq_abs, abs_mul]
    calc |x| * |1 - x ^ α|
        ≤ (2 * M + 1) * (1 + (2 * M + 1) ^ α) :=
          mul_le_mul hx_abs (h_sub.trans (by linarith [h_abs_rpow]))
            (abs_nonneg _) h2M1_nn
      _ ≤ (L : ℝ) := le_max_right _ _
  have hl : LipschitzOnWith K g (Metric.closedBall M (a : ℝ)) := by
    show LipschitzOnWith ⟨1 + (1 + α) * (2 * M + 1) ^ α, by positivity⟩ g (closedBall M (M + 1))
    have hα0 : 0 ≤ α := le_trans zero_le_one _hα
    have hαp : 1 ≤ α + 1 := by linarith
    have hαp_ne : α + 1 ≠ 0 := by linarith
    have hgeq : g = fun u : ℝ => u - u ^ (α + 1) := by
      funext u; simp only [g]
      by_cases hu : u = 0
      · subst hu; simp [hαp_ne]
      · have hp : u ^ (α + 1) = u ^ α * u := Real.rpow_add_one hu α
        linarith [hp]
    rw [hgeq]
    exact Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => differentiableAt_id.sub
        ((Real.differentiable_rpow_const hαp).differentiableAt))
      (fun x hx => by
        rw [← NNReal.coe_le_coe]
        change ‖deriv (fun u : ℝ => u - u ^ (α + 1)) x‖ ≤
          1 + (1 + α) * (2 * M + 1) ^ α
        have hxabs : |x| ≤ 2 * M + 1 := by
          have hd := Metric.mem_closedBall.mp hx
          rw [Real.dist_eq] at hd
          exact abs_le.mpr ⟨by linarith [abs_le.mp hd |>.1], by linarith [abs_le.mp hd |>.2]⟩
        have hxpow : |x ^ α| ≤ (2 * M + 1) ^ α :=
          (Real.abs_rpow_le_abs_rpow x α).trans (Real.rpow_le_rpow (abs_nonneg x) hxabs hα0)
        have hderiv : deriv (fun u : ℝ => u - u ^ (α + 1)) x = 1 - (α + 1) * x ^ α := by
          have hd : HasDerivAt (fun u : ℝ => u - u ^ (α + 1)) (1 - (α + 1) * x ^ α) x := by
            have h1 : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id x
            have h2 : HasDerivAt (fun u : ℝ => u ^ (α + 1)) ((α + 1) * x ^ α) x := by
              have := Real.hasDerivAt_rpow_const (x := x) (p := α + 1) (Or.inr hαp)
              simp only [show α + 1 - 1 = α from by ring] at this; exact this
            simpa using h1.sub h2
          exact hd.deriv
        rw [hderiv, Real.norm_eq_abs]
        have h_tri := norm_sub_le (1 : ℝ) ((α + 1) * x ^ α)
        simp only [Real.norm_eq_abs, abs_one, abs_mul,
          abs_of_nonneg (by linarith : 0 ≤ α + 1)] at h_tri
        linarith [mul_le_mul_of_nonneg_left hxpow (by linarith : 0 ≤ α + 1)])
      (convex_closedBall M (M + 1))
  have hf : IsPicardLindelof f t₀ M a (0 : ℝ≥0) L K := by
    simpa [f] using
      (IsPicardLindelof.of_time_independent (f := g) (t₀ := t₀) (x₀ := M) (a := a)
        (r := (0 : ℝ≥0)) (L := L) (K := K) hb hl htime)
  obtain ⟨ū, hū0, hūderiv⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf
  refine ⟨ū, ?_, ?_⟩
  · simpa [t₀] using hū0
  · intro t ht; simpa [f, g] using hūderiv t ht

end
