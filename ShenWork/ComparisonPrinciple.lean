/-
  ShenWork/ComparisonPrinciple.lean
  Comparison principles for the chemotaxis system.
-/
import ShenWork.Defs
import ShenWork.PDE.ParabolicMaxPrinciple

open Filter Topology

noncomputable section

structure RectangleODESolution (p : CMParams) where
  ū : ℝ → ℝ
  u_bar : ℝ → ℝ
  ū_pos : ∀ t, 0 ≤ t → 0 < ū t
  u_bar_pos : ∀ t, 0 ≤ t → 0 < u_bar t
  ordering : ∀ t, 0 ≤ t → u_bar t < ū t
  ū_lim : Tendsto ū atTop (𝓝 1)
  u_bar_lim : Tendsto u_bar atTop (𝓝 1)

lemma ode_ū_decreasing (p : CMParams) (hp : p.χ ≤ 0)
    (ū u_bar : ℝ) (hū : 1 < ū) (hu_bar_pos : 0 < u_bar) (hu_bar_lt : u_bar < ū) :
    p.χ * ū ^ p.m * (ū ^ p.γ - u_bar ^ p.γ) + ū * (1 - ū ^ p.α) < 0 := by
  have hū_pos : 0 < ū := by linarith
  have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le one_pos p.hγ
  have h_first_nonpos : p.χ * ū ^ p.m * (ū ^ p.γ - u_bar ^ p.γ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hp (Real.rpow_nonneg (le_of_lt hū_pos) p.m))
      (sub_nonneg.mpr (Real.rpow_le_rpow (le_of_lt hu_bar_pos) (le_of_lt hu_bar_lt) (le_of_lt hγ_pos)))
  have h_second_neg : ū * (1 - ū ^ p.α) < 0 :=
    mul_neg_of_pos_of_neg hū_pos (sub_neg.mpr (Real.one_lt_rpow hū hα_pos))
  linarith

lemma ode_u_bar_increasing (p : CMParams) (hp : p.χ ≤ 0)
    (ū u_bar : ℝ) (hū : 1 < ū) (hu_bar_pos : 0 < u_bar) (hu_bar_lt : u_bar < 1) :
    0 < p.χ * u_bar ^ p.m * (u_bar ^ p.γ - ū ^ p.γ) + u_bar * (1 - u_bar ^ p.α) := by
  have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le one_pos p.hγ
  have h_first_nonneg : 0 ≤ p.χ * u_bar ^ p.m * (u_bar ^ p.γ - ū ^ p.γ) := by
    have h1 : p.χ * u_bar ^ p.m ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hp (Real.rpow_nonneg (le_of_lt hu_bar_pos) p.m)
    have h2 : u_bar ^ p.γ - ū ^ p.γ ≤ 0 :=
      sub_nonpos.mpr (Real.rpow_le_rpow (le_of_lt hu_bar_pos) (le_of_lt (lt_trans hu_bar_lt hū)) (le_of_lt hγ_pos))
    exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  have h_second_pos : 0 < u_bar * (1 - u_bar ^ p.α) :=
    mul_pos hu_bar_pos (sub_pos.mpr (Real.rpow_lt_one (le_of_lt hu_bar_pos) hu_bar_lt hα_pos))
  linarith

theorem rectangle_ode_converges (p : CMParams) (_hp : p.χ ≤ 0)
    (M₀ : ℝ) (hM₀ : 1 < M₀) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ sol : RectangleODESolution p, sol.ū 0 = M₀ ∧ sol.u_bar 0 = δ₀ := by
  have hMpos : 0 < M₀ - 1 := sub_pos.mpr hM₀
  have hδcoef_pos : 0 < 1 - δ₀ := sub_pos.mpr hδ₀_lt
  have hExpLim : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
  refine ⟨⟨fun t => 1 + (M₀ - 1) * Real.exp (-t),
           fun t => 1 - (1 - δ₀) * Real.exp (-t), ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro t _; linarith [mul_pos hMpos (Real.exp_pos (-t))]
  · intro t ht
    have : (1 - δ₀) * Real.exp (-t) ≤ 1 - δ₀ :=
      mul_le_of_le_one_right hδcoef_pos.le (Real.exp_le_one_iff.mpr (by linarith))
    linarith
  · intro t _; linarith [mul_pos hMpos (Real.exp_pos (-t)),
      mul_pos hδcoef_pos (Real.exp_pos (-t))]
  · show Tendsto (fun t => 1 + (M₀ - 1) * Real.exp (-t)) atTop (𝓝 1)
    have h := hExpLim.const_mul (M₀ - 1)
    simp only [mul_zero] at h
    have := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop) |>.add h
    simpa [add_zero] using this
  · show Tendsto (fun t => 1 - (1 - δ₀) * Real.exp (-t)) atTop (𝓝 1)
    have h := hExpLim.const_mul (1 - δ₀)
    simp only [mul_zero] at h
    have := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop) |>.sub h
    simpa [sub_zero] using this
  · simp [Real.exp_zero]
  · simp [Real.exp_zero]

theorem pde_bounded_by_rectangle_ode_statement_false :
    ¬ (∀ (p : CMParams), p.χ ≤ 0 →
      ∀ u v : ℝ → ℝ → ℝ,
        IsGlobalClassicalSolution p u v →
        ∀ sol : RectangleODESolution p,
          ∀ t x, 0 ≤ t → sol.u_bar t ≤ u t x ∧ u t x ≤ sol.ū t) := by
  intro h
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hp : p.χ ≤ 0 := by norm_num [p]
  have hExpLim : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
  let sol : RectangleODESolution p :=
    { ū := fun t => 1 + 2 * Real.exp (-t)
      u_bar := fun t => 1 + Real.exp (-t)
      ū_pos := by
        intro t _ht
        positivity
      u_bar_pos := by
        intro t _ht
        positivity
      ordering := by
        intro t _ht
        have hpos : 0 < Real.exp (-t) := Real.exp_pos _
        linarith
      ū_lim := by
        have h := hExpLim.const_mul 2
        simp only [mul_zero] at h
        simpa [add_zero] using
          (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add h
      u_bar_lim := by
        simpa [add_zero] using
          (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add hExpLim }
  have hglobal : IsGlobalClassicalSolution p (fun _ _ => 1) (fun _ _ => 1) :=
    constant_solution_is_global p
  have hbound :=
    h p hp (fun _ _ => 1) (fun _ _ => 1) hglobal sol 0 0 (by norm_num)
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa [sol, Real.exp_zero] using hbound.1
  norm_num at hbad

theorem pde_bounded_by_rectangle_ode (p : CMParams) (hp : p.χ ≤ 0)
    (u v : ℝ → ℝ → ℝ) (hglobal : IsGlobalClassicalSolution p u v)
    (sol : RectangleODESolution p) :
    ∀ t x, 0 ≤ t → sol.u_bar t ≤ u t x ∧ u t x ≤ sol.ū t := by
  sorry

end
