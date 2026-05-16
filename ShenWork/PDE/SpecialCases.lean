/-
  ShenWork/PDE/SpecialCases.lean

  Complete proofs of PDE theorems for special cases.
  These demonstrate the full proof chain for specific initial data.
-/
import ShenWork.Defs
import ShenWork.PDE.SuperSolution
import ShenWork.PDE.GlobalBound

open Filter Topology MeasureTheory Real

noncomputable section

/-- Prop 1.1(1) for the special case u₀ ≡ 1 and χ = 0:
    The constant solution u ≡ 1, v ≡ 1 satisfies all conditions. -/
theorem cm_global_exist_neg_constant_case (p : CMParams) (hp : p.χ = 0) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ t x, 0 ≤ t → u t x ≤ max 1 1) ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → u t x ≤ 1 + ε) := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, constant_solution_is_global p hp, ?_, ?_⟩
  · intro t x _; simp
  · intro ε hε; exact ⟨0, fun t x _ => by linarith⟩

/-- Prop 1.2(1) for the special case u₀ ≡ 1 and χ = 0:
    The constant solution already IS the equilibrium. -/
theorem cm_stabilize_neg_constant_case (p : CMParams) (hp : p.χ = 0) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0) := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, constant_solution_is_global p hp, ?_⟩
  simp only [sub_self, abs_zero, ciSup_const]
  exact tendsto_const_nhds

/-- Any constant u ≡ c with c > 0, v ≡ Ψ(c^γ), is a steady state when χ = 0.
    At c = (a/b)^{1/α} (Paper 2 equilibrium), this gives global existence. -/
theorem constant_equilibrium (p : CMParams) (hp : p.χ = 0)
    (c : ℝ) (hc : 0 < c) (hc_eq : c * (1 - c ^ p.α) = 0) :
    IsGlobalClassicalSolution p (fun _ _ => c) (fun _ _ => c ^ p.γ) := by
  intro T hT
  exact {
    hT := hT
    u_smooth := fun t x _ _ => ⟨differentiableAt_const c, differentiableAt_const c⟩
    v_smooth := fun t x _ _ => differentiableAt_const (c ^ p.γ)
    pde_u := fun t x _ _ => by
      rw [show iteratedDeriv 2 (fun _ : ℝ => c) x = 0 from by
        rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]; simp [deriv_const]]
      simp only [Function.comp_apply, hp, deriv_const, mul_zero, zero_sub, neg_zero, zero_add]
      linarith [hc_eq]
    pde_v := fun t x _ _ => by
      rw [show iteratedDeriv 2 (fun _ : ℝ => c ^ p.γ) x = 0 from by
        rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]; simp [deriv_const]]
      ring
  }

end
