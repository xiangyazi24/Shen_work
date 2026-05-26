/-
  Bridge: closes Theorem_1_3 + (partial) Theorem_1_2 unconditionally on
  unit-point-domain by inlining the explicit Bernoulli-logistic solution.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.UnitPointLogisticODE
import ShenWork.PDE.UnitPointDecayODE

noncomputable section

namespace ShenWork.Paper2

/-- Paper 2 Theorem 1.3 holds unconditionally on the unit-point domain.
The hypothesis `0 < p.a, 0 < p.b` forces the Bernoulli branch. -/
theorem unitPointDomain.Theorem_1_3_holds
    (p : CM2Params) (C : Paper2Constants p) :
    Theorem_1_3 unitPointDomain p C := by
  intro ha hb _hm _hcond
  refine ⟨?_, ?_⟩
  · intro u₀ hu₀
    rcases unitPointLogistic_globalExistence_with_attractor p ha hb u₀ hu₀ with
      ⟨u, v, hglobal, htrace, hbound, _hlim⟩
    refine ⟨1, by norm_num, u, v, ?_, htrace, ?_⟩
    · exact hglobal.classical (T := 1) (by norm_num)
    · refine ⟨max (unitPointDomain.supNorm u₀)
        ((p.a / p.b) ^ (1 / p.α)), ?_⟩
      intro t ht_pos _ht_lt
      exact hbound t ht_pos.le
  · intro _hm_one u₀ hu₀
    rcases unitPointLogistic_globalExistence_with_attractor p ha hb u₀ hu₀ with
      ⟨u, v, hglobal, htrace, hbound, _hlim⟩
    refine ⟨u, v, hglobal, htrace, ?_⟩
    refine ⟨max (unitPointDomain.supNorm u₀)
      ((p.a / p.b) ^ (1 / p.α)), ?_⟩
    refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
    exact hbound t ht

/-- Paper 2 Theorem 1.2 partial: the `0 < p.a ∧ 0 < p.b` slice routed
through the Bernoulli logistic solution.  For `a = 0 ∧ b = 0`, use
`Theorem_1_2_minimal_only` in Statements.lean. -/
theorem unitPointDomain.Theorem_1_2_when_a_pos_b_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    Theorem_1_2 unitPointDomain p := by
  intro _ha_nn _hb_nn _hβ
  refine ⟨?_, ?_⟩
  · intro _hm_pos _hm_lt u₀ hu₀
    rcases unitPointLogistic_globalExistence_with_attractor p ha hb u₀ hu₀ with
      ⟨u, v, hglobal, htrace, hbound, _hlim⟩
    refine ⟨1, by norm_num, u, v, ?_, htrace, ?_⟩
    · exact hglobal.classical (T := 1) (by norm_num)
    · refine ⟨max (unitPointDomain.supNorm u₀)
        ((p.a / p.b) ^ (1 / p.α)), ?_⟩
      intro t ht_pos _ht_lt
      exact hbound t ht_pos.le
  · intro _hm_eq _hχ u₀ hu₀
    rcases unitPointLogistic_globalExistence_with_attractor p ha hb u₀ hu₀ with
      ⟨u, v, hglobal, htrace, hbound, _hlim⟩
    refine ⟨u, v, hglobal, htrace, ?_⟩
    refine ⟨max (unitPointDomain.supNorm u₀)
      ((p.a / p.b) ^ (1 / p.α)), ?_⟩
    refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
    exact hbound t ht

/-- Paper 2 Theorem 1.2 for the disjunction `(a = 0, b = 0) ∨ (0 < a, 0 < b)`.
Combines `Theorem_1_2_minimal_only` (in Statements.lean) with the
Bernoulli-logistic bridge. -/
theorem unitPointDomain.Theorem_1_2_when_a_b_split
    (p : CM2Params)
    (hsplit : (p.a = 0 ∧ p.b = 0) ∨ (0 < p.a ∧ 0 < p.b)) :
    Theorem_1_2 unitPointDomain p := by
  rcases hsplit with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact unitPointDomain.Theorem_1_2_minimal_only p ha hb
  · exact unitPointDomain.Theorem_1_2_when_a_pos_b_pos p ha hb

/-- Paper 2 Theorem 1.2 for the (a = 0, 0 < b) slice, routed through the
explicit Bernoulli decay solution `u' = -b u^(α+1)`. -/
theorem unitPointDomain.Theorem_1_2_when_a_zero_b_pos
    (p : CM2Params) (ha : p.a = 0) (hb : 0 < p.b) :
    Theorem_1_2 unitPointDomain p := by
  intro _ha_nn _hb_nn _hβ
  refine ⟨?_, ?_⟩
  · intro _hm_pos _hm_lt u₀ hu₀
    rcases unitPointDecay_globalExistence_with_bound p ha hb u₀ hu₀ with
      ⟨u, v, hglobal, htrace, hbound⟩
    refine ⟨1, by norm_num, u, v, ?_, htrace, ?_⟩
    · exact hglobal.classical (T := 1) (by norm_num)
    · refine ⟨unitPointDomain.supNorm u₀, ?_⟩
      intro t ht_pos _ht_lt
      exact hbound t ht_pos.le
  · intro _hm_eq _hχ u₀ hu₀
    rcases unitPointDecay_globalExistence_with_bound p ha hb u₀ hu₀ with
      ⟨u, v, hglobal, htrace, hbound⟩
    refine ⟨u, v, hglobal, htrace, ?_⟩
    refine ⟨unitPointDomain.supNorm u₀, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
    exact hbound t ht

/-- The Slot F logistic package realises `UnitPointLogisticNonminimalPackage`
unconditionally on the unit-point domain. -/
theorem unitPointDomain.UnitPointLogisticNonminimalPackage_holds
    (p : CM2Params) : UnitPointLogisticNonminimalPackage p := by
  intro ha hb u₀ hu₀
  exact unitPointLogistic_globalExistence_with_attractor p ha hb u₀ hu₀

/-- Paper 2 Theorem 1.1 holds **unconditionally** on the unit-point domain.
The two disjoint slices of the hypothesis split into:
- `(0 < a, 0 < b)`: Slot F Bernoulli-logistic bridge
- `(a = 0, b = 0)`: `Theorem_1_1_minimal_only`
The negation-of-hypothesis slices `(0 < a, b = 0)` and `(a = 0, 0 < b)`
are vacuous via the disjunct hypotheses. -/
theorem Theorem_1_1_unitPointDomain_holds
    (p : CM2Params) :
    Theorem_1_1 unitPointDomain p :=
  unitPointDomain.Theorem_1_1_from_logistic_nonminimal p
    (unitPointDomain.UnitPointLogisticNonminimalPackage_holds p)

/-- Paper 2 Theorem 1.2 unconditional on the unit-point domain
**excluding** the slice `a > 0 ∧ b = 0` (which makes the unit-point ODE
`u' = au` unbounded — a genuine restriction on the unit-point instance).
Covers `(a = 0, b ≥ 0)` and `(0 < a, 0 < b)`. -/
theorem unitPointDomain.Theorem_1_2_when_not_a_pos_b_zero
    (p : CM2Params)
    (hnot : ¬ (0 < p.a ∧ p.b = 0)) :
    Theorem_1_2 unitPointDomain p := by
  -- Three subcases: (a = 0, b = 0), (a = 0, b > 0), (a > 0, b > 0).
  -- The negation `¬ (a > 0 ∧ b = 0)` forces one of these.
  by_cases ha_pos : 0 < p.a
  · have hb_ne : p.b ≠ 0 := fun hb0 => hnot ⟨ha_pos, hb0⟩
    intro ha_nn hb_nn hβ
    -- Need 0 < p.b; derive from `0 ≤ b ∧ b ≠ 0`.
    have hb_pos : 0 < p.b := lt_of_le_of_ne hb_nn (Ne.symm hb_ne)
    exact unitPointDomain.Theorem_1_2_when_a_pos_b_pos p ha_pos hb_pos
      ha_nn hb_nn hβ
  · -- a = 0.
    intro ha_nn _hb_nn _hβ
    have ha_zero : p.a = 0 := le_antisymm (not_lt.mp ha_pos) ha_nn
    by_cases hb_pos : 0 < p.b
    · exact unitPointDomain.Theorem_1_2_when_a_zero_b_pos p ha_zero hb_pos
        ha_nn _hb_nn _hβ
    · have hb_zero : p.b = 0 := le_antisymm (not_lt.mp hb_pos) _hb_nn
      exact unitPointDomain.Theorem_1_2_minimal_only p ha_zero hb_zero
        ha_nn _hb_nn _hβ

/-! ### Refutation: Theorem 1.2 fails on unitPointDomain when a > 0, b = 0

On the unit-point domain with `b = 0`, the PDE reduces to `u' = a u`, whose
positive solutions grow exponentially.  This contradicts the `IsPaper2Bounded`
conclusion of Theorem 1.2 (second branch, `m = 1`).  The refutation proves
that the 3-of-4 parameter coverage is tight: the `a > 0, b = 0` slice is a
genuine mathematical obstruction, not a gap in the proof. -/

/-- Concrete CM2Params witnessing the a > 0, b = 0 failure of Theorem 1.2
on the unit-point domain.  Parameters: a = 1, b = 0, m = 1, χ₀ = 0, β = 1,
giving `chiBeta p = 1 > 0 = χ₀`. -/
def theorem12RefutationParams : CM2Params where
  N := 1;  hN := by norm_num
  α := 1;  hα := by norm_num
  γ := 1;  hγ := by norm_num
  m := 1;  hm := by norm_num
  μ := 1;  hμ := by norm_num
  ν := 1;  hν := by norm_num
  χ₀ := 0
  a := 1;  ha := by norm_num
  b := 0;  hb := by norm_num
  β := 1;  hβ := by norm_num

/-- Theorem 1.2 is FALSE on unitPointDomain for `a > 0, b = 0`.

The unit-point PDE with `a = 1, b = 0` is `f' = f` (exponential growth).
Any positive classical solution satisfies `f(t) ≥ f(1) · t` for `t ≥ 1`,
contradicting eventual boundedness. -/
theorem not_Theorem_1_2_unitPointDomain_when_a_pos_b_zero :
    ∃ p : CM2Params, 0 < p.a ∧ p.b = 0 ∧ ¬ Theorem_1_2 unitPointDomain p := by
  refine ⟨theorem12RefutationParams, by norm_num [theorem12RefutationParams],
    by norm_num [theorem12RefutationParams], ?_⟩
  intro h12
  -- Discharge Theorem_1_2 hypotheses: 0 ≤ a, 0 ≤ b, 1 ≤ β
  have hbranch := h12 (by norm_num [theorem12RefutationParams])
    (by norm_num [theorem12RefutationParams])
    (by norm_num [theorem12RefutationParams])
  -- χ₀ < chiBeta p: 0 < 1
  have hchi : theorem12RefutationParams.χ₀ < chiBeta theorem12RefutationParams := by
    norm_num [theorem12RefutationParams, chiBeta]
  -- Initial datum u₀ = 1
  set u₀ : Unit → ℝ := fun _ => 1 with hu₀_def
  have hu₀ : PositiveInitialDatum unitPointDomain u₀ := by
    exact ⟨trivial, fun _ _ => by norm_num⟩
  -- Apply second branch: m = 1, χ₀ < chiBeta
  obtain ⟨u, v, hglobal, _htrace, hbounded⟩ :=
    hbranch.2 (by norm_num [theorem12RefutationParams] : theorem12RefutationParams.m = 1)
      hchi u₀ hu₀
  -- Set f(t) := u t ()
  set f : ℝ → ℝ := fun t => u t () with hf_def
  -- Extract differentiability from classical regularity (works for any T)
  have hf_diff : Differentiable ℝ f := by
    have hsol1 := hglobal (T := 1) (by norm_num : (0 : ℝ) < 1)
    exact hsol1.regularity.1
  -- Key PDE property: deriv f t = f t for all t > 0
  have hpde : ∀ t : ℝ, 0 < t → deriv f t = f t := by
    intro t ht
    -- Choose T := t + 1 > t > 0
    have hsol := hglobal (T := t + 1) (by linarith)
    have hpde_raw := hsol.2.2.2.2.1 t () ht (by linarith : t < t + 1) (Set.mem_univ ())
    -- On unitPointDomain: timeDeriv = deriv, laplacian = 0, chemotaxisDiv = 0
    simp only [unitPointDomain] at hpde_raw
    -- The PDE is: deriv f t = 0 - 0 * 0 + f t * (a - b * (f t)^α)
    -- With a=1, b=0, α=1: deriv f t = f t * (1 - 0) = f t
    simp only [theorem12RefutationParams] at hpde_raw
    linarith
  -- Positivity: f t > 0 for all t > 0
  have hf_pos : ∀ t : ℝ, 0 < t → 0 < f t := by
    intro t ht
    have hsol := hglobal (T := t + 1) (by linarith)
    exact hsol.2.2.1 t () ht (by linarith : t < t + 1)
  -- Specific value: f 1 > 0
  have hf1_pos : 0 < f 1 := hf_pos 1 one_pos
  -- Monotonicity on [1, ∞): deriv f t > 0 on (1, ∞)
  have hf_mono : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact hf_diff.continuous.continuousOn
    · exact hf_diff.differentiableOn
    · intro x hx
      rw [interior_Ici] at hx
      have hx_gt : 1 < x := Set.mem_Ioi.mp hx
      have hx_pos : 0 < x := by linarith
      rw [hpde x hx_pos]
      exact le_of_lt (hf_pos x hx_pos)
  -- Lower bound on derivative: for x > 1, f x ≥ f 1, so deriv f x ≥ f 1
  have hderiv_lb : ∀ x : ℝ, x ∈ interior (Set.Ici (1 : ℝ)) → f 1 ≤ deriv f x := by
    intro x hx
    rw [interior_Ici] at hx
    have hx_gt : 1 < x := Set.mem_Ioi.mp hx
    rw [hpde x (by linarith)]
    exact hf_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hx_gt)) (le_of_lt hx_gt)
  -- Linear growth: f t - f 1 ≥ f(1) * (t - 1) for t ≥ 1
  have hgrowth : ∀ t : ℝ, 1 ≤ t → f 1 * (t - 1) ≤ f t - f 1 := by
    intro t ht
    exact (convex_Ici 1).mul_sub_le_image_sub_of_le_deriv
      hf_diff.continuous.continuousOn hf_diff.differentiableOn hderiv_lb
      1 (Set.mem_Ici.mpr le_rfl) t (Set.mem_Ici.mpr ht) ht
  -- From IsPaper2Bounded: ∃ M, ∀ᶠ t in atTop, |f t| ≤ M
  obtain ⟨M, hM⟩ := hbounded
  rw [Filter.eventually_atTop] at hM
  obtain ⟨T₀, hT₀⟩ := hM
  -- Pick t* = max T₀ 1 + M / f(1) + 1
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg (f (max T₀ 1))) (hT₀ (max T₀ 1) (le_max_left _ _))
  have hMdf_nn : 0 ≤ M / f 1 := div_nonneg hM_nn (le_of_lt hf1_pos)
  set tstar := max T₀ 1 + M / f 1 + 1 with htstar_def
  have htstar_ge_T₀ : T₀ ≤ tstar :=
    le_trans (le_max_left T₀ 1) (by linarith)
  have htstar_ge_1 : 1 ≤ tstar :=
    le_trans (le_max_right T₀ 1) (by linarith)
  -- From boundedness at tstar
  have habs_le : |f tstar| ≤ M := hT₀ tstar htstar_ge_T₀
  have hf_tstar_pos : 0 < f tstar := hf_pos tstar (by linarith)
  have hf_le_M : f tstar ≤ M := by rwa [abs_of_pos hf_tstar_pos] at habs_le
  -- From growth: f tstar ≥ f 1 + f 1 * (tstar - 1) = f 1 * tstar
  have hgrowth_tstar := hgrowth tstar htstar_ge_1
  -- f 1 * tstar > M
  have hf1_ne : f 1 ≠ 0 := ne_of_gt hf1_pos
  have hM_recover : f 1 * (M / f 1) = M := mul_div_cancel₀ M hf1_ne
  have hmax_nn : 0 ≤ max T₀ (1 : ℝ) := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  -- f 1 * tstar = f 1 * max T₀ 1 + M + f 1
  have hexpand : f 1 * tstar = f 1 * max T₀ 1 + M + f 1 := by
    rw [htstar_def, mul_add, mul_add, hM_recover]
    ring
  -- So f tstar ≥ f 1 * tstar > M (using f 1 * max T₀ 1 ≥ 0 and f 1 > 0)
  linarith [mul_nonneg (le_of_lt hf1_pos) hmax_nn]

end ShenWork.Paper2

end
