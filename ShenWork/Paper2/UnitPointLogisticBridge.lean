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

end ShenWork.Paper2

end
