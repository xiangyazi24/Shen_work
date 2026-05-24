/-
  Bridge: closes Theorem_1_3 + (partial) Theorem_1_2 unconditionally on
  unit-point-domain by inlining the explicit Bernoulli-logistic solution.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.UnitPointLogisticODE

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

end ShenWork.Paper2

end
