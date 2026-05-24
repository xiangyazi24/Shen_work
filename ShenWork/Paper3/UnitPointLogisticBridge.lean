/-
  Bridge: closes Paper3 Proposition_1_3 + Proposition_1_2 unconditionally
  on unit-point-domain via Slot F's Bernoulli-logistic solution.
-/
import ShenWork.Paper3.Statements
import ShenWork.Paper2.UnitPointLogisticBridge
import ShenWork.PDE.UnitPointLogisticODE

noncomputable section

namespace ShenWork.Paper3

/-- Paper 3 Proposition 1.3 holds unconditionally on the unit-point
domain.  Hypothesis `0 < p.a, 0 < p.b, 1 ≤ p.m, StrongLogisticCondition`
forces the Bernoulli branch; we route through Slot F. -/
theorem unitPointDomain.Proposition_1_3_holds
    (p : CM2Params) (C : ShenWork.Paper2.Paper2Constants p) :
    Proposition_1_3 ShenWork.Paper2.unitPointDomain p C := by
  intro ha hb _hm _hcond u₀ hu₀
  rcases ShenWork.Paper2.unitPointLogistic_globalExistence_with_attractor
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound, _hlim⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨max (ShenWork.Paper2.unitPointDomain.supNorm u₀)
    ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.2 holds for the unit-point domain in the
`0 < p.a ∧ 0 < p.b` slice. -/
theorem unitPointDomain.Proposition_1_2_when_a_pos_b_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    Proposition_1_2 ShenWork.Paper2.unitPointDomain p := by
  intro _hχ _hm u₀ hu₀
  rcases ShenWork.Paper2.unitPointLogistic_globalExistence_with_attractor
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound, _hlim⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨max (ShenWork.Paper2.unitPointDomain.supNorm u₀)
    ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.4 for the `0 < p.a ∧ 0 < p.b` slice (a subcase
of the `(0 ≤ a ∧ 0 < b)` disjunctive branch).  Routes through Slot F. -/
theorem unitPointDomain.Proposition_1_4_when_a_pos_b_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p := by
  intro _hm _hβ _hor _hχ u₀ hu₀
  rcases ShenWork.Paper2.unitPointLogistic_globalExistence_with_attractor
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound, _hlim⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨max (ShenWork.Paper2.unitPointDomain.supNorm u₀)
    ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.4 for the disjunction `(a=0 ∧ b=0) ∨ (0 < a ∧ 0 < b)`.
Covers two of three cases of the full hypothesis disjunction; the
`(a=0 ∧ 0 < b)` case requires a separate ODE bridge. -/
theorem unitPointDomain.Proposition_1_4_when_a_b_split
    (p : CM2Params)
    (hsplit : (p.a = 0 ∧ p.b = 0) ∨ (0 < p.a ∧ 0 < p.b)) :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p := by
  rcases hsplit with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact unitPointDomain.Proposition_1_4_minimal_only p ha hb
  · exact unitPointDomain.Proposition_1_4_when_a_pos_b_pos p ha hb

end ShenWork.Paper3

end
