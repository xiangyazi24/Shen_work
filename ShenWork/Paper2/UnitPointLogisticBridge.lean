/-
  Bridge: closes Theorem_1_3 unconditionally on unit-point-domain by
  inlining the explicit Bernoulli-logistic solution.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.UnitPointLogisticODE

noncomputable section

namespace ShenWork.Paper2

/-- Paper 2 Theorem 1.3 holds unconditionally on the unit-point domain.
The hypothesis `0 < p.a, 0 < p.b` forces the Bernoulli branch; we route
through `unitPointLogistic_globalExistence_with_attractor`. -/
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
    -- IsPaper2Bounded asks ∀ᶠ t in atTop, supNorm ≤ M
    -- atTop on ℝ means eventually large t.  hbound covers t ≥ 0, so OK.
    refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
    exact hbound t ht

end ShenWork.Paper2

end
