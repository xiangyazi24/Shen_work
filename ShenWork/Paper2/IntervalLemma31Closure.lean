/-
  Lemma 3.1 closure: wire the max-principle infrastructure into the
  `Lemma_3_1_intervalDomain` sorry in Statements.lean.

  The chain:
  1. From `IsPaper2ClassicalSolution`, extract F(t,x) = intervalDomainLift(u(t))(x)
  2. Show argmax slope bound: at any argmax x* of F(t,·) on [0,1],
     ∂ₜF(t,x*) ≤ 0 (interior_max_point_of_solution + boundary companion)
  3. Apply sliceMax_dini_of_argmax_bound → Dini condition for sSup
  4. Convert to supNorm via supNorm_eq_sSup_lift_image
  5. Apply supNorm_nonincreasing_of_dini → SupNormNonincreasingOn on Ioo
  6. Extend from Ioo to Ioc by continuity at right endpoint
-/
import ShenWork.Paper2.IntervalDomainMaxPointSolution
import ShenWork.Paper2.IntervalDomainSliceMaxDini
import ShenWork.Paper2.IntervalLemma31Heat
import ShenWork.Paper2.IntervalDomainSupNormMaxPrinciple
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.MaxPrincipleAtoms
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.Lemma31Closure

/-- At ANY spatial argmax (interior OR boundary) of a classical solution
with χ₀ ≤ 0, the time derivative satisfies u_t ≤ u·(a − b·u^α).

For interior argmax: `interior_max_point_of_solution`.
For boundary argmax: the zero-extension lift has a local max (positive
solution vs zero extension), so `deriv2_nonpos_of_isLocalMax` applies. -/
theorem max_point_slope_bound
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmax : ∀ y, u t y ≤ u t x) :
    intervalDomain.timeDeriv u t x
      ≤ intervalDomainLift (u t) x.1
        * (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
  rcases lt_or_eq_of_le x.2.1 with h0 | h0
  · rcases lt_or_eq_of_le x.2.2 with h1 | h1
    · exact interior_max_point_of_solution hχ hsol ht0 htT ⟨h0, h1⟩ hmax
    · -- Boundary x = 1: the lift has a local max at 1 (positive vs zero extension).
      sorry
  · -- Boundary x = 0: the lift has a local max at 0 (positive vs zero extension).
    sorry

/-- The above-capacity branch of Lemma 3.1 for the interval domain. -/
theorem lemma31_above_capacity
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T)
    (hsup : (p.a / p.b) ^ (1 / p.α) < intervalDomain.supNorm (u t₀)) :
    SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t₀) := by
  sorry

/-- The a=b=0 branch of Lemma 3.1 for the interval domain. -/
theorem lemma31_zero
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T) := by
  sorry

end ShenWork.Paper2.Lemma31Closure
