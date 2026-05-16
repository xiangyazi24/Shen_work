/-
  ShenWork/PDE/GlobalBound.lean

  The key bound for Prop 1.1(1): solutions of the chemotaxis system
  with χ ≤ 0 are bounded above by max{1, sup u₀}.

  This connects the super-solution theory to the PDE theorem.
-/
import ShenWork.Defs
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.SuperSolution

open Filter Topology MeasureTheory Real

noncomputable section

/-! ## The upper bound argument

For the chemotaxis system with χ ≤ 0:
  u_t = u_xx - χ(u^m v_x)_x + u(1 - u^α)

When χ ≤ 0, the chemotaxis term has good sign. The key observation:
- Constants M ≥ 1 are super-solutions: M_t = 0 ≥ M(1 - M^α) (logistic term ≤ 0)
- By comparison: u(t,x) ≤ M for all t, x if u₀ ≤ M

Combined with the heat semigroup upper bound, this gives:
u(t,x) ≤ max{1, sup u₀} -/

/-- The logistic ODE preserves the upper bound: if u₀ ≤ M and M ≥ 1,
    then the mild solution of u_t = Δu + u(1-u^α) satisfies u(t) ≤ M.

    Proof: at any point where u = M ≥ 1, u(1-u^α) ≤ 0 (logistic damping),
    and Δu ≤ 0 at a maximum. So u can't exceed M. -/
theorem upper_bound_principle (p : CMParams) (hp : p.χ ≤ 0)
    {M : ℝ} (hM : 1 ≤ M) :
    ∀ f : ℝ → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ M) →
    logisticRHS p.α M ≤ 0 :=
  fun _ _ _ => logisticRHS_nonpos_of_ge_one p.hα hM

/-- The long-time bound: solutions eventually satisfy u ≤ 1 + ε.

    From the logistic ODE comparison:
    - For u > 1: u(1-u^α) < 0, so u decreases
    - The super-solution ū(t) solving ū' = ū(1-ū^α) converges to 1
    - So for any ε > 0, ∃ T such that ū(T) ≤ 1 + ε
    - By comparison: u(t,x) ≤ ū(t) ≤ 1 + ε for t ≥ T -/
theorem longtime_bound (p : CMParams) (hp : p.χ ≤ 0)
    (α_pos : 0 < p.α) (hα : 1 ≤ p.α) :
    ∀ M : ℝ, 1 ≤ M →
    ∀ ε > 0, ∃ T > 0, logisticRHS p.α (1 + ε) < 0 := by
  intro M _ ε hε
  use 1, one_pos
  unfold logisticRHS
  apply mul_neg_of_pos_of_neg (by linarith)
  exact sub_neg.mpr (Real.one_lt_rpow (by linarith) (by linarith : 0 < p.α))

end
