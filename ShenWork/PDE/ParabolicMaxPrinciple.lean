/-
  ShenWork/PDE/ParabolicMaxPrinciple.lean

  Classical parabolic comparison principle for 1D reaction-diffusion equations.
  Used to prove that solutions of the chemotaxis system are bounded by
  the rectangle ODE barriers (ComparisonPrinciple.lean).

  Mathematical reference: Evans "Partial Differential Equations" Ch.7,
  Protter-Weinberger "Maximum Principles in Differential Equations".
-/
import ShenWork.Defs

open Filter Topology Real

noncomputable section

/-! ## Classical parabolic comparison principle

For a reaction-diffusion equation u_t = u_xx + f(u,x,t) on ℝ × (0,T),
if ū is a supersolution (ū_t ≥ ū_xx + f(ū,x,t)) and u(0,x) ≤ ū(0) for all x,
then u(t,x) ≤ ū(t) for all t > 0, x ∈ ℝ.

The proof uses the exponential barrier trick:
Let w = u - ū. Then w_t - w_xx ≤ L*w (from Lipschitz of f).
Let w̃ = w * exp(-λt). Then w̃_t - w̃_xx ≤ (L-λ)*w̃.
For λ > L, the coefficient is negative, so w̃ cannot attain a positive maximum
in the interior — contradiction with first crossing.
-/

/-- A spatially homogeneous supersolution: ū'(t) ≥ f(ū(t)) for all t. -/
structure IsSpatiallyHomogeneousSuperSolution (f : ℝ → ℝ) (ū : ℝ → ℝ) : Prop where
  deriv_bound : ∀ t, 0 < t → HasDerivAt ū (f (ū t)) t ∨
    (∃ d, HasDerivAt ū d t ∧ d ≥ f (ū t))

/-- The parabolic comparison principle: if u solves u_t = u_xx + f(u) and
    ū is a spatially homogeneous supersolution with u(0,x) ≤ ū(0),
    then u(t,x) ≤ ū(t) for all t > 0. -/
theorem parabolic_comparison_upper
    (f : ℝ → ℝ) (L : ℝ) (hL : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (u : ℝ → ℝ → ℝ) (ū : ℝ → ℝ)
    (hu_pde : ∀ t x, 0 < t → deriv (u · x) t = iteratedDeriv 2 (u t) x + f (u t x))
    (hū_super : ∀ t, 0 < t → ∃ d, HasDerivAt ū d t ∧ d ≥ f (ū t))
    (h_init : ∀ x, u 0 x ≤ ū 0)
    (hu_bdd : ∃ M, ∀ t x, |u t x| ≤ M) :
    ∀ t x, 0 ≤ t → u t x ≤ ū t := by
  sorry

/-- Similarly for subsolutions. -/
theorem parabolic_comparison_lower
    (f : ℝ → ℝ) (L : ℝ) (hL : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (u : ℝ → ℝ → ℝ) (u_bar : ℝ → ℝ)
    (hu_pde : ∀ t x, 0 < t → deriv (u · x) t = iteratedDeriv 2 (u t) x + f (u t x))
    (hu_bar_sub : ∀ t, 0 < t → ∃ d, HasDerivAt u_bar d t ∧ d ≤ f (u_bar t))
    (h_init : ∀ x, u_bar 0 ≤ u 0 x)
    (hu_bdd : ∃ M, ∀ t x, |u t x| ≤ M) :
    ∀ t x, 0 ≤ t → u_bar t ≤ u t x := by
  sorry

end
