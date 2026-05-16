/-
  ShenWork/PDE/MildSolution.lean

  Mild solution framework for the chemotaxis system.

  A mild solution of u_t = Δu + F(u) with u(0) = u₀ is a function satisfying
  the Duhamel integral equation:
    u(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} F(u(s)) ds

  For short time T, the map Φ(u)(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} F(u(s)) ds
  is a contraction on a suitable function space, giving local existence
  via Banach fixed-point theorem.
-/
import ShenWork.PDE.HeatSemigroup
import ShenWork.Defs
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory Filter Topology Real

noncomputable section

/-! ## The nonlinear term F(u) for the chemotaxis system -/

/-- The nonlinear source term F(u,v) = -χ(u^m v_x)_x + u(1-u^α).
    For the local existence proof, we treat the full right-hand side
    including the chemotaxis term. For χ ≤ 0, the chemotaxis term
    has good sign properties. -/
def chemotaxisSource (p : CMParams) (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  u x * (1 - (u x) ^ p.α)

/-! ## Mild solution operator -/

/-- The Duhamel / mild solution operator:
    Φ(u)(t,x) = (e^{tΔ} u₀)(x) + ∫₀ᵗ (e^{(t-s)Δ} F(u(s)))(x) ds -/
def mildSolutionOperator (p : CMParams) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) (x : ℝ) : ℝ :=
  heatSemigroup t u₀ x +
  ∫ s in Set.Icc 0 t, heatSemigroup (t - s) (fun y => chemotaxisSource p (u s) (fun _ => 0) y) x

/-! ## Key estimate: the source term is Lipschitz in u -/

/-- For bounded u, the logistic term u(1-u^α) is Lipschitz in u.
    This is the key for the contraction property. -/
lemma logistic_lipschitz_on_bounded {α M : ℝ} (hα : 1 ≤ α) (hM : 0 < M) :
    ∃ L > 0, ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
    |u₁ * (1 - u₁ ^ α) - u₂ * (1 - u₂ ^ α)| ≤ L * |u₁ - u₂| := by
  sorry

/-! ## Local existence via contraction -/

/-- For sufficiently small T > 0, the mild solution operator Φ is a contraction
    on the space of bounded continuous functions [0,T] → C^b(ℝ). -/
theorem mild_solution_operator_contracting (p : CMParams)
    (u₀ : ℝ → ℝ) (hu₀_bdd : IsBddFun u₀) :
    ∃ T > 0, ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧
    ∀ u₁ u₂ : ℝ → ℝ → ℝ,
    (∀ t x, |u₁ t x| ≤ 2 * (sSup (Set.range (fun x => |u₀ x|)))) →
    (∀ t x, |u₂ t x| ≤ 2 * (sSup (Set.range (fun x => |u₀ x|)))) →
    ∀ t x, 0 ≤ t → t ≤ T →
    |mildSolutionOperator p u₀ u₁ t x - mildSolutionOperator p u₀ u₂ t x| ≤
      K * (sSup (Set.range (fun s => sSup (Set.range (fun y => |u₁ s y - u₂ s y|))))) := by
  sorry

/-- Local existence of mild solutions via Banach fixed-point theorem. -/
theorem local_existence_mild (p : CMParams)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ T > 0, ∃ u : ℝ → ℝ → ℝ,
    (∀ t x, 0 ≤ t → t ≤ T → u t x =
      heatSemigroup t u₀ x +
      ∫ s in Set.Icc 0 t, heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u s) (fun _ => 0) y) x) := by
  sorry

end
