import ShenWork.Paper2.Statements
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace ShenWork.Paper2

open Filter Set
open scoped Topology

/-- Exponential weight in the Bernoulli reduction for `u' = u(a - b u^α)`. -/
def bernoulliLogisticWeight (p : CM2Params) (t : ℝ) : ℝ :=
  Real.exp (-(p.α * p.a) * t)

/-- Denominator for the forward-time Bernoulli formula. -/
def bernoulliLogisticDenominator (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  p.b / p.a + (u₀ ^ (-p.α) - p.b / p.a) * bernoulliLogisticWeight p t

/-- Forward-time Bernoulli formula for the scalar logistic ODE. -/
def bernoulliLogisticForward (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  (bernoulliLogisticDenominator p u₀ t) ^ (-1 / p.α)

/-- The derivative prescribed by the logistic vector field at the initial value. -/
def bernoulliLogisticInitialDerivative (p : CM2Params) (u₀ : ℝ) : ℝ :=
  u₀ * (p.a - p.b * u₀ ^ p.α)

/-- A globally differentiable extension of the Bernoulli formula.

For `0 ≤ t` this is the exact Bernoulli solution.  For `t < 0` it uses the
positive exponential arc with the same value and first derivative at `t = 0`;
the Paper 2 unit-point construction only uses the forward-time ODE identity. -/
def bernoulliLogisticSolution (p : CM2Params) (u₀ t : ℝ) : ℝ :=
  if 0 ≤ t then
    bernoulliLogisticForward p u₀ t
  else
    u₀ * Real.exp ((p.a - p.b * u₀ ^ p.α) * t)

@[simp] lemma bernoulliLogisticWeight_zero (p : CM2Params) :
    bernoulliLogisticWeight p 0 = 1 := by
  simp [bernoulliLogisticWeight]

@[simp] lemma bernoulliLogisticDenominator_zero
    (p : CM2Params) (u₀ : ℝ) :
    bernoulliLogisticDenominator p u₀ 0 = u₀ ^ (-p.α) := by
  simp [bernoulliLogisticDenominator, bernoulliLogisticWeight]

@[simp] lemma bernoulliLogisticSolution_of_nonneg
    (p : CM2Params) (u₀ t : ℝ) (ht : 0 ≤ t) :
    bernoulliLogisticSolution p u₀ t = bernoulliLogisticForward p u₀ t := by
  simp [bernoulliLogisticSolution, ht]

@[simp] lemma bernoulliLogisticSolution_of_neg
    (p : CM2Params) (u₀ t : ℝ) (ht : t < 0) :
    bernoulliLogisticSolution p u₀ t =
      u₀ * Real.exp ((p.a - p.b * u₀ ^ p.α) * t) := by
  simp [bernoulliLogisticSolution, not_le.mpr ht]

end ShenWork.Paper2
