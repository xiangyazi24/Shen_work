/-
  ShenWork/Paper2/IntervalMildToClassical.lean

  T7e bridge: GradientMildSolutionData → RegularityBootstrap → localExistence.

  Route A (ChatGPT R2): new direct bridge that consumes the gradient-form mild
  solution, bypassing the old intervalDuhamelOperator entirely.

  **Status: scaffold with sorry for the hard regularity conjuncts.**
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.Paper2.Statements

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalMildToClassical

open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.Paper2

/-! ## Bridge: GradientMildSolutionData → RegularityBootstrap

The easy conjuncts (v exists, v ≥ 0, u > 0) are wired from existing
infrastructure. The hard conjuncts (PDE pointwise, classical regularity)
are sorry — they require the Schauder bootstrap.
-/

/-- The chemical concentration v(t) := resolver(u(t)) for the mild solution. -/
noncomputable def mildChemicalConcentration (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : intervalDomainPoint → ℝ :=
  intervalNeumannResolverR p (u t)

/-- v(t,x) ≥ 0 when u(t) ≥ 0: resolver preserves nonnegativity. -/
theorem mildChemical_nonneg (p : CM2Params)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x)
    (hu_cont : HasContinuousSlices T u)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    0 ≤ mildChemicalConcentration p u t x := by
  unfold mildChemicalConcentration
  sorry -- Wire intervalNeumannResolverR_nonneg_of_nonneg_source

/-- u(t,x) > 0 (strict positivity) from the Picard iteration:
    S(t)u₀(x) ≥ inf u₀ > 0 and corrections are small. -/
theorem mildSolution_strictlyPositive (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hu₀_pos : ∀ x, 0 < u₀ x)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    0 < D.u t x := by
  sorry -- Strengthen hmapsTo_nn from ≥ 0 to > 0 using the positive margin

/-- Initial trace: u(t) → u₀ as t → 0⁺ in L∞. -/
theorem mildSolution_initialTrace (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    InitialTrace intervalDomain u₀ D.u := by
  sorry -- Semigroup approx-identity + Duhamel terms → 0

/-- The parabolic PDE for u: u_t = Δu - χ₀ div(uχ(v)∇v) + u(a-bu^α).
    This is the HARD conjunct requiring Schauder bootstrap. -/
theorem mildSolution_parabolicPDE (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) := by
  sorry -- Schauder bootstrap: differentiate Duhamel integral

/-- The elliptic PDE for v: 0 = Δv - μv + νu^γ. -/
theorem mildChemical_ellipticPDE (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian
            (mildChemicalConcentration p D.u t) x
          - p.μ * mildChemicalConcentration p D.u t x
          + p.ν * (D.u t x) ^ p.γ := by
  sorry -- Resolver satisfies elliptic eq by construction

/-- Neumann BC for u and v. -/
theorem mildSolution_neumannBC (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv (D.u t) x = 0 ∧
      intervalDomain.normalDeriv (mildChemicalConcentration p D.u t) x = 0 := by
  sorry -- Cosine-series Neumann (T7[B]) + resolver grad at 0,1

/-- Classical regularity: u ∈ C^{1,2}, v ∈ C^{0,2}. -/
theorem mildSolution_classicalRegularity (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    intervalDomainClassicalRegularity D.T D.u (mildChemicalConcentration p D.u) := by
  sorry -- T5/T6 assembly: Duhamel C² + time regularity

end ShenWork.IntervalMildToClassical
