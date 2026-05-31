/-
  ShenWork/Paper2/IntervalGradientDuhamelMap.lean

  T7 existence — Atom E/F foundation: the **weak divergence-form mild map** `Φ`
  and the genuine **`IntervalMildSolution`** predicate (the weak Duhamel
  equation `u = Φ u` on `(0,T]`).

  The route's mild map is the gradient-Duhamel (divergence) form — `∂ₓ` lives on
  the semigroup `S(t−s)`, NOT on the source — so it consumes only the C⁰ flux
  `Q = u·∂ₓR/(1+R)^β` (not its divergence `chemDiv`):

      Φ(u₀,u)(t,x) = S(t)u₀(x)
        − χ₀ ∫₀ᵗ ∂ₓ[S(t−s) Q(u(s))](x) ds
        + ∫₀ᵗ S(t−s) L(u(s))(x) ds

  where `S = intervalFullSemigroupOperator`, `Q(w) = lift w · resolverGradReal w
  / (1+R w)^β`, `L(w) = lift(logistic w)`, `R w = intervalNeumannResolverR p w`.
  The analytic bounds this map satisfies are exactly Atom D (`∫∂ₓS`, `∫S`),
  glue1 (`Q` sup-Lipschitz), glue2 (the contraction), Atom C (`L` Lipschitz);
  positivity `R ≥ 0` is O1.

  This file only DEFINES the map and the predicate (a real weak-Duhamel
  equation, not a shell).  The fixed-point assembly (MapsTo + ContractingWith +
  `ContractingWith.exists_fixedPoint'` on the weighted mild ball) is Atom E/F.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.PDE.IntervalChemFluxLipschitz
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.PDE (intervalNeumannResolverR)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)

noncomputable section

namespace ShenWork.IntervalGradientDuhamelMap

open ShenWork.Paper2 (resolverGradReal)

/-- The lifted chemotaxis flux `Q(w)(y) = lift w(y)·∂ₓR(w)(y)/(1+R(w)(y))^β`
(`∂ₓR = resolverGradReal`, `R(w) = intervalNeumannResolverR`).  A C⁰ object on the
weak ball (no `chemDiv` / second derivative). -/
def chemFluxLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun y => intervalDomainLift w y * resolverGradReal p w y
    / (1 + intervalDomainLift (intervalNeumannResolverR p w) y) ^ p.β

/-- The lifted logistic source `L(w) = lift(w·(a − b·w^α))`. -/
def logisticLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  intervalDomainLift (intervalLogisticSource p w)

/-- **The weak divergence-form mild map.**  `Φ(u₀,u)(t,x) = S(t)u₀(x) −
χ₀∫₀ᵗ∂ₓS(t−s)Q(u(s))(x)ds + ∫₀ᵗS(t−s)L(u(s))(x)ds`.  The chemotaxis term puts
`∂ₓ` on the semigroup (divergence form), so it integrates the C⁰ flux `Q`. -/
def intervalGradientDuhamelMap (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
    + (-p.χ₀) * (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x.1)
    + ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1

/-- **The weak mild-solution predicate** — the genuine weak Duhamel equation
`u(t) = Φ(u₀,u)(t)` at every interior time `t ∈ (0,T]` and every point.  This is a
real proposition (the fixed-point equation), NOT a shell: a weak mild solution is
exactly a fixed point of `Φ`. -/
def IntervalMildSolution (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    u t x = intervalGradientDuhamelMap p u₀ u t x

end ShenWork.IntervalGradientDuhamelMap
