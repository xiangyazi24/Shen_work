import ShenWork.Paper3.IntervalDomainPersistenceLogistic
import ShenWork.Paper2.IntervalDomainChemDivCritical

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

/-- Lower-right Dini lower estimate, written in the same right-neighbourhood
form as the existing Hamilton minimum machinery.

`RightLowerDiniGE z f I` means that the lower right Dini derivative of `z` is
at least `f (z t)` at every `t ∈ I`. -/
def RightLowerDiniGE (z f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∀ r : ℝ, -f (z t) < r →
    ∃ᶠ s in nhdsWithin t (Set.Ioi t),
      (s - t)⁻¹ * (z t - z s) < r

/-- Spatial minimum trajectory of the interval-domain `u` component. -/
def intervalDomainSpatialMin
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  sInf (Set.range (u t))

/-- The Dini comparison shape requested for the logistic branch. -/
def LogisticSpatialMinimumDini
    (p : CM2Params) (Cχ : ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  RightLowerDiniGE (intervalDomainSpatialMin u)
    (fun z => p.a * z - p.b * z ^ (1 + p.α) - Cχ * z ^ p.m)
    (Set.Ioi 0)

/-- The three u-lower fields isolated from
`IntervalDomainLogisticPersistenceInputs`.  This is a named target for the
spatial-minimum Dini plus scalar-comparison frontier. -/
structure IntervalDomainLogisticULowerFields (p : CM2Params) : Prop where
  part1 :
    0 < p.a → 0 < p.b → 1 ≤ p.m →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          ∃ deltaU > 0,
            ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, deltaU ≤ u t x
  part1Liminf :
    0 < p.a → 0 < p.b → 1 ≤ p.m →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          ∃ deltaU > 0,
            deltaU ≤ liminfInfValue intervalDomain u ∧
            p.ν / p.μ * (liminfInfValue intervalDomain u) ^ p.γ ≤
              liminfInfValue intervalDomain v ∧
            (∀ᶠ t in atTop, ∀ x : intervalDomain.Point, deltaU ≤ u t x) ∧
            (∀ᶠ t in atTop, ∀ x : intervalDomain.Point,
              p.ν / p.μ * deltaU ^ p.γ ≤ v t x)
  part2 :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            ∀ᶠ t in atTop,
              ∀ x : intervalDomain.Point, theorem21Part2LowerU p ≤ u t x
  part2Liminf :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            theorem21Part2LowerU p ≤ liminfInfValue intervalDomain u ∧
            p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤
              liminfInfValue intervalDomain v
  part3 :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          ∀ᶠ t in atTop,
            ∀ x : intervalDomain.Point, theorem21Part3LowerU p ≤ u t x
  part3Liminf :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          theorem21Part3LowerU p ≤ liminfInfValue intervalDomain u ∧
          p.ν / p.μ * theorem21Part3LowerU p ^ p.γ ≤
            liminfInfValue intervalDomain v

/-- Once the three u-lower fields are proved, the existing elliptic transfer
and persistence packaging close `IntervalDomainLogisticPersistenceInputs`. -/
def IntervalDomainLogisticULowerFields.to_inputs
    {p : CM2Params} (h : IntervalDomainLogisticULowerFields p) :
    IntervalDomainLogisticPersistenceInputs p where
  part1ULower := h.part1
  part1Liminf := h.part1Liminf
  part2ULower := h.part2
  part2Liminf := h.part2Liminf
  part3ULower := h.part3
  part3Liminf := h.part3Liminf

/-- Once the three u-lower fields are proved, the logistic-branch sectorial
persistence package follows from the already proved wrappers. -/
def IntervalDomainLogisticULowerFields.to_persistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainLogisticULowerFields p)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    IntervalDomainSectorialTheorem21Persistence p uBar :=
  h.to_inputs.to_persistence ha hb

/-- Current proved critical-point formula for the formal interval-domain
chemotaxis divergence.  The factor is linear in `u(x*)`; it is not the
`u(x*) ^ p.m` factor needed for the requested superlinear `z ^ p.m`
spatial-minimum Dini inequality. -/
theorem intervalDomain_chemDiv_critical_linear_factor
    {p : CM2Params} {u v : intervalDomain.Point → ℝ}
    {x : intervalDomain.Point} {vx vxx : ℝ}
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y) :
    intervalDomainChemotaxisDiv p u v x =
      intervalDomainLift u x.1 *
        (-p.β * (1 + intervalDomainLift v x.1) ^ (-p.β - 1) * vx ^ 2
          + (1 + intervalDomainLift v x.1) ^ (-p.β) * vxx) :=
  chemDiv_at_critical hux hv hvxx hvnn

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.IntervalDomainLogisticULowerFields.to_inputs
#print axioms ShenWork.Paper3.IntervalDomainLogisticULowerFields.to_persistence
#print axioms ShenWork.Paper3.intervalDomain_chemDiv_critical_linear_factor
