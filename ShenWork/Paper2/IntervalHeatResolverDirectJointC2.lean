/-
  Historical compatibility wrapper.

  The original contents of this file duplicated the direct cutoff resolver
  construction and isolated three analytic placeholders.  The maintained proof is
  now `ShenWork.Paper2.HeatResolverJointC2Direct.heatResolver_jointContDiffAt_two`.
-/
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)

noncomputable section

namespace ShenWork.Paper2.HeatResolverDirectJointC2

/-- Compatibility name for the maintained heat-level resolver joint `C²` theorem. -/
theorem heatResolver_directJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s₀, x₀) :=
  ShenWork.Paper2.HeatResolverJointC2Direct.heatResolver_jointContDiffAt_two
    hu₀_bound hu₀_cont hu₀_pos hfloor hc hs₀ hx₀

end ShenWork.Paper2.HeatResolverDirectJointC2

end -- noncomputable section
