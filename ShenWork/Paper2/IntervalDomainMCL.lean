import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainStructuredMoserPower

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainStructuredMoserData
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMCL

/-- General unit-interval GN/Young power estimate feeding the relative Moser
interpolation field.  This is deliberately stated for an arbitrary profile
`f`, not as the Moser-closure field for a particular solution. -/
def UnitIntervalPowerGNYoungForMoser : Prop :=
  ∀ rho p eps : ℝ, 0 < rho → 0 < p → 0 < eps →
    ∃ Ceps, 0 ≤ Ceps ∧
      ∀ f : intervalDomain.Point → ℝ,
        ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
        (∀ x, 0 ≤ f x) →
          intervalDomain.integral (fun x => f x ^ (p + rho)) ≤
            eps * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => f y ^ (p / 2)) x) ^ 2) +
            Ceps * intervalDomain.integral (fun x => f x ^ p)

theorem relativeMoserInterpolationBefore_of_unitIntervalPowerGNYoung
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hGN : UnitIntervalPowerGNYoungForMoser) :
    RelativeMoserInterpolationBefore intervalDomain u T rho p0 := by
  intro p hp eps heps
  have hrho := AbstractLpBootstrapHypothesis.rho_pos hboot
  have hp_pos : 0 < p := by
    have hp0_gt_one : 1 < p0 := by
      have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
      have hone_le : (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
        le_max_left _ _
      linarith
    linarith
  rcases hGN rho p eps hrho hp_pos heps with ⟨Ceps, hCeps, hineq⟩
  refine ⟨Ceps, hCeps, ?_⟩
  intro t ht0 htT
  have htI : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  rcases hsol.regularity with ⟨_, _, _, _, hclosed, _, _⟩
  have hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ((hclosed t htI).1.1).continuousOn
  exact hineq (u t) hcont
    (fun x => (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)

/-- Regularity now supplies energy, power-integrability, and Lp monotonicity.
The remaining inputs are the committed relative interpolation, the committed
dissipation/drop condition, and the quantitative root-tower endpoint. -/
def structuredMoserBootstrapData_of_regularity_MCL
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBefore intervalDomain u T rho p0)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IntervalDomainStructuredMoserBootstrapData u T :=
  intervalDomain_structuredMoserBootstrapData_of_regularity hsol hcross hboot
    hdiss hrel
    (lpMono_of_classical_solution_power_integrable hsol
      (intervalDomain_classical_solution_powerIntegrable hsol))
    hEndpoint

end ShenWork.Paper2.IntervalDomainMCL

end
