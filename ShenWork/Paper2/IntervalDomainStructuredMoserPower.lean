import ShenWork.Paper2.IntervalDomainStructuredMoserData

open MeasureTheory
open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure

noncomputable section

namespace ShenWork.Paper2.IntervalDomainStructuredMoserData

/-- Classical interval solutions have every positive spatial power
interval-integrable on `[0,1]`.

This discharges the `powerIntegrable` field of `Prop25MoserFrontiers` from the
closed-domain `C²` regularity and positivity already stored in
`IsPaper2ClassicalSolution intervalDomain`.
-/
theorem intervalDomain_classical_solution_powerIntegrable
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ r : ℝ, 1 < r → ∀ t, 0 < t → t < T →
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        volume 0 1 := by
  intro r _hr t ht0 htT
  have htI : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  rcases hsol.regularity with
    ⟨_, _, _, _, hclosed, _, _⟩
  have hu_cont :
      ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ((hclosed t htI).1.1).continuousOn
  have hu_ne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≠ 0 := by
    intro y hy
    have hpos : 0 < u t ⟨y, hy⟩ :=
      IsPaper2ClassicalSolution.u_pos' hsol ht0 htT
    have hne : u t ⟨y, hy⟩ ≠ 0 := ne_of_gt hpos
    simpa [intervalDomainLift, hy] using hne
  have hpow_cont :
      ContinuousOn (fun y => (intervalDomainLift (u t) y) ^ r)
        (Set.Icc (0 : ℝ) 1) :=
    hu_cont.rpow_const (fun y hy => Or.inl (hu_ne y hy))
  have htarget_cont :
      ContinuousOn
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        (Set.Icc (0 : ℝ) 1) := by
    refine hpow_cont.congr ?_
    intro y hy
    simp [intervalDomainLift, hy]
  have htarget_ucont :
      ContinuousOn
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        (uIcc (0 : ℝ) 1) := by
    rwa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact htarget_ucont.intervalIntegrable (μ := volume)

/-- Build the Prop. 2.5 Moser-frontier record once the four remaining analytic
frontiers are supplied; `powerIntegrable` is produced by classical regularity.
-/
def prop25MoserFrontiers_of_energy_dissipation_relative_endpoint
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T 1 pExp)
    (hdiss : MoserDissipationDropBefore intervalDomain u T 1 pExp)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T 1 pExp)
    (hEndpoint :
      (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    Prop25MoserFrontiers u T pExp where
  pSeq := pSeq
  rootBound := rootBound
  energy := henergy
  dissipation := hdiss
  relative := hrel
  powerIntegrable :=
    intervalDomain_classical_solution_powerIntegrable hsol
  endpoint := hEndpoint

end ShenWork.Paper2.IntervalDomainStructuredMoserData

end
