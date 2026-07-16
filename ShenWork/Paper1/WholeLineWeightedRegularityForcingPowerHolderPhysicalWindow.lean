import ShenWork.Paper1.WholeLineWeightedRegularityForcingPowerHolderWindow
import ShenWork.Paper1.WholeLineWeightedRegularityForcingContinuityNatural

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Transfer the uniform forcing modulus to the physical trajectory

The quantitative estimate is proved for the expanded four-term forcing.
On a classical positive-time window that scalar field equals the physical
generator forcing, so their clamped canonical `L²` trajectories are exactly
equal.
-/

/-- Pointwise equality on a closed time window gives equality of the clamped
canonical `L²` trajectories. -/
theorem wholeLineRealL2PositiveWindowTrajectory_congr
    {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ q ∈ Set.Icc a b, f q = g q) :
    wholeLineRealL2PositiveWindowTrajectory hab f =
      wholeLineRealL2PositiveWindowTrajectory hab g := by
  funext s
  unfold wholeLineRealL2PositiveWindowTrajectory
  rw [hfg _ (Set.projIcc a b hab s).2]

/-- On a classical positive-time window the clamped expanded forcing
trajectory is exactly the natural physical forcing trajectory. -/
theorem paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_eq_expanded
    (p : CMParams) {T eta c a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hbT : b < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ q ∈ Set.Icc a b, ∀ x, 0 ≤ coMovingPath c u q x)
    (hu2 : ∀ q ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c v q))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V) :
    paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
        p eta c u v U V hab =
      wholeLineRealL2PositiveWindowTrajectory hab
        (paper5WeightedGeneratorForcingExpandedTrajectory p eta
          (coMovingPath c u) (coMovingPath c v) U
          (paper5WeightedPopulation eta (coMovingPath c u) U)
          (paper5WeightedPopulationX eta (coMovingPath c u) U)
          (paper5WeightedSignal eta (coMovingPath c v) V)
          (paper5WeightedSignalX eta (coMovingPath c v) V)) := by
  apply wholeLineRealL2PositiveWindowTrajectory_congr
  intro q hq
  exact
    (paper5WeightedGeneratorForcingExpandedTrajectory_fun_eq_generatorForcing
      p hsol (ha.trans_le hq.1) (hq.2.trans_lt hbT) hTW (hu q hq)
        ((hu2 q hq).of_le (by norm_num)) (hv2 q hq)
        (hU2.of_le (by norm_num)) hV2).symm

/-- Any uniform Hölder estimate for the expanded clamped trajectory transfers
verbatim to the natural physical forcing trajectory. -/
theorem exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_of_expanded
    (p : CMParams) {T eta c a b theta : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hbT : b < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ q ∈ Set.Icc a b, ∀ x, 0 ≤ coMovingPath c u q x)
    (hu2 : ∀ q ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c v q))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hholder : ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖wholeLineRealL2PositiveWindowTrajectory hab
              (paper5WeightedGeneratorForcingExpandedTrajectory p eta
                (coMovingPath c u) (coMovingPath c v) U
                (paper5WeightedPopulation eta (coMovingPath c u) U)
                (paper5WeightedPopulationX eta (coMovingPath c u) U)
                (paper5WeightedSignal eta (coMovingPath c v) V)
                (paper5WeightedSignalX eta (coMovingPath c v) V)) s -
            wholeLineRealL2PositiveWindowTrajectory hab
              (paper5WeightedGeneratorForcingExpandedTrajectory p eta
                (coMovingPath c u) (coMovingPath c v) U
                (paper5WeightedPopulation eta (coMovingPath c u) U)
                (paper5WeightedPopulationX eta (coMovingPath c u) U)
                (paper5WeightedSignal eta (coMovingPath c v) V)
                (paper5WeightedSignalX eta (coMovingPath c v) V)) t‖ ≤
          H * |s - t| ^ theta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab s -
            paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab t‖ ≤
          H * |s - t| ^ theta := by
  rw [paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_eq_expanded
    p hab ha hbT hsol hTW hu hu2 hv2 hU2 hV2]
  exact hholder

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineRealL2PositiveWindowTrajectory_congr
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_eq_expanded
#print axioms
  ShenWork.Paper1.exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_of_expanded
