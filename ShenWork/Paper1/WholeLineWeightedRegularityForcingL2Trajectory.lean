import ShenWork.Paper1.WholeLineWeightedRegularityForcingContinuity
import ShenWork.Paper1.WholeLineWeightedRegularityForcingTrajectory

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical exact-weight `L²` trajectory of the generator forcing

The expanded forcing already comes with scalar exact-weight strong `L²`
continuity.  This file packages its square-integrable representatives into
the canonical `WholeLineRealL2` section and records the representative,
norm, and continuity interfaces.  It also identifies the expanded
representative with the physical generator forcing on every classical
positive-time slice.
-/

/-- The canonical `L²(ℝ)` realization of the exact-weight expanded
generator forcing. -/
def paper5WeightedGeneratorForcingExpandedL2Trajectory
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ)
    (hF_meas : ∀ t, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t) volume)
    (hF_sq : ∀ t, Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t x ^ 2) volume) :
    ℝ → WholeLineRealL2 :=
  wholeLineRealL2Section
    (paper5WeightedGeneratorForcingExpandedTrajectory
      p eta u v U W Wx Z Zx) hF_meas hF_sq

/-- The canonical `L²` trajectory represents the expanded scalar forcing
almost everywhere at every time. -/
theorem paper5WeightedGeneratorForcingExpandedL2Trajectory_coe_ae
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ)
    (hF_meas : ∀ t, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t) volume)
    (hF_sq : ∀ t, Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t x ^ 2) volume)
    (t : ℝ) :
    (((paper5WeightedGeneratorForcingExpandedL2Trajectory
          p eta u v U W Wx Z Zx hF_meas hF_sq t : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume]
      paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t) := by
  exact wholeLineRealL2Section_coe_ae
    (paper5WeightedGeneratorForcingExpandedTrajectory
      p eta u v U W Wx Z Zx) hF_meas hF_sq t

/-- The squared Hilbert norm of the canonical trajectory is the concrete
square integral of the expanded forcing. -/
theorem paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sq
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ)
    (hF_meas : ∀ t, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t) volume)
    (hF_sq : ∀ t, Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t x ^ 2) volume)
    (t : ℝ) :
    ‖paper5WeightedGeneratorForcingExpandedL2Trajectory
        p eta u v U W Wx Z Zx hF_meas hF_sq t‖ ^ 2 =
      ∫ x : ℝ,
        paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx t x ^ 2 := by
  exact wholeLineRealL2Section_norm_sq
    (paper5WeightedGeneratorForcingExpandedTrajectory
      p eta u v U W Wx Z Zx) hF_meas hF_sq t

/-- Unsquared norm form of the preceding identity. -/
theorem paper5WeightedGeneratorForcingExpandedL2Trajectory_norm
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ)
    (hF_meas : ∀ t, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t) volume)
    (hF_sq : ∀ t, Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t x ^ 2) volume)
    (t : ℝ) :
    ‖paper5WeightedGeneratorForcingExpandedL2Trajectory
        p eta u v U W Wx Z Zx hF_meas hF_sq t‖ =
      Real.sqrt (∫ x : ℝ,
        paper5WeightedGeneratorForcingExpandedTrajectory
          p eta u v U W Wx Z Zx t x ^ 2) := by
  rw [← paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- All-time scalar strong `L²` continuity turns the canonical expanded
forcing section into a continuous Hilbert-valued trajectory.  The retained
eventual square-integrability component is the native output of the
forcing-specific strong-`L²` producer. -/
theorem paper5WeightedGeneratorForcingExpandedL2Trajectory_continuous
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ → ℝ)
    (hF_meas : ∀ t, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t) volume)
    (hF_sq : ∀ t, Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcingExpandedTrajectory
        p eta u v U W Wx Z Zx t x ^ 2) volume)
    (hstrong : ∀ t,
      (∀ᶠ s in nhds t, Integrable (fun x : ℝ =>
        (paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx s x -
          paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx t x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx s x -
          paper5WeightedGeneratorForcingExpandedTrajectory
            p eta u v U W Wx Z Zx t x) ^ 2)
        (nhds t) (nhds 0)) :
    Continuous
      (paper5WeightedGeneratorForcingExpandedL2Trajectory
        p eta u v U W Wx Z Zx hF_meas hF_sq) := by
  exact wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero
    hF_meas hF_sq (fun t => (hstrong t).2)

/-- On a classical positive-time slice, the expanded exact-weight forcing
with the actual weighted population and signal fields agrees pointwise with
the physical generator forcing. -/
theorem paper5WeightedGeneratorForcingExpandedTrajectory_eq_generatorForcing
    (p : CMParams) {T eta c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    paper5WeightedGeneratorForcingExpandedTrajectory p eta
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U)
        (paper5WeightedPopulationX eta (coMovingPath c u) U)
        (paper5WeightedSignal eta (coMovingPath c v) V)
        (paper5WeightedSignalX eta (coMovingPath c v) V) t x =
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x := by
  calc
    paper5WeightedGeneratorForcingExpandedTrajectory p eta
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U)
        (paper5WeightedPopulationX eta (coMovingPath c u) U)
        (paper5WeightedSignal eta (coMovingPath c v) V)
        (paper5WeightedSignalX eta (coMovingPath c v) V) t x =
      paper5WeightedLowerOrderSource p eta c
          (coMovingPath c u) (coMovingPath c v) U
          (paper5WeightedPopulation eta (coMovingPath c u) U t)
          (paper5WeightedPopulationX eta (coMovingPath c u) U t)
          (paper5WeightedSignal eta (coMovingPath c v) V t)
          (paper5WeightedSignalX eta (coMovingPath c v) V t) t x -
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x :=
      paper5WeightedGeneratorForcingExpandedTrajectory_eq
        p eta c (coMovingPath c u) (coMovingPath c v) U
          (paper5WeightedPopulation eta (coMovingPath c u) U)
          (paper5WeightedPopulationX eta (coMovingPath c u) U)
          (paper5WeightedSignal eta (coMovingPath c v) V)
          (paper5WeightedSignalX eta (coMovingPath c v) V) t x
    _ = paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x :=
      paper5WeightedLowerOrderSource_sub_growth_eq_generatorForcing
        p hsol ht0 htT hTW hu (hTW.U_pos x).le
          hu1 hv2 hU1 hV2

/-- Function-valued form of the classical pointwise identification. -/
theorem paper5WeightedGeneratorForcingExpandedTrajectory_fun_eq_generatorForcing
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    paper5WeightedGeneratorForcingExpandedTrajectory p eta
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U)
        (paper5WeightedPopulationX eta (coMovingPath c u) U)
        (paper5WeightedSignal eta (coMovingPath c v) V)
        (paper5WeightedSignalX eta (coMovingPath c v) V) t =
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t := by
  funext x
  exact paper5WeightedGeneratorForcingExpandedTrajectory_eq_generatorForcing
    p hsol ht0 htT hTW (hu x) hu1 hv2 hU1 hV2

/-- The canonical expanded-forcing trajectory therefore represents the
physical generator forcing almost everywhere on every classical
positive-time slice. -/
theorem paper5WeightedGeneratorForcingExpandedL2Trajectory_coe_ae_generatorForcing
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hF_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory p eta
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U)
        (paper5WeightedPopulationX eta (coMovingPath c u) U)
        (paper5WeightedSignal eta (coMovingPath c v) V)
        (paper5WeightedSignalX eta (coMovingPath c v) V) s) volume)
    (hF_sq : ∀ s, Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcingExpandedTrajectory p eta
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U)
        (paper5WeightedPopulationX eta (coMovingPath c u) U)
        (paper5WeightedSignal eta (coMovingPath c v) V)
        (paper5WeightedSignalX eta (coMovingPath c v) V) s x ^ 2) volume)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    (((paper5WeightedGeneratorForcingExpandedL2Trajectory p eta
          (coMovingPath c u) (coMovingPath c v) U
          (paper5WeightedPopulation eta (coMovingPath c u) U)
          (paper5WeightedPopulationX eta (coMovingPath c u) U)
          (paper5WeightedSignal eta (coMovingPath c v) V)
          (paper5WeightedSignalX eta (coMovingPath c v) V)
          hF_meas hF_sq t : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t) := by
  filter_upwards [
    paper5WeightedGeneratorForcingExpandedL2Trajectory_coe_ae
      p eta (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U)
        (paper5WeightedPopulationX eta (coMovingPath c u) U)
        (paper5WeightedSignal eta (coMovingPath c v) V)
        (paper5WeightedSignalX eta (coMovingPath c v) V)
        hF_meas hF_sq t] with x hx
  rw [hx]
  exact paper5WeightedGeneratorForcingExpandedTrajectory_eq_generatorForcing
    p hsol ht0 htT hTW (hu x) hu1 hv2 hU1 hV2

section AxiomAudit

#print axioms paper5WeightedGeneratorForcingExpandedL2Trajectory_coe_ae
#print axioms paper5WeightedGeneratorForcingExpandedL2Trajectory_norm_sq
#print axioms paper5WeightedGeneratorForcingExpandedL2Trajectory_norm
#print axioms paper5WeightedGeneratorForcingExpandedL2Trajectory_continuous
#print axioms
  paper5WeightedGeneratorForcingExpandedTrajectory_eq_generatorForcing
#print axioms
  paper5WeightedGeneratorForcingExpandedTrajectory_fun_eq_generatorForcing
#print axioms
  paper5WeightedGeneratorForcingExpandedL2Trajectory_coe_ae_generatorForcing

end AxiomAudit

end ShenWork.Paper1
