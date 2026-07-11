/-
  Positive-time generator identity for the full Neumann semigroup.

  The public generic wrapper combines the cosine-series target-time derivative
  with the already-proved closed-interval identification of the spectral second
  value with the literal second spatial derivative of the propagator.

  The faithful subtype wrapper then replaces the discontinuous zero extension
  `intervalDomainLift u₀` by the continuous clipped extension of `u₀`.  The
  two extensions agree on `[0,1]`, hence define the same full Neumann semigroup
  at every time and spatial point.
-/
import ShenWork.Paper2.ChemMildC1eta
import ShenWork.Paper2.IntervalMildPicardThreshold

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDomainRegularityBootstrap
  (unitIntervalCosineHeatSecondValue)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_continuous unitClip_of_mem)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded)

/-- At positive time, the target-time derivative of the full Neumann semigroup
is its literal second spatial derivative at every point of the closed interval.

This is the public endpoint-safe wrapper around
`unitIntervalCosineHeatValue_hasDerivAt_time` and
`intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc`. -/
theorem intervalFullSemigroupOperator_hasDerivAt_time_secondDeriv_Icc
    {t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ => intervalFullSemigroupOperator r f x)
      (deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator t f z) y) x)
      t := by
  have htime :
      HasDerivAt
        (fun r : ℝ => unitIntervalCosineHeatValue r (cosineCoeffs f) x)
        (unitIntervalCosineHeatSecondValue t (cosineCoeffs f) x) t :=
    ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
      ht hM
  have htime_semigroup :
      HasDerivAt
        (fun r : ℝ => intervalFullSemigroupOperator r f x)
        (unitIntervalCosineHeatSecondValue t (cosineCoeffs f) x) t := by
    refine htime.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact
      ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
        hr hf hM hx
  rw [intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc ht hf hM hx]
  exact htime_semigroup

/-- Faithful subtype-datum form of the positive-time generator identity.

Continuity of `u₀` is the only datum hypothesis.  Compactness supplies a
coefficient bound internally.  The continuous clipped extension and the
zero-extension lift agree on `[0,1]`, which is all the full Neumann operator
sees. -/
theorem intervalFullSemigroupOperator_lift_hasDerivAt_time_secondDeriv_Icc
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : Continuous u₀)
    {t x : ℝ} (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ =>
        intervalFullSemigroupOperator r (intervalDomainLift u₀) x)
      (deriv (fun y : ℝ => deriv
        (fun z : ℝ =>
          intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y) x)
      t := by
  let f : ℝ → ℝ := fun y => u₀ (unitClip y)
  have hf : Continuous f := hu₀.comp unitClip_continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  let C : ℝ := max B 0
  have hC : 0 ≤ C := by
    exact le_max_right B 0
  have hf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ C := by
    intro y hy
    have hyB := hB y hy
    rw [Real.norm_eq_abs] at hyB
    exact hyB.trans (le_max_left B 0)
  have hcoeff : ∀ n, |cosineCoeffs f n| ≤ 2 * C :=
    cosineCoeffs_abs_le_of_continuous_bounded hf.continuousOn hC hf_bound
  have hmain :=
    intervalFullSemigroupOperator_hasDerivAt_time_secondDeriv_Icc
      ht hf hcoeff hx
  have hlift_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ y = f y := by
    intro y hy
    simp [f, intervalDomainLift, hy, unitClip_of_mem hy]
  have hsemigroup : ∀ r z,
      intervalFullSemigroupOperator r (intervalDomainLift u₀) z =
        intervalFullSemigroupOperator r f z := by
    intro r z
    exact intervalFullSemigroupOperator_congr_on_Icc hlift_eq z
  have htime_eq :
      (fun r : ℝ =>
        intervalFullSemigroupOperator r (intervalDomainLift u₀) x) =
      (fun r : ℝ => intervalFullSemigroupOperator r f x) := by
    funext r
    exact hsemigroup r x
  have hspace_eq :
      (fun z : ℝ =>
        intervalFullSemigroupOperator t (intervalDomainLift u₀) z) =
      (fun z : ℝ => intervalFullSemigroupOperator t f z) := by
    funext z
    exact hsemigroup t z
  rw [htime_eq, hspace_eq]
  exact hmain

/-- Derivative-value form of
`intervalFullSemigroupOperator_lift_hasDerivAt_time_secondDeriv_Icc`. -/
theorem intervalFullSemigroupOperator_lift_timeDeriv_eq_secondDeriv_Icc
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : Continuous u₀)
    {t x : ℝ} (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv
        (fun r : ℝ =>
          intervalFullSemigroupOperator r (intervalDomainLift u₀) x) t =
      deriv (fun y : ℝ => deriv
        (fun z : ℝ =>
          intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y) x :=
  (intervalFullSemigroupOperator_lift_hasDerivAt_time_secondDeriv_Icc
    hu₀ ht hx).deriv

section AxiomAudit

#print axioms intervalFullSemigroupOperator_hasDerivAt_time_secondDeriv_Icc
#print axioms intervalFullSemigroupOperator_lift_hasDerivAt_time_secondDeriv_Icc
#print axioms intervalFullSemigroupOperator_lift_timeDeriv_eq_secondDeriv_Icc

end AxiomAudit

end ShenWork.Paper2
