import ShenWork.Paper3.MinimalSteadyWABranchSelection
import ShenWork.Paper3.StaticWAEvalAlgebra
import ShenWork.Paper2.IntervalDomainResolverStrictPos

/-!
# Classical profiles on the local minimal steady branch

For a branch amplitude `a`, the physical population and signal coefficients
are

`u = 1 + a h`,  `v = 1 + a R h`.

This file realizes them as real `C²` functions.  It proves the Neumann
conditions and mass constraint for every amplitude, nonconstancy for
`a ≠ 0`, and positivity for all amplitudes sufficiently close to zero.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open Filter Set Topology
open ShenWork.Wiener
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalPicardIterateRestart

/-! ## Physical coefficient curves -/

def minimalSteadyPopulationCoeff (a : ℝ) : WA 2 :=
  blownPopulation (minimalSteadyBranchPoint a)

/-- Since `blownDenominator = 1 + v`, subtracting the algebra unit gives the
physical signal `v = 1 + a R h`. -/
def minimalSteadySignalCoeff (a : ℝ) : WA 2 :=
  blownDenominator (minimalSteadyBranchPoint a) - 1

def minimalSteadyPopulationEvenReal (a : ℝ) : EvenRealWA 2 :=
  blownPopulationEvenReal (minimalSteadyBranchPoint a)

def minimalSteadySignalEvenReal (a : ℝ) : EvenRealWA 2 :=
  ⟨minimalSteadySignalCoeff a,
    (evenRealSubmodule 2).sub_mem
      (blownDenominatorEvenReal (minimalSteadyBranchPoint a)).2
      (one_mem_evenReal 2)⟩

@[simp]
theorem minimalSteadyPopulationEvenReal_coe (a : ℝ) :
    (minimalSteadyPopulationEvenReal a : WA 2) =
      minimalSteadyPopulationCoeff a :=
  rfl

@[simp]
theorem minimalSteadySignalEvenReal_coe (a : ℝ) :
    (minimalSteadySignalEvenReal a : WA 2) =
      minimalSteadySignalCoeff a :=
  rfl

theorem minimalSteadyPopulationCoeff_formula (a : ℝ) :
    minimalSteadyPopulationCoeff a =
      1 + a • branchSpaceAmbientCLM (minimalSteadyProfile a) :=
  rfl

theorem minimalSteadySignalCoeff_formula (a : ℝ) :
    minimalSteadySignalCoeff a =
      1 + a • signalResolverAmbientCLM (minimalSteadyProfile a) := by
  unfold minimalSteadySignalCoeff blownDenominator
    minimalSteadyBranchPoint minimalSteadyProfile
  simp only [branchAmplitudeCLM_apply]
  rw [two_smul]
  abel

@[simp]
theorem minimalSteadyPopulationCoeff_zero :
    minimalSteadyPopulationCoeff 0 = 1 := by
  rw [minimalSteadyPopulationCoeff,
    minimalSteadyBranchPoint_zero, blownPopulation_base]

@[simp]
theorem minimalSteadySignalCoeff_zero :
    minimalSteadySignalCoeff 0 = 1 := by
  rw [minimalSteadySignalCoeff,
    minimalSteadyBranchPoint_zero, blownDenominator_base, two_smul]
  abel

/-! ## Classical realization -/

def minimalSteadyPopulation (a : ℝ) : ℝ → ℝ :=
  staticEval (minimalSteadyPopulationCoeff a)

def minimalSteadySignal (a : ℝ) : ℝ → ℝ :=
  staticEval (minimalSteadySignalCoeff a)

theorem minimalSteadyPopulation_contDiff_two (a : ℝ) :
    ContDiff ℝ 2 (minimalSteadyPopulation a) :=
  staticEval_contDiff_two (minimalSteadyPopulationEvenReal a)

theorem minimalSteadySignal_contDiff_two (a : ℝ) :
    ContDiff ℝ 2 (minimalSteadySignal a) :=
  staticEval_contDiff_two (minimalSteadySignalEvenReal a)

theorem minimalSteadyPopulation_neumann_zero (a : ℝ) :
    deriv (minimalSteadyPopulation a) 0 = 0 :=
  staticEval_neumann_zero (minimalSteadyPopulationEvenReal a)

theorem minimalSteadyPopulation_neumann_one (a : ℝ) :
    deriv (minimalSteadyPopulation a) 1 = 0 :=
  staticEval_neumann_one (minimalSteadyPopulationEvenReal a)

theorem minimalSteadySignal_neumann_zero (a : ℝ) :
    deriv (minimalSteadySignal a) 0 = 0 :=
  staticEval_neumann_zero (minimalSteadySignalEvenReal a)

theorem minimalSteadySignal_neumann_one (a : ℝ) :
    deriv (minimalSteadySignal a) 1 = 0 :=
  staticEval_neumann_one (minimalSteadySignalEvenReal a)

/-! ## Mass and prescribed first mode -/

theorem minimalSteadyPopulationCoeff_zero_mode (a : ℝ) :
    (minimalSteadyPopulationCoeff a).toFun 0 = 1 := by
  rw [minimalSteadyPopulationCoeff_formula]
  change
    wOne 0 +
        ((a : ℂ) * (minimalSteadyProfile a).1.1.toFun 0) =
      1
  rw [MeanZeroEvenRealWA.coeff_zero]
  simp [wOne]

theorem minimalSteadyPopulation_mass (a : ℝ) :
    ∫ x in (0 : ℝ)..1, minimalSteadyPopulation a x = 1 := by
  change
    ∫ x in (0 : ℝ)..1,
      staticEval (minimalSteadyPopulationEvenReal a).1 x = 1
  rw [intervalIntegral_staticEval_eq_coeff_zero
      (minimalSteadyPopulationEvenReal a)]
  change ((minimalSteadyPopulationCoeff a).toFun 0).re = 1
  rw [minimalSteadyPopulationCoeff_zero_mode]
  norm_num

theorem minimalSteadyProfile_amplitude (a : ℝ) :
    amplitudeCLM (minimalSteadyProfile a) = 1 := by
  rw [minimalSteadyProfile_formula, map_add,
    amplitude_firstMode, amplitude_complement, add_zero]

theorem minimalSteadyPopulation_cosineCoeff_one (a : ℝ) :
    staticCosCoeff (minimalSteadyPopulationEvenReal a) 1 = a := by
  rw [staticCosCoeff_of_ne_zero
    (minimalSteadyPopulationEvenReal a) (by norm_num)]
  change
    2 * ((minimalSteadyPopulationCoeff a).toFun 1).re = a
  rw [minimalSteadyPopulationCoeff_formula]
  change
    2 * (wOne 1 +
      (a : ℂ) * (minimalSteadyProfile a).1.1.toFun 1).re = a
  simp only [wOne, if_neg (by norm_num : (1 : ℤ) ≠ 0), zero_add,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hamp := minimalSteadyProfile_amplitude a
  rw [amplitudeCLM_apply] at hamp
  calc
    2 * (a * ((minimalSteadyProfile a).1.1.toFun 1).re) =
        a * (2 * ((minimalSteadyProfile a).1.1.toFun 1).re) := by ring
    _ = a := by rw [hamp, mul_one]

theorem minimalSteadyPopulation_nonconstant {a : ℝ} (ha : a ≠ 0) :
    ¬ ∀ x y : ℝ,
      minimalSteadyPopulation a x = minimalSteadyPopulation a y := by
  have hcoeff :
      cosineCoeffs (minimalSteadyPopulation a) 1 = a := by
    have h :=
      cosineCoeffs_of_l1_cosineSeries
        (staticCosCoeff_summable
          (minimalSteadyPopulationEvenReal a)) 1
    rw [← staticEval_evenReal_eq_cosineSeries
      (minimalSteadyPopulationEvenReal a)] at h
    exact h.trans (minimalSteadyPopulation_cosineCoeff_one a)
  intro hconstant
  have hfun :
      minimalSteadyPopulation a =
        fun _ => minimalSteadyPopulation a 0 := by
    funext x
    exact hconstant x 0
  rw [hfun,
    ShenWork.IntervalDomainResolverStrictPos.cosineCoeffs_const,
    if_neg (by norm_num : (1 : ℕ) ≠ 0)] at hcoeff
  exact ha hcoeff.symm

/-! ## Positivity near the branch point -/

theorem staticEval_pos_of_norm_sub_one_lt_one
    (a : EvenRealWA 2) (hsmall : ‖a.1 - 1‖ < 1) (x : ℝ) :
    0 < staticEval a.1 x := by
  have hbound := abs_staticEval_le_norm (a.1 - 1) x
  have habs :
      |staticEval (a.1 - 1) x| < 1 :=
    lt_of_le_of_lt hbound hsmall
  have heq :
      staticEval (a.1 - 1) x = staticEval a.1 x - 1 := by
    calc
      staticEval (a.1 - 1) x =
          (staticEval a.1 - staticEval 1) x :=
        congrFun (staticEval_sub a.1 1) x
      _ = staticEval a.1 x - 1 := by
        rw [Pi.sub_apply, congrFun (staticEval_one 2) x]
        rfl
  rw [heq, abs_lt] at habs
  linarith

theorem minimalSteadyPopulationCoeff_continuousAt :
    ContinuousAt minimalSteadyPopulationCoeff 0 := by
  exact
    blownPopulation_contDiff.continuous.continuousAt.comp'
      minimalSteadyBranchPoint_contDiffAt.continuousAt

theorem minimalSteadySignalCoeff_continuousAt :
    ContinuousAt minimalSteadySignalCoeff 0 := by
  exact
    (blownDenominator_contDiff.continuous.continuousAt.comp'
      minimalSteadyBranchPoint_contDiffAt.continuousAt).sub continuousAt_const

theorem eventually_minimalSteadyPopulationCoeff_close_one :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      ‖minimalSteadyPopulationCoeff a - 1‖ < 1 := by
  have ht :
      Tendsto minimalSteadyPopulationCoeff (𝓝 0) (𝓝 (1 : WA 2)) := by
    rw [← minimalSteadyPopulationCoeff_zero]
    exact minimalSteadyPopulationCoeff_continuousAt
  have hball :=
    ht.eventually (Metric.ball_mem_nhds (1 : WA 2) one_pos)
  simpa only [Metric.mem_ball, dist_eq_norm] using hball

theorem eventually_minimalSteadySignalCoeff_close_one :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      ‖minimalSteadySignalCoeff a - 1‖ < 1 := by
  have ht :
      Tendsto minimalSteadySignalCoeff (𝓝 0) (𝓝 (1 : WA 2)) := by
    rw [← minimalSteadySignalCoeff_zero]
    exact minimalSteadySignalCoeff_continuousAt
  have hball :=
    ht.eventually (Metric.ball_mem_nhds (1 : WA 2) one_pos)
  simpa only [Metric.mem_ball, dist_eq_norm] using hball

theorem eventually_minimalSteady_profiles_positive :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      (∀ x : ℝ, 0 < minimalSteadyPopulation a x) ∧
        ∀ x : ℝ, 0 < minimalSteadySignal a x := by
  filter_upwards
    [eventually_minimalSteadyPopulationCoeff_close_one,
      eventually_minimalSteadySignalCoeff_close_one] with a hu hv
  exact
    ⟨fun x =>
      staticEval_pos_of_norm_sub_one_lt_one
        (minimalSteadyPopulationEvenReal a) hu x,
      fun x =>
      staticEval_pos_of_norm_sub_one_lt_one
        (minimalSteadySignalEvenReal a) hv x⟩

end ShenWork.M3Counterexample
