import ShenWork.Paper2.IntervalFractionalSubordinationScalar
import ShenWork.Paper2.IntervalFullKernelFullQGenerator
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.IntervalRestartDerivJointContinuity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Fractional full-`q` Neumann smoothing by derivative subordination

For `0 < sigma < 1` we realize

`(-Delta_N)^sigma exp(t Delta_N)`

as the absolutely convergent Bochner integral of
`s^(-sigma) (-Delta_N) exp((t+s) Delta_N)`.  The integer generator has the
physical full-`q` Schur estimate from
`IntervalFullKernelFullQGenerator`; the time integral is handled by
`norm_integral_le_integral_norm` through the abstract theorem in
`IntervalFractionalSubordinationScalar`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology BigOperators BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper2.IntervalFractionalSubordinationFullQ

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.HeatKernelGradientEstimates
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugateCosineSeries
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalDomainRegularityBootstrap
open ShenWork.Paper2.IntervalFullKernelFullQGenerator
open ShenWork.Paper2.IntervalFractionalSubordinationScalar

/-! ## Spectral identification of the physical generator -/

private theorem neumannCosineWeight_abs_le_two (n : ℕ) :
    |neumannCosineWeight n| ≤ (2 : ℝ) := by
  unfold neumannCosineWeight
  by_cases hn : n = 0 <;> simp [hn]

private theorem kernelNatCoeff_grad2_summable
    {t x : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ =>
      |neumannCosineWeight n *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * cosineMode n x| *
        (((n : ℝ) * Real.pi) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((ShenWork.IntervalRestartDerivJointContinuity.eigenvalue_mul_exp_summable ht).mul_left 2)
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hw : |neumannCosineWeight n| ≤ 2 :=
    neumannCosineWeight_abs_le_two n
  have hc : |cosineMode n x| ≤ 1 := by
    simp only [cosineMode]
    exact Real.abs_cos_le_one _
  have hE : 0 ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    Real.exp_nonneg _
  have hfreq : 0 ≤ ((n : ℝ) * Real.pi) ^ 2 := sq_nonneg _
  calc
    |neumannCosineWeight n| *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * |cosineMode n x| *
        ((n : ℝ) * Real.pi) ^ 2
        ≤ (2 * Real.exp (-t * unitIntervalCosineEigenvalue n) * 1) *
            ((n : ℝ) * Real.pi) ^ 2 := by gcongr
    _ = 2 * (unitIntervalCosineEigenvalue n *
          Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
      simp only [unitIntervalCosineEigenvalue]
      ring

/-- Second derivative in the second variable of the full kernel, in folded
Neumann cosine form. -/
theorem secondDeriv_intervalNeumannFullKernel_eq_cosineKernel_snd
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun z : ℝ => deriv
        (fun w : ℝ => intervalNeumannFullKernel t x w) z) y =
      ∑' n : ℕ,
        (neumannCosineWeight n *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * cosineMode n x) *
          (-(((n : ℝ) * Real.pi) ^ 2) * cosineMode n y) := by
  set c : ℕ → ℝ := fun n =>
    neumannCosineWeight n *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * cosineMode n x with hc
  have hgrad2 : Summable (fun n : ℕ =>
      |c n| * (((n : ℝ) * Real.pi) ^ 2)) := by
    simpa [c, hc] using kernelNatCoeff_grad2_summable (t := t) (x := x) ht
  have hfirst :
      (fun z : ℝ => deriv
        (fun w : ℝ => intervalNeumannFullKernel t x w) z) =
      fun z : ℝ => ∑' n : ℕ,
        c n * (-((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * z)) := by
    funext z
    rw [deriv_intervalNeumannFullKernel_eq_cosineKernel_snd ht x z]
  rw [hfirst]
  simpa [c, hc, cosineMode] using
    (sineSeries_hasDerivAt_of_grad2Summable hgrad2 y).deriv

/-- The physical generator kernel has the expected nonnegative spectral
multiplier `lambda_n exp(-t lambda_n)`. -/
theorem intervalFullGeneratorKernel_eq_cosineKernel
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    intervalFullGeneratorKernel t x y =
      ∑' n : ℕ,
        (neumannCosineWeight n *
          (unitIntervalCosineEigenvalue n *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) * cosineMode n x) *
          cosineMode n y := by
  have hfun : (fun z : ℝ => intervalNeumannFullKernel t z y) =
      fun z : ℝ => intervalNeumannFullKernel t y z := by
    funext z
    exact intervalNeumannFullKernel_symm ht z y
  unfold intervalFullGeneratorKernel
  rw [hfun, secondDeriv_intervalNeumannFullKernel_eq_cosineKernel_snd ht y x]
  rw [← tsum_neg]
  exact tsum_congr (fun n => by
    simp only [unitIntervalCosineEigenvalue]
    ring)

/-- Every integrable input has uniformly bounded normalized cosine
coefficients. -/
theorem cosineCoeffs_abs_le_two_integral_norm
    {f : ℝ → ℝ} (hf : Integrable f (intervalMeasure 1)) (n : ℕ) :
    |cosineCoeffs f n| ≤
      2 * ∫ y, ‖f y‖ ∂(intervalMeasure 1) := by
  rw [cosineCoeffs_eq_factor_mul_integral]
  have hfactor : |(if n = 0 then (1 : ℝ) else 2)| ≤ 2 := by
    split_ifs <;> norm_num
  have hcosf : IntegrableOn
      (fun y : ℝ => Real.cos ((n : ℝ) * Real.pi * y) * f y)
      (Set.Ioc (0 : ℝ) 1) := by
    have hfIcc : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      simpa [intervalMeasure, intervalSet] using hf
    have hmul : Integrable
        (fun y : ℝ => Real.cos ((n : ℝ) * Real.pi * y) * f y)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      refine hfIcc.bdd_mul (c := 1)
        (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using
          Real.abs_cos_le_one ((n : ℝ) * Real.pi * y)
    have hmulOn : IntegrableOn
        (fun y : ℝ => Real.cos ((n : ℝ) * Real.pi * y) * f y)
        (Set.Icc (0 : ℝ) 1) := hmul
    exact hmulOn.mono_set Set.Ioc_subset_Icc_self
  rw [abs_mul]
  calc
    |(if n = 0 then (1 : ℝ) else 2)| *
        |∫ y in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * y) * f y|
      ≤ 2 * |∫ y in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * y) * f y| :=
        mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
    _ ≤ 2 * ∫ y in Set.Ioc (0 : ℝ) 1, ‖f y‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← Real.norm_eq_abs]
      calc
        ‖∫ y in Set.Ioc (0 : ℝ) 1,
            Real.cos ((n : ℝ) * Real.pi * y) * f y‖
          ≤ ∫ y in Set.Ioc (0 : ℝ) 1,
              ‖Real.cos ((n : ℝ) * Real.pi * y) * f y‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ y in Set.Ioc (0 : ℝ) 1, ‖f y‖ := by
          have hfnormIoc : IntegrableOn (fun y : ℝ => ‖f y‖)
              (Set.Ioc (0 : ℝ) 1) := by
            have hfnormIcc : IntegrableOn (fun y : ℝ => ‖f y‖)
                (Set.Icc (0 : ℝ) 1) := by
              simpa [intervalMeasure, intervalSet] using hf.norm
            exact hfnormIcc.mono_set Set.Ioc_subset_Icc_self
          apply integral_mono hcosf.norm
            hfnormIoc
          intro y
          change ‖Real.cos ((n : ℝ) * Real.pi * y) * f y‖ ≤ ‖f y‖
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (by simpa using Real.abs_cos_le_one ((n : ℝ) * Real.pi * y))
    _ = 2 * ∫ y, ‖f y‖ ∂(intervalMeasure 1) := by
      congr 1
      simp only [intervalMeasure, intervalSet]
      exact MeasureTheory.integral_Icc_eq_integral_Ioc.symm

private theorem intervalMeasure_integral_eq_intervalIntegral
    (g : ℝ → ℝ) :
    (∫ y, g y ∂(intervalMeasure 1)) = ∫ y in (0 : ℝ)..1, g y := by
  simp only [intervalMeasure, intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, g y ∂volume) =
    ∫ y in (0 : ℝ)..1, g y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- For every integrable source, the physical Hessian-kernel generator is
exactly the spectral generator.  This is the `L¹`-dominated sum/integral
interchange needed to connect the subordination integral with
`(-Delta_N)^sigma`. -/
theorem intervalFullGeneratorHeatOperator_eq_neg_secondValue
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Integrable f (intervalMeasure 1)) (x : ℝ) :
    intervalFullGeneratorHeatOperator t f x =
      -unitIntervalCosineHeatSecondValue t (cosineCoeffs f) x := by
  let μ := intervalMeasure 1
  let E : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n *
      Real.exp (-t * unitIntervalCosineEigenvalue n)
  let D : ℕ → ℝ → ℝ := fun n y =>
    (neumannCosineWeight n * E n * cosineMode n x) * cosineMode n y
  let F : ℕ → ℝ → ℝ := fun n y => D n y * f y
  let Cf : ℝ := ∫ y, ‖f y‖ ∂μ
  have hCf : 0 ≤ Cf := integral_nonneg fun y => norm_nonneg _
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    dsimp [E]
    exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)
  have hEsum : Summable E := by
    simpa [E] using
      ShenWork.IntervalRestartDerivJointContinuity.eigenvalue_mul_exp_summable ht
  have hFint : ∀ n, Integrable (F n) μ := by
    intro n
    have hcosf : Integrable (fun y => cosineMode n y * f y) μ := by
      refine hf.bdd_mul (c := 1) ?_ ?_
      · change AEStronglyMeasurable
          (fun y : ℝ => Real.cos ((n : ℝ) * Real.pi * y)) μ
        exact (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y => by
          simpa [cosineMode, Real.norm_eq_abs] using
            Real.abs_cos_le_one ((n : ℝ) * Real.pi * y)
    have hconst := hcosf.const_mul
      (neumannCosineWeight n * E n * cosineMode n x)
    refine hconst.congr ?_
    exact Filter.Eventually.of_forall fun y => by
      dsimp [F, D]
      ring
  have hFbound : ∀ n y, ‖F n y‖ ≤ 2 * E n * ‖f y‖ := by
    intro n y
    dsimp [F, D]
    simp only [abs_mul]
    have hw : ‖neumannCosineWeight n‖ ≤ 2 := by
      simpa [Real.norm_eq_abs] using neumannCosineWeight_abs_le_two n
    have hcx : ‖cosineMode n x‖ ≤ 1 := by
      simpa [cosineMode, Real.norm_eq_abs] using
        Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
    have hcy : ‖cosineMode n y‖ ≤ 1 := by
      simpa [cosineMode, Real.norm_eq_abs] using
        Real.abs_cos_le_one ((n : ℝ) * Real.pi * y)
    have hEn : 0 ≤ E n := hE0 n
    rw [abs_of_nonneg hEn]
    calc
      |neumannCosineWeight n| * E n * |cosineMode n x| *
            |cosineMode n y| * |f y|
        ≤ 2 * E n * 1 * 1 * |f y| := by
          simpa [Real.norm_eq_abs] using
            (show ‖neumannCosineWeight n‖ * E n * ‖cosineMode n x‖ *
                  ‖cosineMode n y‖ * ‖f y‖ ≤
                2 * E n * 1 * 1 * ‖f y‖ by gcongr)
      _ = 2 * E n * |f y| := by ring
  have hFnorm : ∀ n, (∫ y, ‖F n y‖ ∂μ) ≤ 2 * E n * Cf := by
    intro n
    calc
      (∫ y, ‖F n y‖ ∂μ) ≤
          ∫ y, 2 * E n * ‖f y‖ ∂μ :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hf.norm.const_mul (2 * E n))
          (Filter.Eventually.of_forall (hFbound n))
      _ = 2 * E n * Cf := by
        rw [MeasureTheory.integral_const_mul]
  have hFsum : Summable (fun n => ∫ y, ‖F n y‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun y => norm_nonneg _) hFnorm ?_
    exact (hEsum.mul_left 2).mul_right Cf
  have hswap :
      (∫ y, ∑' n, F n y ∂μ) = ∑' n, ∫ y, F n y ∂μ :=
    (integral_tsum_of_summable_integral_norm hFint hFsum).symm
  have hkernel : ∀ y, intervalFullGeneratorKernel t x y = ∑' n, D n y := by
    intro y
    rw [intervalFullGeneratorKernel_eq_cosineKernel ht x y]

  have hintegrand :
      (fun y => intervalFullGeneratorKernel t x y * f y) =
        fun y => ∑' n, F n y := by
    funext y
    rw [hkernel y, ← tsum_mul_right]
  have hterm : ∀ n, (∫ y, F n y ∂μ) =
      (E n * cosineCoeffs f n) * cosineMode n x := by
    intro n
    rw [cosineCoeffs_eq_factor_mul_integral]
    have hweight : neumannCosineWeight n =
        (if n = 0 then (1 : ℝ) else 2) := rfl
    dsimp [F, D]
    rw [show (fun y =>
          (neumannCosineWeight n * E n * cosineMode n x) *
              cosineMode n y * f y) =
        fun y => (neumannCosineWeight n * E n * cosineMode n x) *
          (cosineMode n y * f y) by funext y; ring,
      MeasureTheory.integral_const_mul,
      intervalMeasure_integral_eq_intervalIntegral]
    rw [hweight]
    simp only [cosineMode]
    ring
  unfold intervalFullGeneratorHeatOperator
  rw [hintegrand, hswap]
  rw [show (∑' n, ∫ y, F n y ∂μ) =
      ∑' n, (E n * cosineCoeffs f n) * cosineMode n x from
        tsum_congr hterm]
  unfold unitIntervalCosineHeatSecondValue
  rw [← tsum_neg]
  exact tsum_congr (fun n => by
    dsimp [E]
    simp only [unitIntervalCosineHeatSecondPointWeight, cosineMode,
      unitIntervalCosineEigenvalue]
    ring)

/-! ## A strongly measurable physical generator family in `Lp` -/

/-- A cosine mode as a bounded continuous function on the real line. -/
def cosineModeBCF (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (cosineMode n)
    (by
      change Continuous (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x))
      fun_prop)
    1
    (fun x => by
      simpa [cosineMode, Real.norm_eq_abs] using
        Real.abs_cos_le_one ((n : ℝ) * Real.pi * x))

theorem cosineModeBCF_norm_le_one (n : ℕ) :
    ‖cosineModeBCF n‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num)).2
  intro x
  simpa [cosineModeBCF, cosineMode, Real.norm_eq_abs] using
    Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)

/-- Bounded-continuous realization of
`(-Delta_N) exp(-u(-Delta_N))` on a cosine coefficient sequence. -/
def intervalSpectralGeneratorBCF (u : ℝ) (a : ℕ → ℝ) : ℝ →ᵇ ℝ :=
  ∑' n : ℕ,
    (unitIntervalCosineEigenvalue n *
      Real.exp (-u * unitIntervalCosineEigenvalue n) * a n) •
        cosineModeBCF n

theorem intervalSpectralGeneratorBCF_summable
    {u : ℝ} (hu : 0 < u) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n : ℕ =>
      (unitIntervalCosineEigenvalue n *
        Real.exp (-u * unitIntervalCosineEigenvalue n) * a n) •
          cosineModeBCF n) := by
  have hM0 : 0 ≤ M := (abs_nonneg (a 0)).trans (hM 0)
  have hbase :=
    ShenWork.IntervalRestartDerivJointContinuity.eigenvalue_mul_exp_summable hu
  refine Summable.of_norm_bounded (g := fun n =>
      M * (unitIntervalCosineEigenvalue n *
        Real.exp (-u * unitIntervalCosineEigenvalue n)))
    (hbase.mul_left M) ?_
  intro n
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by unfold unitIntervalCosineEigenvalue; positivity),
    abs_of_nonneg (Real.exp_nonneg _)]
  have hmode := cosineModeBCF_norm_le_one n
  have hweight0 : 0 ≤ unitIntervalCosineEigenvalue n *
      Real.exp (-u * unitIntervalCosineEigenvalue n) :=
    mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)
  calc
    unitIntervalCosineEigenvalue n *
          Real.exp (-u * unitIntervalCosineEigenvalue n) * |a n| *
        ‖cosineModeBCF n‖
      ≤ unitIntervalCosineEigenvalue n *
          Real.exp (-u * unitIntervalCosineEigenvalue n) * M *
            ‖cosineModeBCF n‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM n) hweight0) (norm_nonneg _)
    _ ≤ unitIntervalCosineEigenvalue n *
          Real.exp (-u * unitIntervalCosineEigenvalue n) * M * 1 :=
        mul_le_mul_of_nonneg_left hmode (mul_nonneg hweight0 hM0)
    _ = M * (unitIntervalCosineEigenvalue n *
        Real.exp (-u * unitIntervalCosineEigenvalue n)) := by ring

/-- Evaluation of the bounded-continuous spectral generator is the negative
spectral heat second value. -/
theorem intervalSpectralGeneratorBCF_apply
    {u : ℝ} (hu : 0 < u) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    intervalSpectralGeneratorBCF u a x =
      -unitIntervalCosineHeatSecondValue u a x := by
  have hsum := intervalSpectralGeneratorBCF_summable hu hM
  have hmap := (BoundedContinuousFunction.evalCLM ℝ x).map_tsum hsum
  rw [show intervalSpectralGeneratorBCF u a x =
      ∑' n : ℕ,
        ((unitIntervalCosineEigenvalue n *
          Real.exp (-u * unitIntervalCosineEigenvalue n) * a n) •
            cosineModeBCF n) x by
        simpa [intervalSpectralGeneratorBCF] using hmap]
  unfold unitIntervalCosineHeatSecondValue
  rw [← tsum_neg]
  exact tsum_congr (fun n => by
    change (unitIntervalCosineEigenvalue n *
        Real.exp (-u * unitIntervalCosineEigenvalue n) * a n) *
          cosineMode n x = _
    simp only [unitIntervalCosineHeatSecondPointWeight,
      unitIntervalCosineEigenvalue, cosineMode]
    ring)

/-- The spectral generator is continuous in the additional subordination time
on the whole closed half-line. -/
theorem intervalSpectralGeneratorBCF_continuousOn
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    ContinuousOn
      (fun s : ℝ => intervalSpectralGeneratorBCF (t + s) a)
      (Set.Ici 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg (a 0)).trans (hM 0)
  have hbase :=
    ShenWork.IntervalRestartDerivJointContinuity.eigenvalue_mul_exp_summable ht
  unfold intervalSpectralGeneratorBCF
  apply continuousOn_tsum
    (fun n => (by fun_prop : ContinuousOn
      (fun s : ℝ =>
        (unitIntervalCosineEigenvalue n *
          Real.exp (-(t + s) * unitIntervalCosineEigenvalue n) * a n) •
            cosineModeBCF n) (Set.Ici 0)))
    (hbase.mul_left M)
  intro n s hs
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by unfold unitIntervalCosineEigenvalue; positivity),
    abs_of_nonneg (Real.exp_nonneg _)]
  have hmode := cosineModeBCF_norm_le_one n
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hexp :
      Real.exp (-(t + s) * unitIntervalCosineEigenvalue n) ≤
        Real.exp (-t * unitIntervalCosineEigenvalue n) := by
    apply Real.exp_le_exp_of_le
    have hs0 : 0 ≤ s := hs
    nlinarith [mul_nonneg hs0 hlam]
  have hweight0 : 0 ≤ unitIntervalCosineEigenvalue n *
      Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    mul_nonneg hlam (Real.exp_nonneg _)
  calc
    unitIntervalCosineEigenvalue n *
          Real.exp (-(t + s) * unitIntervalCosineEigenvalue n) * |a n| *
        ‖cosineModeBCF n‖
      ≤ unitIntervalCosineEigenvalue n *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * |a n| *
            ‖cosineModeBCF n‖ := by
        gcongr
    _ ≤ unitIntervalCosineEigenvalue n *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * M *
            ‖cosineModeBCF n‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM n) hweight0) (norm_nonneg _)
    _ ≤ unitIntervalCosineEigenvalue n *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * M * 1 :=
        mul_le_mul_of_nonneg_left hmode (mul_nonneg hweight0 hM0)
    _ = M * (unitIntervalCosineEigenvalue n *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring

/-- The same spectral generator, mapped continuously into the physical
`Lp([0,1])` space. -/
def intervalSpectralGeneratorLp
    (q u : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (a : ℕ → ℝ) :
    Lp ℝ (ENNReal.ofReal q) (intervalMeasure 1) :=
  BoundedContinuousFunction.toLp (ENNReal.ofReal q) (intervalMeasure 1) ℝ
    (intervalSpectralGeneratorBCF u a)

theorem intervalSpectralGeneratorLp_continuousOn
    {q t : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (ht : 0 < t)
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    ContinuousOn
      (fun s : ℝ => intervalSpectralGeneratorLp q (t + s) a)
      (Set.Ici 0) := by
  simpa [intervalSpectralGeneratorLp, Function.comp_def] using
    (BoundedContinuousFunction.toLp
      (ENNReal.ofReal q) (intervalMeasure 1) ℝ).continuous.comp_continuousOn
        (intervalSpectralGeneratorBCF_continuousOn ht hM)

/-- The spectral `Lp` realization inherits the physical full-`q` generator
estimate through the Hessian-kernel/spectral identification above. -/
theorem intervalSpectralGeneratorLp_norm_le
    {q r u : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hu : 0 < u) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    ‖intervalSpectralGeneratorLp q u (cosineCoeffs f)‖ ≤
      (fullGeneratorKernelConstant * u ^ (-(1 : ℝ))) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hrq.symm.lt.le
  have hfint : Integrable f (intervalMeasure 1) :=
    memLp_one_iff_integrable.mp (hf.mono_exponent h1q)
  let M : ℝ := 2 * ∫ y, ‖f y‖ ∂(intervalMeasure 1)
  have hM : ∀ n, |cosineCoeffs f n| ≤ M :=
    cosineCoeffs_abs_le_two_integral_norm hfint
  let B : ℝ →ᵇ ℝ := intervalSpectralGeneratorBCF u (cosineCoeffs f)
  let G : Lp ℝ (ENNReal.ofReal q) (intervalMeasure 1) :=
    intervalSpectralGeneratorLp q u (cosineCoeffs f)
  have hpoint : ∀ x, B x = intervalFullGeneratorHeatOperator u f x := by
    intro x
    exact (intervalSpectralGeneratorBCF_apply hu hM x).trans
      (intervalFullGeneratorHeatOperator_eq_neg_secondValue hu hfint x).symm
  have hcoe : (G : ℝ → ℝ) =ᵐ[intervalMeasure 1] B := by
    simpa [G, B, intervalSpectralGeneratorLp] using
      (BoundedContinuousFunction.coeFn_toLp
        (ENNReal.ofReal q) (intervalMeasure 1) ℝ B)
  have hGgen : (G : ℝ → ℝ) =ᵐ[intervalMeasure 1]
      intervalFullGeneratorHeatOperator u f :=
    hcoe.trans (Filter.Eventually.of_forall hpoint)
  have hgenMem : MemLp (intervalFullGeneratorHeatOperator u f)
      (ENNReal.ofReal q) (intervalMeasure 1) :=
    (Lp.memLp G).ae_eq hGgen
  calc
    ‖intervalSpectralGeneratorLp q u (cosineCoeffs f)‖ =
        (eLpNorm (G : ℝ → ℝ) (ENNReal.ofReal q)
          (intervalMeasure 1)).toReal := by
      simpa [G] using MeasureTheory.Lp.norm_def G
    _ = (eLpNorm (intervalFullGeneratorHeatOperator u f)
          (ENNReal.ofReal q) (intervalMeasure 1)).toReal := by
      rw [eLpNorm_congr_ae hGgen]
    _ = lpNorm (intervalFullGeneratorHeatOperator u f)
          (ENNReal.ofReal q) (intervalMeasure 1) :=
      toReal_eLpNorm hgenMem.aestronglyMeasurable
    _ ≤ (fullGeneratorKernelConstant * u ^ (-(1 : ℝ))) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) :=
      intervalFullGeneratorHeatOperator_lpNorm_le hu hrq hf

/-! ## Fractional operator and the full-`q` estimate -/

/-- The fractional Neumann heat operator as an absolutely convergent
`Lp`-valued derivative-subordination integral.  The proof argument records
that the `Lp` exponent is at least one, as required by the Banach structure. -/
def intervalFractionalNeumannLp
    (sigma t q : ℝ) (hq : 1 ≤ ENNReal.ofReal q) (f : ℝ → ℝ) :
    Lp ℝ (ENNReal.ofReal q) (intervalMeasure 1) := by
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨hq⟩
  exact fractionalDerivativeBochner sigma
    (fun s => intervalSpectralGeneratorLp q (t + s) (cosineCoeffs f))

/-- **Fractional full-`q` Neumann semigroup estimate.**  For every
`0 < sigma < 1` and every conjugate pair `r,q` (hence `1 < q < infinity`),

`norm ((-Delta_N)^sigma exp(t Delta_N) f)_q`

is at most an explicit constant times `t^(-sigma) norm(f)_q`.

No multiplier theorem or functional calculus is used: only the integer
generator Schur bound, the scalar Gamma integral, and Bochner Minkowski. -/
theorem intervalFractionalNeumannLp_norm_le
    {sigma t q r : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    ‖intervalFractionalNeumannLp sigma t q
        (by simpa using ENNReal.ofReal_le_ofReal hrq.symm.lt.le) f‖ ≤
      fractionalSubordinationConstant sigma * fullGeneratorKernelConstant *
        (1 / (1 - sigma) + 1 / sigma) * t ^ (-sigma) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  have hqFact : 1 ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hrq.symm.lt.le
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨hqFact⟩
  have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := hqFact
  have hfint : Integrable f (intervalMeasure 1) :=
    memLp_one_iff_integrable.mp (hf.mono_exponent h1q)
  let M : ℝ := 2 * ∫ y, ‖f y‖ ∂(intervalMeasure 1)
  have hM : ∀ n, |cosineCoeffs f n| ≤ M :=
    cosineCoeffs_abs_le_two_integral_norm hfint
  let F : ℝ → Lp ℝ (ENNReal.ofReal q) (intervalMeasure 1) :=
    fun s => intervalSpectralGeneratorLp q (t + s) (cosineCoeffs f)
  have hFcont : ContinuousOn F (Set.Ici 0) := by
    simpa [F] using intervalSpectralGeneratorLp_continuousOn
      (q := q) ht hM
  have hscont : ContinuousOn (fun s : ℝ => s ^ (-sigma)) (Set.Ioi 0) := by
    exact continuousOn_id.rpow_const
      (fun s hs => Or.inl (Set.mem_Ioi.mp hs).ne')
  have hweighted : ContinuousOn (fun s : ℝ => s ^ (-sigma) • F s)
      (Set.Ioi 0) :=
    hscont.smul (hFcont.mono Set.Ioi_subset_Ici_self)
  have hFmeas : AEStronglyMeasurable
      (fun s : ℝ => s ^ (-sigma) • F s)
      (volume.restrict (Set.Ioi 0)) :=
    hweighted.aestronglyMeasurable measurableSet_Ioi
  have hFbound : ∀ s, 0 < s →
      ‖F s‖ ≤ fullGeneratorKernelConstant *
        (t + s) ^ (-(1 : ℝ)) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
    intro s hs
    simpa [F, mul_assoc] using
      intervalSpectralGeneratorLp_norm_le (q := q) (r := r)
        (by linarith : 0 < t + s) hrq hf
  have hmain := norm_fractionalDerivativeBochner_le
    (E := Lp ℝ (ENNReal.ofReal q) (intervalMeasure 1))
    hsigma0 hsigma1 ht fullGeneratorKernelConstant_pos.le lpNorm_nonneg
    F hFmeas hFbound
  simpa [intervalFractionalNeumannLp, F] using hmain

/-- Mode-by-mode specialization of the scalar Gamma identity to every Neumann
eigenvalue `((n*pi)^2)`, including the constant mode. -/
theorem neumannMode_fractional_subordination
    {sigma t : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (n : ℕ) :
    fractionalSubordinationConstant sigma *
        (∫ s : ℝ in Set.Ioi 0,
          fractionalHeatDerivativeIntegrand sigma t
            (unitIntervalCosineEigenvalue n) s) =
      (unitIntervalCosineEigenvalue n) ^ sigma *
        Real.exp (-(t * unitIntervalCosineEigenvalue n)) := by
  apply fractionalHeat_subordination_scalar_nonneg hsigma0 hsigma1
  unfold unitIntervalCosineEigenvalue
  positivity

#print axioms intervalFullGeneratorHeatOperator_eq_neg_secondValue
#print axioms intervalSpectralGeneratorLp_norm_le
#print axioms intervalFractionalNeumannLp_norm_le
#print axioms neumannMode_fractional_subordination

end ShenWork.Paper2.IntervalFractionalSubordinationFullQ
