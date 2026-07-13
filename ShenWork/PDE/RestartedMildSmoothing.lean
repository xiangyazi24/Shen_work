/-
# Restarted mild smoothing: shared closure core

This file contains the problem-independent part of the restarted Duhamel
argument used by Paper 2 and Paper 3.  There are deliberately two exit doors:

* `bochner_mild_affine_bound` is an affine estimate and needs no smallness;
* `superlinear_closedBall_fixedPoint` is the Banach fixed-point exit and needs
  a strict superlinear smallness inequality.

The semigroup, source, and trajectory spaces are supplied by the application.
The strict inequality in the second exit is essential: a non-strict bound that
allows contraction factor one is not enough for Banach's theorem.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Topology.MetricSpace.Contracting

namespace ShenWork.PDE

open MeasureTheory Set

noncomputable section

/-! ## L1: singular-kernel calculus -/

/-- The standard analytic-semigroup smoothing majorant. -/
def restartedSmoothingKernel (C theta nu r : ℝ) : ℝ :=
  C * (1 + r ^ (-theta)) * Real.exp (-nu * r)

/-- Finite-window mass when no exponential gap is available. -/
def restartedKernelMassZero (C theta T : ℝ) : ℝ :=
  C * (T + T ^ (1 - theta) / (1 - theta))

/-- Uniform infinite-window mass when the semigroup has a positive gap. -/
def restartedKernelMassPositive (C theta nu : ℝ) : ℝ :=
  C * (1 / nu + nu ^ (theta - 1) * Real.Gamma (1 - theta))

/-- The order-`theta` singularity is integrable on every finite time window
exactly in the range used by the two applications, `theta < 1`. -/
theorem rpow_neg_intervalIntegrable
    {theta a b : ℝ} (htheta : theta < 1) :
    IntervalIntegrable (fun r : ℝ => r ^ (-theta)) volume a b := by
  exact intervalIntegral.intervalIntegrable_rpow' (by linarith)

/-- Exact finite-window integral of the singular factor. -/
theorem integral_rpow_neg
    {theta T : ℝ} (htheta : theta < 1) (_hT : 0 ≤ T) :
    (∫ r in (0 : ℝ)..T, r ^ (-theta)) =
      T ^ (1 - theta) / (1 - theta) := by
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -theta))]
  have hne : (1 - theta : ℝ) ≠ 0 := by linarith
  rw [show -theta + 1 = 1 - theta by ring,
    Real.zero_rpow hne, sub_zero]

/-- L1, zero-gap branch: the exact kernel mass on `[0,T]`. -/
theorem restartedSmoothingKernel_integral_zero
    {C theta T : ℝ} (htheta : theta < 1) (hT : 0 ≤ T) :
    (∫ r in (0 : ℝ)..T, restartedSmoothingKernel C theta 0 r) =
      restartedKernelMassZero C theta T := by
  have hpow : IntervalIntegrable (fun r : ℝ => r ^ (-theta)) volume 0 T :=
    rpow_neg_intervalIntegrable htheta
  have hCconst : IntervalIntegrable (fun _r : ℝ => C) volume 0 T :=
    intervalIntegral.intervalIntegrable_const
  have hCpow : IntervalIntegrable (fun r : ℝ => C * r ^ (-theta)) volume 0 T :=
    hpow.const_mul C
  simp only [restartedSmoothingKernel, zero_mul, neg_zero, Real.exp_zero, mul_one,
    mul_add]
  rw [intervalIntegral.integral_add hCconst hCpow,
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    integral_rpow_neg htheta hT]
  simp only [restartedKernelMassZero]
  simp only [smul_eq_mul]
  ring

/-- Integrability on the positive half-line of the singular exponential
factor. -/
theorem rpow_neg_mul_exp_integrableOn_Ioi
    {theta nu : ℝ} (_htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hnu : 0 < nu) :
    IntegrableOn (fun r : ℝ => r ^ (-theta) * Real.exp (-nu * r))
      (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := -theta) (b := nu)
    (by linarith) (by norm_num) hnu
  simpa only [Real.rpow_one, neg_mul] using h

/-- Gamma evaluation of the singular exponential mass. -/
theorem integral_rpow_neg_mul_exp_Ioi
    {theta nu : ℝ} (_htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hnu : 0 < nu) :
    (∫ r in Set.Ioi (0 : ℝ),
      r ^ (-theta) * Real.exp (-nu * r)) =
        nu ^ (theta - 1) * Real.Gamma (1 - theta) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := -theta) (b := nu)
    (by norm_num) (by linarith) hnu
  norm_num [Real.rpow_one] at h
  simpa only [neg_mul, show -1 + theta = theta - 1 by ring,
    show -theta + 1 = 1 - theta by ring,
    show -(1 - theta) = theta - 1 by ring] using h

/-- L1, positive-gap branch: the kernel mass is uniformly bounded on every
finite window by its explicit infinite-time Gamma mass. -/
theorem restartedSmoothingKernel_integral_le_positive
    {C theta nu T : ℝ}
    (hC : 0 ≤ C) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hnu : 0 < nu) (hT : 0 ≤ T) :
    (∫ r in (0 : ℝ)..T, restartedSmoothingKernel C theta nu r) ≤
      restartedKernelMassPositive C theta nu := by
  let f0 : ℝ → ℝ := fun r => Real.exp (-nu * r)
  let ftheta : ℝ → ℝ := fun r => r ^ (-theta) * Real.exp (-nu * r)
  have hf0 : IntegrableOn f0 (Set.Ioi 0) := by
    simpa [f0, neg_mul] using integrableOn_exp_mul_Ioi (a := -nu) (by linarith) 0
  have hftheta : IntegrableOn ftheta (Set.Ioi 0) := by
    simpa [ftheta] using
      rpow_neg_mul_exp_integrableOn_Ioi htheta0 htheta1 hnu
  have hsum : IntegrableOn (fun r => f0 r + ftheta r) (Set.Ioi 0) :=
    hf0.add hftheta
  have hnonneg : ∀ᵐ r ∂volume.restrict (Set.Ioi 0),
      0 ≤ f0 r + ftheta r := by
    refine (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun r hr => ?_)
    exact add_nonneg (Real.exp_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _))
  have hsubset : Set.Ioc (0 : ℝ) T ⊆ Set.Ioi 0 := fun _ hr => hr.1
  have hmono :
      (∫ r in (0 : ℝ)..T, f0 r + ftheta r) ≤
        ∫ r in Set.Ioi (0 : ℝ), f0 r + ftheta r := by
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hsum hnonneg
      (Filter.Eventually.of_forall hsubset)
  have hf0eq : (∫ r in Set.Ioi (0 : ℝ), f0 r) = 1 / nu := by
    calc
      (∫ r in Set.Ioi (0 : ℝ), f0 r) =
          -Real.exp ((-nu) * 0) / (-nu) := by
        simpa [f0] using integral_exp_mul_Ioi (a := -nu) (by linarith) 0
      _ = 1 / nu := by
        rw [mul_zero, Real.exp_zero]
        field_simp
  have hfthetaeq : (∫ r in Set.Ioi (0 : ℝ), ftheta r) =
      nu ^ (theta - 1) * Real.Gamma (1 - theta) := by
    simpa [ftheta] using
      integral_rpow_neg_mul_exp_Ioi htheta0 htheta1 hnu
  have hinside : ∀ r,
      restartedSmoothingKernel C theta nu r = C * (f0 r + ftheta r) := by
    intro r
    dsimp [restartedSmoothingKernel, f0, ftheta]
    ring
  simp_rw [hinside]
  rw [intervalIntegral.integral_const_mul]
  calc
    C * (∫ r in (0 : ℝ)..T, f0 r + ftheta r) ≤
        C * (∫ r in Set.Ioi (0 : ℝ), f0 r + ftheta r) :=
      mul_le_mul_of_nonneg_left hmono hC
    _ = C * ((∫ r in Set.Ioi (0 : ℝ), f0 r) +
        ∫ r in Set.Ioi (0 : ℝ), ftheta r) := by
      rw [MeasureTheory.integral_add hf0 hftheta]
    _ = restartedKernelMassPositive C theta nu := by
      rw [hf0eq, hfthetaeq]
      rfl

/-- The positive-gap smoothing kernel is interval-integrable on every finite
window. -/
theorem restartedSmoothingKernel_intervalIntegrable_positive
    {C theta nu T : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hnu : 0 < nu) (hT : 0 ≤ T) :
    IntervalIntegrable (restartedSmoothingKernel C theta nu) volume 0 T := by
  let f0 : ℝ → ℝ := fun r => Real.exp (-nu * r)
  let ftheta : ℝ → ℝ := fun r => r ^ (-theta) * Real.exp (-nu * r)
  have hf0 : IntegrableOn f0 (Set.Ioi 0) := by
    simpa [f0, neg_mul] using integrableOn_exp_mul_Ioi (a := -nu) (by linarith) 0
  have hftheta : IntegrableOn ftheta (Set.Ioi 0) := by
    simpa [ftheta] using
      rpow_neg_mul_exp_integrableOn_Ioi htheta0 htheta1 hnu
  have hkernelIoi : IntegrableOn (restartedSmoothingKernel C theta nu)
      (Set.Ioi 0) := by
    have hsum := (hf0.add hftheta).const_mul C
    refine IntegrableOn.congr_fun
      (f := fun r => C * (f0 r + ftheta r))
      (g := restartedSmoothingKernel C theta nu)
      (s := Set.Ioi 0) hsum ?_ measurableSet_Ioi
    intro r _hr
    dsimp [restartedSmoothingKernel, f0, ftheta]
    ring
  have hkernelIci : IntegrableOn (restartedSmoothingKernel C theta nu)
      (Set.Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hkernelIoi
  have huIcc : Set.uIcc (0 : ℝ) T ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hT]
    exact fun _r hr => hr.1
  exact (hkernelIci.mono_set huIcc).intervalIntegrable

/-! ## L2: weighted convolution with a reserved decay rate -/

/-- Weighted convolution for the singular smoothing kernel.  The desired
output rate is reserved strictly below the semigroup gap.  This is the honest
form used by the nonlinear stability proof: taking the output rate equal to
the gap would leave no exponential mass in the elapsed-time kernel. -/
theorem weightedConvolution_le_reservedRate
    {C theta omega rate eps t : ℝ}
    (hC : 0 ≤ C) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hrate : 0 < rate) (hrateomega : rate < omega)
    (heps : 0 ≤ eps) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        restartedSmoothingKernel C theta omega (t - s) *
          Real.exp (-(1 + eps) * rate * s)) ≤
      Real.exp (-rate * t) *
        restartedKernelMassPositive C theta (omega - rate) := by
  let source : ℝ → ℝ := fun s =>
    restartedSmoothingKernel C theta omega (t - s) *
      Real.exp (-(1 + eps) * rate * s)
  let major : ℝ → ℝ := fun s =>
    Real.exp (-rate * t) *
      restartedSmoothingKernel C theta (omega - rate) (t - s)
  have hgap : 0 < omega - rate := sub_pos.mpr hrateomega
  have hkernelInt := restartedSmoothingKernel_intervalIntegrable_positive
    (C := C) htheta0 htheta1 hgap ht
  have hcompInt : IntervalIntegrable
      (fun s => restartedSmoothingKernel C theta (omega - rate) (t - s))
      volume 0 t := by
    simpa using (hkernelInt.comp_sub_left t).symm
  have hmajorInt : IntervalIntegrable major volume 0 t :=
    hcompInt.const_mul (Real.exp (-rate * t))
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) t, source s ≤ major s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hr0 : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hextra : Real.exp (-eps * rate * s) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hprod : 0 ≤ eps * rate * s :=
        mul_nonneg (mul_nonneg heps hrate.le) hs0
      nlinarith
    have hexpEq :
        Real.exp (-omega * (t - s)) *
            Real.exp (-(1 + eps) * rate * s) =
          Real.exp (-rate * t) *
            Real.exp (-(omega - rate) * (t - s)) *
              Real.exp (-eps * rate * s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hbase0 : 0 ≤
        C * (1 + (t - s) ^ (-theta)) :=
      mul_nonneg hC
        (add_nonneg zero_le_one (Real.rpow_nonneg hr0 _))
    dsimp [source, major, restartedSmoothingKernel]
    rw [show
      (C * (1 + (t - s) ^ (-theta)) * Real.exp (-omega * (t - s))) *
          Real.exp (-(1 + eps) * rate * s) =
        C * (1 + (t - s) ^ (-theta)) *
          (Real.exp (-omega * (t - s)) *
            Real.exp (-(1 + eps) * rate * s)) by ring,
      hexpEq]
    calc
      C * (1 + (t - s) ^ (-theta)) *
          (Real.exp (-rate * t) *
            Real.exp (-(omega - rate) * (t - s)) *
              Real.exp (-eps * rate * s)) ≤
        C * (1 + (t - s) ^ (-theta)) *
          (Real.exp (-rate * t) *
            Real.exp (-(omega - rate) * (t - s)) * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hextra
              (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))) hbase0
      _ = Real.exp (-rate * t) *
          (C * (1 + (t - s) ^ (-theta)) *
            Real.exp (-(omega - rate) * (t - s))) := by ring
  have hsourceMeas : AEStronglyMeasurable source
      (volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [source, restartedSmoothingKernel]
    fun_prop
  have hsourceInt : IntervalIntegrable source volume 0 t := by
    apply hmajorInt.mono_fun
    · exact hsourceMeas
    · refine (ae_restrict_iff' measurableSet_uIoc).2
        (Filter.Eventually.of_forall fun s hs => ?_)
      have hsIcc : s ∈ Set.Icc (0 : ℝ) t := by
        rw [Set.uIoc_of_le ht] at hs
        exact ⟨le_of_lt hs.1, hs.2⟩
      have hsource0 : 0 ≤ source s := by
        dsimp [source, restartedSmoothingKernel]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg hC
              (add_nonneg zero_le_one
                (Real.rpow_nonneg (sub_nonneg.mpr hsIcc.2) _)))
            (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      have hmajor0 : 0 ≤ major s := by
        dsimp [major, restartedSmoothingKernel]
        exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg
            (mul_nonneg hC
              (add_nonneg zero_le_one
                (Real.rpow_nonneg (sub_nonneg.mpr hsIcc.2) _)))
            (Real.exp_nonneg _))
      simpa [Real.norm_eq_abs, abs_of_nonneg hsource0,
        abs_of_nonneg hmajor0] using hpoint s hsIcc
  have hmono : (∫ s in (0 : ℝ)..t, source s) ≤
      ∫ s in (0 : ℝ)..t, major s :=
    intervalIntegral.integral_mono_on ht hsourceInt hmajorInt hpoint
  have hmajorEq : (∫ s in (0 : ℝ)..t, major s) =
      Real.exp (-rate * t) *
        ∫ r in (0 : ℝ)..t,
          restartedSmoothingKernel C theta (omega - rate) r := by
    dsimp [major]
    rw [intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  have hmass := restartedSmoothingKernel_integral_le_positive
    hC htheta0 htheta1 hgap ht
  calc
    (∫ s in (0 : ℝ)..t,
        restartedSmoothingKernel C theta omega (t - s) *
          Real.exp (-(1 + eps) * rate * s)) =
        ∫ s in (0 : ℝ)..t, source s := rfl
    _ ≤ ∫ s in (0 : ℝ)..t, major s := hmono
    _ = Real.exp (-rate * t) *
        ∫ r in (0 : ℝ)..t,
          restartedSmoothingKernel C theta (omega - rate) r := hmajorEq
    _ ≤ Real.exp (-rate * t) *
        restartedKernelMassPositive C theta (omega - rate) :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)

/-! ## Bochner-Duhamel norm extraction -/

/-- Taking the norm in a vector-valued Duhamel formula.  This is the common
Bochner-integral glue; all application-specific smoothing estimates enter only
through `hpoint`. -/
theorem bochner_mild_norm_le
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {w linear integrand : ℝ → Z} {major : ℝ → ℝ} {t L : ℝ}
    (ht : 0 ≤ t)
    (hmild : w t = linear t + ∫ s in (0 : ℝ)..t, integrand s)
    (hlinear : ‖linear t‖ ≤ L)
    (hmajor : IntervalIntegrable major volume 0 t)
    (hpoint : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖integrand s‖ ≤ major s) :
    ‖w t‖ ≤ L + ∫ s in (0 : ℝ)..t, major s := by
  rw [hmild]
  refine (norm_add_le _ _).trans (add_le_add hlinear ?_)
  exact intervalIntegral.norm_integral_le_of_norm_le ht
    (Filter.Eventually.of_forall fun s hs => hpoint s hs) hmajor

/-- L3a, the affine exit.  Once the forcing has a constant bound, a mild
trajectory is controlled by the kernel mass.  There is no smallness
assumption and no fixed-point argument in this branch. -/
theorem bochner_mild_affine_bound
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {w linear integrand : ℝ → Z} {kernel : ℝ → ℝ}
    {t M datum Lambda Kzero : ℝ}
    (ht : 0 ≤ t)
    (hmild : w t = linear t + ∫ s in (0 : ℝ)..t, integrand s)
    (hlinear : ‖linear t‖ ≤ M * datum)
    (hkernel : IntervalIntegrable kernel volume 0 t)
    (hpoint : ∀ s ∈ Set.Ioc (0 : ℝ) t,
      ‖integrand s‖ ≤ Lambda * kernel s)
    (hLambda : 0 ≤ Lambda)
    (hkernelMass : (∫ s in (0 : ℝ)..t, kernel s) ≤ Kzero) :
    ‖w t‖ ≤ M * datum + Lambda * Kzero := by
  have hscaledInt : IntervalIntegrable (fun s => Lambda * kernel s) volume 0 t :=
    hkernel.const_mul Lambda
  have hnorm := bochner_mild_norm_le ht hmild hlinear hscaledInt hpoint
  calc
    ‖w t‖ ≤ M * datum + ∫ s in (0 : ℝ)..t, Lambda * kernel s := hnorm
    _ = M * datum + Lambda * ∫ s in (0 : ℝ)..t, kernel s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ M * datum + Lambda * Kzero :=
      add_le_add_right (mul_le_mul_of_nonneg_left hkernelMass hLambda) _

/-! ## The superlinear Banach exit -/

/-- Data needed after the singular Bochner convolution has been estimated on
a closed trajectory ball.  The exponent is a natural number because the P3
nonlinearity is quadratic; this avoids hiding any real-power side conditions.

`map_bound` is the Duhamel self-map estimate and `difference_bound` is the
corresponding local Lipschitz estimate. -/
structure SuperlinearClosedBallData
    {X : Type*} [MetricSpace X]
    (F : X → X) (center : X) where
  order : ℕ
  M : ℝ
  datum : ℝ
  Lambda : ℝ
  kernelMass : ℝ
  radius : ℝ
  localRadius : ℝ
  order_pos : 0 < order
  M_nonneg : 0 ≤ M
  datum_nonneg : 0 ≤ datum
  Lambda_nonneg : 0 ≤ Lambda
  kernelMass_nonneg : 0 ≤ kernelMass
  radius_pos : 0 < radius
  localRadius_pos : 0 < localRadius
  radius_le_localRadius : radius ≤ localRadius
  radius_eq : radius = 2 * M * datum
  superlinear_small :
    Lambda * kernelMass * radius ^ order < 1 / 2
  map_bound : ∀ x ∈ Metric.closedBall center radius,
    dist (F x) center ≤
      M * datum + Lambda * kernelMass * radius ^ (order + 1)
  difference_bound : ∀ x ∈ Metric.closedBall center radius,
    ∀ y ∈ Metric.closedBall center radius,
      dist (F x) (F y) ≤
        (2 * Lambda * kernelMass * radius ^ order) * dist x y

namespace SuperlinearClosedBallData

variable {X : Type*} [MetricSpace X]
  {F : X → X} {center : X}

private theorem contractionFactor_nonneg
    (D : SuperlinearClosedBallData F center) :
    0 ≤ 2 * D.Lambda * D.kernelMass * D.radius ^ D.order := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) D.Lambda_nonneg)
      D.kernelMass_nonneg)
    (pow_nonneg D.radius_pos.le _)

private theorem contractionFactor_lt_one
    (D : SuperlinearClosedBallData F center) :
    2 * D.Lambda * D.kernelMass * D.radius ^ D.order < 1 := by
  nlinarith [D.superlinear_small]

/-- The Duhamel map sends the strong trajectory ball to itself. -/
theorem mapsTo (D : SuperlinearClosedBallData F center) :
    MapsTo F (Metric.closedBall center D.radius)
      (Metric.closedBall center D.radius) := by
  intro x hx
  rw [Metric.mem_closedBall]
  have hmap := D.map_bound x hx
  have hhalf :
      D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) <
        D.radius / 2 := by
    have hr0 : 0 ≤ D.radius := D.radius_pos.le
    have hmul := mul_lt_mul_of_pos_right D.superlinear_small D.radius_pos
    calc
      D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) =
          (D.Lambda * D.kernelMass * D.radius ^ D.order) * D.radius := by
            rw [pow_succ]
            ring
      _ < (1 / 2) * D.radius := hmul
      _ = D.radius / 2 := by ring
  have hdatum : D.M * D.datum = D.radius / 2 := by
    rw [D.radius_eq]
    ring
  have hlt : dist (F x) center < D.radius := by
    calc
      dist (F x) center ≤ D.M * D.datum +
          D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) := hmap
      _ = D.radius / 2 +
          D.Lambda * D.kernelMass * D.radius ^ (D.order + 1) := by rw [hdatum]
      _ < D.radius / 2 + D.radius / 2 := add_lt_add_right hhalf _
      _ = D.radius := by ring
  exact hlt.le

/-- The restricted Duhamel map is a genuine Mathlib contraction. -/
theorem contracting (D : SuperlinearClosedBallData F center) :
    ContractingWith
      (2 * D.Lambda * D.kernelMass * D.radius ^ D.order).toNNReal
      (D.mapsTo.restrict F (Metric.closedBall center D.radius)
        (Metric.closedBall center D.radius)) := by
  refine ⟨Real.toNNReal_lt_one.mpr D.contractionFactor_lt_one, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq,
    MapsTo.val_restrict_apply, MapsTo.val_restrict_apply]
  rw [Real.coe_toNNReal _ D.contractionFactor_nonneg]
  exact D.difference_bound x x.2 y y.2

/-- L3b, the superlinear exit.  A strict smallness inequality makes the
singular Duhamel self-map invariant and contracting, hence produces a unique
mild fixed point in the strong trajectory ball. -/
theorem fixedPoint [CompleteSpace X]
    (D : SuperlinearClosedBallData F center) :
    ∃ y ∈ Metric.closedBall center D.radius,
      Function.IsFixedPt F y ∧
      ∀ z ∈ Metric.closedBall center D.radius,
        Function.IsFixedPt F z → z = y := by
  let B : Set X := Metric.closedBall center D.radius
  have hBc : IsComplete B := Metric.isClosed_closedBall.isComplete
  have hcenter : center ∈ B := by
    exact Metric.mem_closedBall_self D.radius_pos.le
  have hedist : edist center (F center) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y, hyB, hyfix, _hyconv, _hyrate⟩ :=
    D.contracting.exists_fixedPoint' hBc D.mapsTo hcenter hedist
  refine ⟨y, hyB, hyfix, ?_⟩
  intro z hzB hzfix
  let ys : B := ⟨y, hyB⟩
  let zs : B := ⟨z, hzB⟩
  have hysfix : Function.IsFixedPt
      (D.mapsTo.restrict F B B) ys := by
    apply Subtype.ext
    exact hyfix
  have hzsfix : Function.IsFixedPt
      (D.mapsTo.restrict F B B) zs := by
    apply Subtype.ext
    exact hzfix
  have hsub : zs = ys := D.contracting.fixedPoint_unique' hzsfix hysfix
  exact congrArg Subtype.val hsub

end SuperlinearClosedBallData

/-! ## L4: restart glue -/

/-- A uniform datum bound and a uniform estimate on every restarted window
give a uniform tail estimate.  Applications normally take `window = 1` and
restart a trajectory at `t - 1`. -/
theorem restartGlue
    {size datum : ℝ → ℝ} {K B window : ℝ}
    (hwindow : 0 < window)
    (hdatum : ∀ r, 0 ≤ r → datum r ≤ K)
    (hlocal : ∀ r, 0 ≤ r → datum r ≤ K →
      ∀ tau, 0 ≤ tau → tau ≤ window → size (r + tau) ≤ B) :
    ∀ t, window ≤ t → size t ≤ B := by
  intro t ht
  let r := t - window
  have hr : 0 ≤ r := sub_nonneg.mpr ht
  have h := hlocal r hr (hdatum r hr) window hwindow.le le_rfl
  simpa [r] using h

/-- A continuous first-exit bootstrap on a compact time interval.

The hypothesis `himprove` is the usual restarted-mild estimate: assuming the
trajectory stays in the radius-`q` tube up to a time `r`, the estimate improves
the whole prefix to radius `q / 2`.  Continuity then rules out a first exit.

The proof uses the continuous running maximum
`r ↦ max_{x ∈ [0,1]} size (r*x)`.  This avoids choosing a least exit time and
is reusable for weak-norm basin-entry arguments. -/
theorem continuousPrefixBootstrap
    {size : ℝ → ℝ} {T q : ℝ}
    (hsize : Continuous size) (hT : 0 ≤ T) (hq : 0 < q)
    (hzero : size 0 ≤ q / 2)
    (himprove : ∀ r, 0 ≤ r → r ≤ T →
      (∀ s, 0 ≤ s → s ≤ r → size s ≤ q) →
        ∀ s, 0 ≤ s → s ≤ r → size s ≤ q / 2) :
    ∀ t, 0 ≤ t → t ≤ T → size t ≤ q / 2 := by
  let runningMax : ℝ → ℝ := fun r =>
    sSup ((fun x : ℝ => size (r * x)) '' Set.Icc (0 : ℝ) 1)
  have hrunning : Continuous runningMax := by
    dsimp [runningMax]
    apply isCompact_Icc.continuous_sSup
    fun_prop
  have hrunning_zero : runningMax 0 = size 0 := by
    simp [runningMax]
  have hle_running : ∀ {r s : ℝ}, 0 ≤ r → 0 ≤ s → s ≤ r →
      size s ≤ runningMax r := by
    intro r s hr hs hsr
    by_cases hr0 : r = 0
    · subst r
      have hs0 : s = 0 := by linarith
      subst s
      rw [hrunning_zero]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hx : s / r ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hs hr
        · exact (div_le_one hrpos).2 hsr
      have hcont : Continuous fun x : ℝ => size (r * x) := by fun_prop
      have hbdd : BddAbove
          ((fun x : ℝ => size (r * x)) '' Set.Icc (0 : ℝ) 1) :=
        isCompact_Icc.bddAbove_image hcont.continuousOn
      have hmem : size s ∈
          (fun x : ℝ => size (r * x)) '' Set.Icc (0 : ℝ) 1 := by
        refine ⟨s / r, hx, ?_⟩
        field_simp
      exact le_csSup hbdd hmem
  have hglobal : ∀ t, 0 ≤ t → t ≤ T → size t ≤ q := by
    intro t ht htT
    by_contra hnot
    have hqt : q < size t := lt_of_not_ge hnot
    have hrun_t : q < runningMax t :=
      hqt.trans_le (hle_running ht ht (le_refl t))
    have hrun_zero : runningMax 0 < q := by
      rw [hrunning_zero]
      linarith
    have hqmem : q ∈ Set.Icc (runningMax 0) (runningMax t) :=
      ⟨hrun_zero.le, hrun_t.le⟩
    obtain ⟨r, hrIcc, hrexit⟩ :=
      (intermediate_value_Icc ht hrunning.continuousOn) hqmem
    have hrpos : 0 < r := by
      have hrne : r ≠ 0 := by
        intro hre
        subst r
        rw [hrunning_zero] at hrexit
        linarith
      exact lt_of_le_of_ne hrIcc.1 (Ne.symm hrne)
    have hprefix : ∀ s, 0 ≤ s → s ≤ r → size s ≤ q := by
      intro s hs hsr
      exact (hle_running hrIcc.1 hs hsr).trans_eq hrexit
    have himproved := himprove r hrIcc.1 (hrIcc.2.trans htT) hprefix
    have hmax_le : runningMax r ≤ q / 2 := by
      dsimp [runningMax]
      apply csSup_le
      · exact ⟨size 0, ⟨0, by norm_num, by simp⟩⟩
      · intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact himproved (r * x)
          (mul_nonneg hrIcc.1 hx.1)
          (by nlinarith [hx.2, hrIcc.1])
    rw [hrexit] at hmax_le
    linarith
  exact himprove T hT (le_refl T) (fun s hs hsT => hglobal s hs hsT)

#print axioms rpow_neg_intervalIntegrable
#print axioms integral_rpow_neg
#print axioms restartedSmoothingKernel_integral_zero
#print axioms restartedSmoothingKernel_integral_le_positive
#print axioms weightedConvolution_le_reservedRate

#print axioms bochner_mild_norm_le
#print axioms bochner_mild_affine_bound
#print axioms SuperlinearClosedBallData.mapsTo
#print axioms SuperlinearClosedBallData.contracting
#print axioms SuperlinearClosedBallData.fixedPoint
#print axioms restartGlue
#print axioms continuousPrefixBootstrap

end

end ShenWork.PDE
