import ShenWork.Paper1.WholeLineCauchyHolderBootstrap
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Holder flux and whole-line Hessian cancellation

This is the second positive-time regularity rung for the whole-line Cauchy
construction.  The Hessian heat kernel has zero mass, so a spatial Holder
modulus replaces the nonintegrable `t^-1` bounded-source estimate by the
integrable `t^(-1+theta/2)` estimate.  The truncated chemotaxis flux inherits
the same Holder exponent from the population profile.
-/

/-- The whole-line heat semigroup preserves constant profiles. -/
theorem heatSemigroup_const_apply
    {t c x : ℝ} (ht : 0 < t) :
    heatSemigroup t (fun _ : ℝ => c) x = c := by
  unfold heatSemigroup
  rw [show (fun y : ℝ => heatKernel t (x - y) * c) =
      fun y : ℝ => c * heatKernel t (x - y) by
        funext y
        ring]
  rw [integral_const_mul, heatKernel_integral_translated ht, mul_one]

/-- The second spatial derivative of the whole-line heat kernel has zero
mass. -/
theorem secondDeriv_heatKernel_integral_translated_eq_zero
    {t x : ℝ} (ht : 0 < t) :
    (∫ y : ℝ,
      deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y)) = 0 := by
  have hsecond :=
    ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_second_deriv
      (f := fun _ : ℝ => (1 : ℝ)) (t := t) (x := x) (M := 1)
      ht continuous_const.aestronglyMeasurable (fun _ => by norm_num)
  have hsemigroup :
      (fun w : ℝ => heatSemigroup t (fun _ : ℝ => (1 : ℝ)) w) =
        fun _ : ℝ => (1 : ℝ) := by
    funext w
    exact heatSemigroup_const_apply ht
  have hderivZero :
      (fun z : ℝ =>
        deriv (fun w : ℝ => heatSemigroup t (fun _ : ℝ => (1 : ℝ)) w) z) =
        fun _ : ℝ => (0 : ℝ) := by
    rw [hsemigroup]
    funext z
    simp
  rw [hderivZero] at hsecond
  simpa using hsecond.deriv.symm

/-- Hessian convolution may be written after subtracting the value of the
source at the evaluation point. -/
theorem wholeLineCauchyHeatHessOp_eq_subtract
    {f : ℝ → ℝ} {t x : ℝ} (ht : 0 < t)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf_bound : ∃ M : ℝ, ∀ y, |f y| ≤ M) :
    wholeLineCauchyHeatHessOp t f x =
      Real.exp (-t) * ∫ y : ℝ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x - y) * (f y - f x) := by
  rcases hf_bound with ⟨M, hM⟩
  let K : ℝ → ℝ := fun y =>
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      (x - y)
  have hKint : Integrable K := by
    have hKmeas : AEStronglyMeasurable K volume :=
      ((ShenWork.IntervalNeumannFullKernel.continuous_secondDeriv_heatKernel ht).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    apply (integrable_norm_iff hKmeas).mp
    simpa [K, Real.norm_eq_abs, sub_eq_add_neg, add_comm] using
      ((ShenWork.IntervalNeumannFullKernel.secondDeriv_heatKernel_abs_integrable
        ht).comp_neg.comp_add_right (-x))
  have hKf : Integrable (fun y => K y * f y) := by
    exact ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
      ht x hM hf_meas
  have hKconst : Integrable (fun y => K y * f x) := hKint.mul_const _
  have hKzero : (∫ y : ℝ, K y) = 0 := by
    simpa [K] using secondDeriv_heatKernel_integral_translated_eq_zero ht
  unfold wholeLineCauchyHeatHessOp
  congr 1
  calc
    (∫ y : ℝ, K y * f y) =
        (∫ y : ℝ, K y * f y) - ∫ y : ℝ, K y * f x := by
      rw [integral_mul_const, hKzero, zero_mul, sub_zero]
    _ = ∫ y : ℝ, (K y * f y - K y * f x) := by
      rw [integral_sub hKf hKconst]
    _ = ∫ y : ℝ, K y * (f y - f x) := by
      congr 1
      funext y
      ring

/-- Whole-line cancellation estimate
`C^theta -> L∞` for the modified heat Hessian. -/
theorem wholeLineCauchyHeatHessOp_Ctheta_abs_le
    {f : ℝ → ℝ} {t theta H M x : ℝ}
    (ht : 0 < t) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hH : 0 ≤ H)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hf_holder : ∀ a b, |f a - f b| ≤ H * |a - b| ^ theta) :
    |wholeLineCauchyHeatHessOp t f x| ≤
      ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta *
        t ^ (-1 + theta / 2 : ℝ) * H := by
  let K : ℝ → ℝ := fun y =>
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      (x - y)
  have hweighted : Integrable (fun y : ℝ => |K y| * |x - y| ^ theta) := by
    have hbase :=
      ShenWork.IntervalNeumannFullKernel.heatKernel_secondDeriv_weighted_abs_integrable
        ht htheta0 htheta1
    simpa [K, sub_eq_add_neg, add_comm] using
      (hbase.comp_neg.comp_add_right (-x))
  have hsubInt : Integrable (fun y => K y * (f y - f x)) := by
    refine (hweighted.const_mul H).mono' ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · exact ((ShenWork.IntervalNeumannFullKernel.continuous_secondDeriv_heatKernel ht).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
        (hf_meas.sub aestronglyMeasurable_const)
    · rw [Real.norm_eq_abs]
      rw [abs_mul]
      calc
        |K y| * |f y - f x| ≤ |K y| * (H * |y - x| ^ theta) :=
          mul_le_mul_of_nonneg_left (hf_holder y x) (abs_nonneg _)
        _ = H * (|K y| * |x - y| ^ theta) := by
          rw [abs_sub_comm]
          ring
  rw [wholeLineCauchyHeatHessOp_eq_subtract ht hf_meas ⟨M, hf⟩,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  calc
    Real.exp (-t) * |∫ y : ℝ, K y * (f y - f x)| ≤
        |∫ y : ℝ, K y * (f y - f x)| := by
      nlinarith [abs_nonneg (∫ y : ℝ, K y * (f y - f x)), Real.exp_pos (-t)]
    _ ≤ ∫ y : ℝ, |K y * (f y - f x)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ, H * (|K y| * |x - y| ^ theta) := by
      refine integral_mono hsubInt.abs (hweighted.const_mul H) (fun y => ?_)
      rw [abs_mul]
      calc
        |K y| * |f y - f x| ≤ |K y| * (H * |y - x| ^ theta) :=
          mul_le_mul_of_nonneg_left (hf_holder y x) (abs_nonneg _)
        _ = H * (|K y| * |x - y| ^ theta) := by
          rw [abs_sub_comm]
          ring
    _ = H * ∫ y : ℝ, |K y| * |x - y| ^ theta := by
      rw [integral_const_mul]
    _ ≤ H * (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta *
          t ^ (-1 + theta / 2 : ℝ)) := by
      gcongr
      have hmass :=
        ShenWork.IntervalNeumannFullKernel.heatKernel_secondDeriv_weighted_abs_integral_le
          ht htheta0 htheta1
      let G : ℝ → ℝ := fun w =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| *
          |w| ^ theta
      have htranslate : (∫ y : ℝ, |K y| * |x - y| ^ theta) = ∫ w : ℝ, G w := by
        calc
          (∫ y : ℝ, |K y| * |x - y| ^ theta) =
              ∫ y : ℝ, G (-(y - x)) := by
            congr 1
            funext y
            dsimp [K, G]
            congr 2 <;> ring_nf
          _ = ∫ q : ℝ, G (-q) := integral_sub_right_eq_self (fun q => G (-q)) x
          _ = ∫ w : ℝ, G w := integral_neg_eq_self G volume
      rw [htranslate]
      simpa [G] using hmass
    _ = ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta *
          t ^ (-1 + theta / 2 : ℝ) * H := by ring

/-- A Holder population profile produces a Holder truncated chemotaxis flux
with the same exponent. -/
theorem wholeLineCauchyTruncatedFlux_holder_of_profile_holder
    (p : CMParams) {M theta Hu : ℝ} (hM : 0 ≤ M)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (hHu : 0 ≤ Hu)
    (hu_holder : ∀ x y, |u x - u y| ≤ Hu * |x - y| ^ theta) :
    ∀ x y,
      |wholeLineCauchyTruncatedFlux p M u x -
          wholeLineCauchyTruncatedFlux p M u y| ≤
        (rpowLip p.m M * Hu * M ^ p.γ +
          M ^ p.m * (2 * M ^ p.γ)) * |x - y| ^ theta := by
  let c : ℝ → ℝ := wholeLineCauchyClampProfile M u
  have hcIs : IsCUnifBdd c := wholeLineCauchyClampProfile_isCUnifBdd hM hu
  have hcM : ∀ x, c x ∈ Set.Icc (0 : ℝ) M :=
    wholeLineCauchyClampProfile_mem_Icc hM u
  have hc_holder : ∀ x y, |c x - c y| ≤ Hu * |x - y| ^ theta := by
    intro x y
    exact wholeLineCauchyClampProfile_diff_abs_le M (fun _ => hu_holder x y) x
  have hcpow : ∀ x y,
      |c x ^ p.m - c y ^ p.m| ≤
        rpowLip p.m M * Hu * |x - y| ^ theta := by
    intro x y
    calc
      |c x ^ p.m - c y ^ p.m| ≤
          rpowLip p.m M * |c x - c y| :=
        abs_rpow_sub_rpow_le_of_mem_Icc p.hm hM (hcM x) (hcM y)
      _ ≤ rpowLip p.m M * (Hu * |x - y| ^ theta) :=
        mul_le_mul_of_nonneg_left (hc_holder x y)
          (rpowLip_nonneg p.hm hM)
      _ = rpowLip p.m M * Hu * |x - y| ^ theta := by ring
  have hVbound : ∀ x, |deriv (frozenElliptic p c) x| ≤ M ^ p.γ :=
    frozenElliptic_deriv_abs_le_rpow_of_Icc p hM hcIs hcM
  have hVlip : ∀ x y,
      |deriv (frozenElliptic p c) x - deriv (frozenElliptic p c) y| ≤
        (2 * M ^ p.γ) * |x - y| := by
    intro x y
    have h := (frozenElliptic_deriv_lipschitz_of_Icc p hM hcIs hcM).dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq,
      Real.coe_toNNReal _ (mul_nonneg (by norm_num) (Real.rpow_nonneg hM _))] at h
    exact h
  have hVholder : ∀ x y,
      |deriv (frozenElliptic p c) x - deriv (frozenElliptic p c) y| ≤
        (2 * M ^ p.γ) * |x - y| ^ theta := by
    intro x y
    simpa [max_self] using holder_of_local_lipschitz_of_bounded_cauchy
      htheta0 htheta1.le
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hM _)) hVbound
      (fun a b _ => hVlip a b) x y
  intro x y
  change |c x ^ p.m * deriv (frozenElliptic p c) x -
      c y ^ p.m * deriv (frozenElliptic p c) y| ≤ _
  calc
    |c x ^ p.m * deriv (frozenElliptic p c) x -
        c y ^ p.m * deriv (frozenElliptic p c) y| =
        |(c x ^ p.m - c y ^ p.m) * deriv (frozenElliptic p c) x +
          c y ^ p.m * (deriv (frozenElliptic p c) x -
            deriv (frozenElliptic p c) y)| := by ring_nf
    _ ≤ |c x ^ p.m - c y ^ p.m| *
          |deriv (frozenElliptic p c) x| +
        |c y ^ p.m| * |deriv (frozenElliptic p c) x -
          deriv (frozenElliptic p c) y| := by
      simpa only [abs_mul] using abs_add_le
        ((c x ^ p.m - c y ^ p.m) * deriv (frozenElliptic p c) x)
        (c y ^ p.m * (deriv (frozenElliptic p c) x -
          deriv (frozenElliptic p c) y))
    _ ≤ (rpowLip p.m M * Hu * |x - y| ^ theta) * M ^ p.γ +
        M ^ p.m * ((2 * M ^ p.γ) * |x - y| ^ theta) := by
      refine add_le_add
        (mul_le_mul (hcpow x y) (hVbound x) (abs_nonneg _) ?_)
        (mul_le_mul ?_ (hVholder x y) (abs_nonneg _)
          (Real.rpow_nonneg hM _))
      · exact mul_nonneg
          (mul_nonneg (rpowLip_nonneg p.hm hM) hHu)
          (Real.rpow_nonneg (abs_nonneg _) _)
      · rw [abs_of_nonneg (Real.rpow_nonneg (hcM y).1 _)]
        exact Real.rpow_le_rpow (hcM y).1 (hcM y).2
          (zero_le_one.trans p.hm)
    _ = (rpowLip p.m M * Hu * M ^ p.γ +
          M ^ p.m * (2 * M ^ p.γ)) * |x - y| ^ theta := by ring

/-- The actual flux-source trajectory has a spatial Holder modulus on every
positive-time slice. -/
theorem wholeLineCauchyFluxSourceTrajectory_slice_Ctheta
    (p : CMParams) {M T theta : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ HF : ℝ, 0 ≤ HF ∧ ∀ x y : ℝ,
      |(wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) z.1).1 x -
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) z.1).1 y| ≤
        HF * |x - y| ^ theta := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  rcases wholeLineCauchyBUCMildFixedPoint_slice_Ctheta
      p hM hT u₀ hsmall z hz htheta0 htheta1 with ⟨Hu, hHu, huHolder⟩
  let HF : ℝ :=
    rpowLip p.m M * Hu * M ^ p.γ + M ^ p.m * (2 * M ^ p.γ)
  have hHF : 0 ≤ HF := by
    have hLip : 0 ≤ rpowLip p.m M := rpowLip_nonneg p.hm hM
    dsimp [HF]
    positivity
  refine ⟨HF, hHF, ?_⟩
  have hflux := wholeLineCauchyTruncatedFlux_holder_of_profile_holder
    p hM (WholeLineBUC.isCUnifBdd (U z)) htheta0 htheta1 hHu huHolder
  intro x y
  have hext : wholeLineBUCTrajectoryExtend hT U z.1 = U z :=
    wholeLineBUCTrajectoryExtend_eq hT U z.2
  simpa [U, HF, wholeLineCauchyFluxSourceTrajectory, hext] using hflux x y

/-- The actual flux trajectory has one common spatial Holder modulus on every
compact positive-time window. -/
theorem exists_wholeLineCauchyFluxSourceTrajectory_window_Ctheta
    (p : CMParams) {M T a b theta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ha : 0 < a) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ HF : ℝ, 0 ≤ HF ∧ ∀ s ∈ Set.Icc a b, ∀ x y : ℝ,
      |(wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x -
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 y| ≤
        HF * |x - y| ^ theta := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  rcases exists_wholeLineCauchySliceHolderConst_window_bound
      p u₀ (M := M) (a := a) (b := b) (theta := theta) ha with
    ⟨HU, hHU, hwindow⟩
  let HF : ℝ :=
    rpowLip p.m M * HU * M ^ p.γ + M ^ p.m * (2 * M ^ p.γ)
  have hHF : 0 ≤ HF := by
    have hLip : 0 ≤ rpowLip p.m M := rpowLip_nonneg p.hm hM
    dsimp [HF]
    positivity
  refine ⟨HF, hHF, ?_⟩
  intro s hs x y
  have hs0 : 0 ≤ s := (ha.le.trans hs.1)
  have hsT : s ≤ T := hs.2.trans hbT
  let z : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
  have hz : 0 < z.1 := ha.trans_le hs.1
  rcases wholeLineCauchyBUCMildFixedPoint_slice_Ctheta_explicit
      p hM hT u₀ hsmall z hz htheta0 htheta1 with ⟨_hcoef, hu⟩
  have huHU : ∀ q r : ℝ,
      |(U z).1 q - (U z).1 r| ≤ HU * |q - r| ^ theta := by
    intro q r
    have hle := hwindow s hs
    exact (hu q r).trans
      (mul_le_mul_of_nonneg_right hle
        (Real.rpow_nonneg (abs_nonneg _) _))
  have hflux := wholeLineCauchyTruncatedFlux_holder_of_profile_holder
    p hM (WholeLineBUC.isCUnifBdd (U z)) htheta0 htheta1 hHU huHU x y
  have hext : wholeLineBUCTrajectoryExtend hT U s = U z :=
    wholeLineBUCTrajectoryExtend_eq hT U z.2
  simpa [U, z, HF, wholeLineCauchyFluxSourceTrajectory, hext] using hflux

/-- The chemotaxis gradient history has its first spatial derivative at every
positive-time point.  The time integral is split analytically at `t/2`: the
old part uses the bounded-source Hessian estimate, while the recent part uses
the uniform Holder cancellation estimate. -/
theorem wholeLineCauchyFluxGradientHistory_hasDerivAt_positive
    (p : CMParams) {M T theta : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (x : ℝ) :
    HasDerivAt
      (fun w : ℝ => wholeLineCauchyGradientHistory
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall)) z.1 w)
      (∫ s in (0 : ℝ)..z.1,
        wholeLineCauchyHeatHessOp (z.1 - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by
    dsimp [MF]
    positivity
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hgradInt : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (z.1 - s) (F s).1 x)
      volume 0 z.1 :=
    wholeLineCauchyGradientHistory_intervalIntegrable
      hFcont hz hMF hFnorm x
  have hhalf : 0 < z.1 / 2 := by positivity
  rcases exists_wholeLineCauchyFluxSourceTrajectory_window_Ctheta
      p hM hT hhalf z.2.2 u₀ hsmall htheta0 htheta1 with
    ⟨HF, hHF, hFholder⟩
  let Cearly : ℝ :=
    (5 * Real.sqrt 2 / 2) * (z.1 / 2) ^ (-(1 : ℝ)) * MF
  let Wtheta : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let bound : ℝ → ℝ := fun s =>
    Cearly + Wtheta * (z.1 - s) ^ (-1 + theta / 2 : ℝ) * HF
  have hCearly : 0 ≤ Cearly := by
    dsimp [Cearly]
    positivity
  have hWtheta : 0 ≤ Wtheta := by
    dsimp [Wtheta]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hboundInt : IntervalIntegrable bound volume 0 z.1 := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := z.1) htheta0
    have hscaled := (hk.const_mul Wtheta).mul_const HF
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 z.1 :=
      intervalIntegrable_const
    simpa [bound, mul_assoc] using hconst.add hscaled
  have hbound : ∀ s, 0 ≤ s → s < z.1 → ∀ q ∈ Metric.ball x 1,
      ‖wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q‖ ≤ bound s := by
    intro s hs0 hst q _hq
    have hlag : 0 < z.1 - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ z.1 / 2
    · have hlagHalf : z.1 / 2 ≤ z.1 - s := by linarith
      have hpow : (z.1 - s) ^ (-(1 : ℝ)) ≤
          (z.1 / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hglobal := wholeLineCauchyHeatHessOp_abs_le
        hlag hMF (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s))
        (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q| ≤
            ((5 * Real.sqrt 2 / 2) * (z.1 - s) ^ (-(1 : ℝ))) * MF :=
          hglobal
        _ ≤ Cearly := by
          dsimp [Cearly]
          gcongr
        _ ≤ bound s := by
          dsimp [bound]
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hWtheta
              (Real.rpow_nonneg (sub_pos.mpr hst).le _)) hHF)
    · have hsHalf' : z.1 / 2 ≤ s := le_of_not_ge hsHalf
      have hsWindow : s ∈ Set.Icc (z.1 / 2) z.1 := ⟨hsHalf', hst.le⟩
      have hholder := hFholder s hsWindow
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag htheta0 htheta1 hHF
        (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s))
        hholder (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q| ≤
            Wtheta * (z.1 - s) ^ (-1 + theta / 2 : ℝ) * HF := by
          simpa [Wtheta] using hcancel
        _ ≤ bound s := by
          dsimp [bound]
          linarith
  change HasDerivAt (fun w : ℝ => wholeLineCauchyGradientHistory F z.1 w) _ x
  exact wholeLineCauchyGradientHistory_hasDerivAt
    hFcont hz one_pos hFnorm hgradInt hboundInt hbound

/-- Every positive-time canonical mild slice has its first spatial derivative.
This is the first genuine differentiability conclusion of the global
bootstrap, not merely a Holder estimate. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1) (x : ℝ) :
    HasDerivAt
      (fun w : ℝ =>
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w)
      (wholeLineCauchyHeatGradOp z.1 u₀.1 x +
        (-p.χ) * (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatHessOp (z.1 - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) +
        (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatGradOp (z.1 - s)
            (wholeLineCauchyReactionSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x)) x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by
    dsimp [MR]
    positivity
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hRvalue : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatOp (z.1 - s) (R s).1 x)
      volume 0 z.1 :=
    wholeLineCauchyValueHistory_intervalIntegrable hRcont hz hMR hRnorm x
  have hdatum : ∀ y, |u₀.1 y| ≤ ‖u₀‖ :=
    fun y => WholeLineBUC.abs_apply_le_norm u₀ y
  have hheat := wholeLineCauchyHeatOp_hasDerivAt
    hz u₀.1.continuous.aestronglyMeasurable hdatum (x := x)
  have hflux := wholeLineCauchyFluxGradientHistory_hasDerivAt_positive
    p hM hT u₀ hsmall z hz (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) x
  have hreac := wholeLineCauchyValueHistory_hasDerivAt
    hRcont hz hMR one_pos hRnorm hRvalue
  have hsum := (hheat.add (hflux.const_mul (-p.χ))).add hreac
  have hfun :
      (fun w : ℝ => (U z).1 w) =
        fun w : ℝ => wholeLineCauchyHeatOp z.1 u₀.1 w +
          (-p.χ) * wholeLineCauchyGradientHistory F z.1 w +
          wholeLineCauchyValueHistory R z.1 w := by
    funext w
    simpa [U, F, R] using
      wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
        p hM hT u₀ hsmall z w hz
  change HasDerivAt (fun w : ℝ => (U z).1 w) _ x
  rw [hfun]
  simpa [F, R, U] using hsum

section WholeLineCauchyFluxHolderBootstrapAxiomAudit

#print axioms secondDeriv_heatKernel_integral_translated_eq_zero
#print axioms wholeLineCauchyHeatHessOp_Ctheta_abs_le
#print axioms wholeLineCauchyTruncatedFlux_holder_of_profile_holder
#print axioms wholeLineCauchyFluxSourceTrajectory_slice_Ctheta
#print axioms exists_wholeLineCauchyFluxSourceTrajectory_window_Ctheta
#print axioms wholeLineCauchyFluxGradientHistory_hasDerivAt_positive
#print axioms wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive

end WholeLineCauchyFluxHolderBootstrapAxiomAudit

end ShenWork.Paper1
