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

section WholeLineCauchyFluxHolderBootstrapAxiomAudit

#print axioms secondDeriv_heatKernel_integral_translated_eq_zero
#print axioms wholeLineCauchyHeatHessOp_Ctheta_abs_le
#print axioms wholeLineCauchyTruncatedFlux_holder_of_profile_holder
#print axioms wholeLineCauchyFluxSourceTrajectory_slice_Ctheta

end WholeLineCauchyFluxHolderBootstrapAxiomAudit

end ShenWork.Paper1
