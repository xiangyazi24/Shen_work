import ShenWork.Paper1.WholeLineCauchyNonnegativity
import Mathlib.Analysis.Calculus.MeanValue

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time Holder bootstrap for the whole-line Cauchy solution

The divergence-form mild equation contains the spatial heat-gradient applied
to a bounded chemotaxis flux.  A bounded source does not give a uniformly
integrable Hessian bound at the terminal time.  It does give a fractional
spatial modulus: interpolate the gradient-kernel `L¹` estimate with the
Hessian-kernel `L¹` estimate.  The resulting time singularity is
`t ^ (-(1 + theta) / 2)`, which is integrable for every `theta < 1`.
-/

/-- Elementary interpolation of a minimum. -/
theorem min_le_rpow_interp {a b theta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    min a b ≤ a ^ (1 - theta) * b ^ theta := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hrhs : 0 ≤ a ^ (1 - theta) * b ^ theta := by positivity
      simpa [← ha0] using hrhs
    · have hsplit : a = a ^ (1 - theta) * a ^ theta := by
        rw [← Real.rpow_add hapos]
        simp
      calc
        a = a ^ (1 - theta) * a ^ theta := hsplit
        _ ≤ a ^ (1 - theta) * b ^ theta := by
          have hmono : a ^ theta ≤ b ^ theta :=
            Real.rpow_le_rpow ha hab htheta0
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
  · rw [min_eq_right hba]
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · have hrhs : 0 ≤ a ^ (1 - theta) * b ^ theta := by positivity
      simpa [← hb0] using hrhs
    · have hsplit : b = b ^ (1 - theta) * b ^ theta := by
        rw [← Real.rpow_add hbpos]
        simp
      calc
        b = b ^ (1 - theta) * b ^ theta := hsplit
        _ ≤ a ^ (1 - theta) * b ^ theta := by
          have hmono : b ^ (1 - theta) ≤ a ^ (1 - theta) :=
            Real.rpow_le_rpow hb hba (by linarith)
          exact mul_le_mul_of_nonneg_right hmono (by positivity)

/-- A bounded function with a unit-scale Lipschitz bound is globally Holder. -/
theorem holder_of_local_lipschitz_of_bounded_cauchy
    {theta L C : ℝ} {f : ℝ → ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hL : 0 ≤ L)
    (hbound : ∀ x, |f x| ≤ C)
    (hlip : ∀ x y, |x - y| ≤ 1 →
      |f x - f y| ≤ L * |x - y|) :
    ∀ x y, |f x - f y| ≤ max L (2 * C) * |x - y| ^ theta := by
  intro x y
  let d : ℝ := |x - y|
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hmaxL : L ≤ max L (2 * C) := le_max_left _ _
  have hmaxC : 2 * C ≤ max L (2 * C) := le_max_right _ _
  by_cases hsmall : d ≤ 1
  · have hdpow : d ≤ d ^ theta := by
      by_cases hd0 : d = 0
      · rw [hd0]
        exact Real.rpow_nonneg le_rfl _
      · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
        calc
          d = d ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ d ^ theta :=
            Real.rpow_le_rpow_of_exponent_ge hdpos hsmall htheta1
    calc
      |f x - f y| ≤ L * d := by
        exact hlip x y (by simpa [d] using hsmall)
      _ ≤ L * d ^ theta := mul_le_mul_of_nonneg_left hdpow hL
      _ ≤ max L (2 * C) * d ^ theta :=
        mul_le_mul_of_nonneg_right hmaxL (Real.rpow_nonneg hd _)
  · have hone : 1 ≤ d := le_of_not_ge hsmall
    have honepow : 1 ≤ d ^ theta := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ theta := by rw [Real.one_rpow]
        _ ≤ d ^ theta := Real.rpow_le_rpow zero_le_one hone htheta0.le
    have hdiff : |f x - f y| ≤ 2 * C := by
      calc
        |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ C + C := add_le_add (hbound x) (hbound y)
        _ = 2 * C := by ring
    calc
      |f x - f y| ≤ 2 * C := hdiff
      _ ≤ max L (2 * C) := hmaxC
      _ = max L (2 * C) * 1 := by ring
      _ ≤ max L (2 * C) * d ^ theta := by
        gcongr

/-- Positive-lag modified heat flow is Lipschitz in space for bounded data. -/
theorem wholeLineCauchyHeatOp_lipschitz
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x y : ℝ) :
    |wholeLineCauchyHeatOp t f x - wholeLineCauchyHeatOp t f y| ≤
      ((2 / Real.sqrt (4 * Real.pi)) * M *
        t ^ (-(1 / 2 : ℝ))) * |x - y| := by
  let g : ℝ → ℝ := fun z => wholeLineCauchyHeatOp t f z
  let C : ℝ := (2 / Real.sqrt (4 * Real.pi)) * M *
    t ^ (-(1 / 2 : ℝ))
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt g (deriv g z) Set.univ z := by
    intro z _hz
    exact (wholeLineCauchyHeatOp_hasDerivAt ht hf_meas hf (x := z)).differentiableAt
      |>.hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv g z‖ ≤ C := by
    intro z _hz
    have hz := wholeLineCauchyHeatOp_hasDerivAt ht hf_meas hf (x := z)
    rw [Real.norm_eq_abs, hz.deriv]
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using
      wholeLineCauchyHeatGradOp_norm_le_rpow ht hM hf z
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (𝕜 := ℝ) (G := ℝ) (f := g) (s := Set.univ)
    hderiv hbound convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [g, C, Real.norm_eq_abs, abs_sub_comm] using hmv

/-- Positive-lag modified heat flow maps bounded data to every fractional
Holder class below one. -/
theorem wholeLineCauchyHeatOp_Ctheta
    {f : ℝ → ℝ} {t M theta : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x y : ℝ) :
    |wholeLineCauchyHeatOp t f x - wholeLineCauchyHeatOp t f y| ≤
      max ((2 / Real.sqrt (4 * Real.pi)) * M *
          t ^ (-(1 / 2 : ℝ))) (2 * M) * |x - y| ^ theta := by
  apply holder_of_local_lipschitz_of_bounded_cauchy
    htheta0 htheta1.le (by positivity)
  · exact wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
      hf hM hf_meas ht.le
  · intro a b _hab
    exact wholeLineCauchyHeatOp_lipschitz ht hM hf_meas hf a b

/-- The whole-line modified heat-gradient is globally Lipschitz in space at
every positive lag.  Its Lipschitz constant has the expected `t⁻¹` scale. -/
theorem wholeLineCauchyHeatGradOp_lipschitz
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x y : ℝ) :
    |wholeLineCauchyHeatGradOp t f x - wholeLineCauchyHeatGradOp t f y| ≤
      ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * M) * |x - y| := by
  let g : ℝ → ℝ := fun z => wholeLineCauchyHeatGradOp t f z
  let C : ℝ := (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * M
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt g (deriv g z) Set.univ z := by
    intro z _hz
    have hz := wholeLineCauchyHeatGradOp_hasDerivAt ht hf_meas hf (x := z)
    exact hz.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv g z‖ ≤ C := by
    intro z _hz
    have hz := wholeLineCauchyHeatGradOp_hasDerivAt ht hf_meas hf (x := z)
    rw [Real.norm_eq_abs, hz.deriv]
    exact wholeLineCauchyHeatHessOp_abs_le ht hM hf_meas hf
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (𝕜 := ℝ) (G := ℝ) (f := g) (s := Set.univ)
    hderiv hbound convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [g, C, Real.norm_eq_abs, abs_sub_comm] using hmv

/-- Fractional spatial smoothing of the whole-line modified heat-gradient.
The exponent `-(1+theta)/2` is strictly above `-1` when `theta < 1`, so this
estimate can be integrated over a Duhamel history. -/
theorem wholeLineCauchyHeatGradOp_Linf_to_Ctheta
    {f : ℝ → ℝ} {t M theta : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x y : ℝ) :
    |wholeLineCauchyHeatGradOp t f x - wholeLineCauchyHeatGradOp t f y| ≤
      (2 : ℝ) ^ (1 - theta) *
          ((5 * Real.sqrt 2 / 2) ^ theta *
            (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) *
        t ^ (-((1 + theta) / 2) : ℝ) * M * |x - y| ^ theta := by
  let Cgrad : ℝ := 2 / Real.sqrt (4 * Real.pi)
  let Cgg : ℝ := 5 * Real.sqrt 2 / 2
  have hCgrad : 0 ≤ Cgrad := by dsimp [Cgrad]; positivity
  have hCgg : 0 ≤ Cgg := by dsimp [Cgg]; positivity
  let gx : ℝ := wholeLineCauchyHeatGradOp t f x
  let gy : ℝ := wholeLineCauchyHeatGradOp t f y
  let A : ℝ := Cgrad * t ^ (-(1 / 2) : ℝ) * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hgx : |gx| ≤ A := by
    dsimp [gx, A, Cgrad]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      wholeLineCauchyHeatGradOp_norm_le_rpow ht hM hf x
  have hgy : |gy| ≤ A := by
    dsimp [gy, A, Cgrad]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      wholeLineCauchyHeatGradOp_norm_le_rpow ht hM hf y
  have hval : |gx - gy| ≤ 2 * A := by
    calc
      |gx - gy| ≤ |gx| + |gy| := abs_sub _ _
      _ ≤ A + A := add_le_add hgx hgy
      _ = 2 * A := by ring
  let B : ℝ := Cgg * t ^ (-(1 : ℝ)) * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlip : |gx - gy| ≤ B * |x - y| := by
    dsimp [gx, gy, B, Cgg]
    exact wholeLineCauchyHeatGradOp_lipschitz ht hM hf_meas hf x y
  let a : ℝ := 2 * A
  let b : ℝ := B * |x - y|
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hchain : |gx - gy| ≤ a ^ (1 - theta) * b ^ theta :=
    (le_min hval hlip).trans
      (min_le_rpow_interp ha hb htheta0.le htheta1.le)
  have htpowA :
      (t ^ (-(1 / 2) : ℝ)) ^ (1 - theta) =
        t ^ (-(1 - theta) / 2 : ℝ) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  have htpowB :
      (t ^ (-(1 : ℝ))) ^ theta = t ^ (-(theta : ℝ)) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  have hapow :
      a ^ (1 - theta) = (2 : ℝ) ^ (1 - theta) *
        (Cgrad ^ (1 - theta) * t ^ (-(1 - theta) / 2 : ℝ) *
          M ^ (1 - theta)) := by
    rw [show a = 2 * (Cgrad * t ^ (-(1 / 2) : ℝ) * M) by rfl]
    rw [Real.mul_rpow (by norm_num) hA,
      Real.mul_rpow (by positivity) hM,
      Real.mul_rpow hCgrad (Real.rpow_nonneg ht.le _), htpowA]
  have hbpow :
      b ^ theta = Cgg ^ theta * t ^ (-(theta : ℝ)) *
        M ^ theta * |x - y| ^ theta := by
    rw [show b = (Cgg * t ^ (-(1 : ℝ)) * M) * |x - y| by rfl]
    rw [Real.mul_rpow hB (abs_nonneg _),
      Real.mul_rpow (by positivity) hM,
      Real.mul_rpow hCgg (Real.rpow_nonneg ht.le _), htpowB]
  have htime :
      t ^ (-(1 - theta) / 2 : ℝ) * t ^ (-(theta : ℝ)) =
        t ^ (-((1 + theta) / 2) : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hMcollapse : M ^ (1 - theta) * M ^ theta = M := by
    rw [← Real.rpow_add' hM (by simp)]
    simp
  have hfinal :
      a ^ (1 - theta) * b ^ theta =
        (2 : ℝ) ^ (1 - theta) *
            (Cgg ^ theta * Cgrad ^ (1 - theta)) *
          t ^ (-((1 + theta) / 2) : ℝ) * M * |x - y| ^ theta := by
    rw [hapow, hbpow]
    rw [show
      (2 : ℝ) ^ (1 - theta) *
          (Cgrad ^ (1 - theta) * t ^ (-(1 - theta) / 2 : ℝ) *
            M ^ (1 - theta)) *
          (Cgg ^ theta * t ^ (-(theta : ℝ)) * M ^ theta *
            |x - y| ^ theta) =
        (2 : ℝ) ^ (1 - theta) *
            (Cgg ^ theta * Cgrad ^ (1 - theta)) *
          (t ^ (-(1 - theta) / 2 : ℝ) * t ^ (-(theta : ℝ))) *
          (M ^ (1 - theta) * M ^ theta) * |x - y| ^ theta by ring]
    rw [htime, hMcollapse]
  rw [hfinal] at hchain
  simpa [gx, gy, Cgrad, Cgg] using hchain

/-- The time singularity produced by the gradient Holder estimate is
interval-integrable precisely below exponent one. -/
theorem intervalIntegrable_sub_rpow_gradient_holder
    {t theta : ℝ} (htheta1 : theta < 1) :
    IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-((1 + theta) / 2) : ℝ)) volume 0 t := by
  have hexp : (-1 : ℝ) < -((1 + theta) / 2) := by linarith
  have hbase : IntervalIntegrable
      (fun q : ℝ => q ^ (-((1 + theta) / 2) : ℝ)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  simpa using (hbase.comp_sub_left t).symm

/-- Exact evaluation of the gradient-Holder time kernel. -/
theorem integral_sub_rpow_gradient_holder
    {t theta : ℝ} (_ht : 0 ≤ t) (htheta1 : theta < 1) :
    (∫ s in (0 : ℝ)..t, (t - s) ^ (-((1 + theta) / 2) : ℝ)) =
      t ^ ((1 - theta) / 2 : ℝ) / ((1 - theta) / 2) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun q : ℝ => q ^ (-((1 + theta) / 2) : ℝ)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith :
    (-1 : ℝ) < -((1 + theta) / 2)))]
  have hexp : -((1 + theta) / 2 : ℝ) + 1 = (1 - theta) / 2 := by ring
  have hne : ((1 - theta) / 2 : ℝ) ≠ 0 := by linarith
  rw [hexp, Real.zero_rpow hne, sub_zero]

/-- A continuous uniformly bounded BUC source produces a spatially Holder
gradient Duhamel history.  This is the first positive-time smoothing step for
the chemotaxis leg. -/
theorem wholeLineCauchyGradientHistory_Ctheta
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M theta : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hFnorm : ∀ s, ‖F s‖ ≤ M) (x y : ℝ) :
    |wholeLineCauchyGradientHistory F t x -
        wholeLineCauchyGradientHistory F t y| ≤
      ((2 : ℝ) ^ (1 - theta) *
          ((5 * Real.sqrt 2 / 2) ^ theta *
            (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) *
        M * |x - y| ^ theta) *
      (t ^ ((1 - theta) / 2 : ℝ) / ((1 - theta) / 2)) := by
  let K : ℝ := (2 : ℝ) ^ (1 - theta) *
      ((5 * Real.sqrt 2 / 2) ^ theta *
        (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) *
      M * |x - y| ^ theta
  have hxint := wholeLineCauchyGradientHistory_intervalIntegrable
    hF ht hM hFnorm x
  have hyint := wholeLineCauchyGradientHistory_intervalIntegrable
    hF ht hM hFnorm y
  have hdiffint : IntervalIntegrable
      (fun s : ℝ =>
        wholeLineCauchyHeatGradOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 y) volume 0 t :=
    hxint.sub hyint
  have hkernelint := intervalIntegrable_sub_rpow_gradient_holder
    (t := t) htheta1
  have hmajorint : IntervalIntegrable
      (fun s : ℝ => K * (t - s) ^ (-((1 + theta) / 2) : ℝ))
      volume 0 t := hkernelint.const_mul K
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      |wholeLineCauchyHeatGradOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 y| ≤
        K * (t - s) ^ (-((1 + theta) / 2) : ℝ) := by
    intro s hs
    have hlag : 0 < t - s := sub_pos.mpr hs.2
    have hsource : ∀ z, |(F s).1 z| ≤ M := by
      intro z
      exact (WholeLineBUC.abs_apply_le_norm (F s) z).trans (hFnorm s)
    have hop := wholeLineCauchyHeatGradOp_Linf_to_Ctheta
      hlag hM htheta0 htheta1 (F s).1.continuous.aestronglyMeasurable
      hsource x y
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hop
  unfold wholeLineCauchyGradientHistory
  rw [← intervalIntegral.integral_sub hxint hyint]
  calc
    |∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatGradOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 y)| ≤
        ∫ s in (0 : ℝ)..t,
          |wholeLineCauchyHeatGradOp (t - s) (F s).1 x -
            wholeLineCauchyHeatGradOp (t - s) (F s).1 y| :=
      intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0 : ℝ)..t,
        K * (t - s) ^ (-((1 + theta) / 2) : ℝ) := by
      exact intervalIntegral.integral_mono_on_of_le_Ioo ht.le
        hdiffint.abs hmajorint hpoint
    _ = K * (t ^ ((1 - theta) / 2 : ℝ) /
        ((1 - theta) / 2)) := by
      rw [intervalIntegral.integral_const_mul,
        integral_sub_rpow_gradient_holder ht.le htheta1]
    _ = ((2 : ℝ) ^ (1 - theta) *
          ((5 * Real.sqrt 2 / 2) ^ theta *
            (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) *
        M * |x - y| ^ theta) *
      (t ^ ((1 - theta) / 2 : ℝ) / ((1 - theta) / 2)) := rfl

/-- Uniform bound for a value Duhamel history with bounded BUC source. -/
theorem wholeLineCauchyValueHistory_abs_le
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hFnorm : ∀ s, ‖F s‖ ≤ M) (x : ℝ) :
    |wholeLineCauchyValueHistory F t x| ≤ M * t := by
  have hint := wholeLineCauchyValueHistory_intervalIntegrable
    hF ht hM hFnorm x
  have hconst : IntervalIntegrable (fun _s : ℝ => M) volume 0 t :=
    intervalIntegrable_const
  unfold wholeLineCauchyValueHistory
  calc
    |∫ s in (0 : ℝ)..t, wholeLineCauchyHeatOp (t - s) (F s).1 x| ≤
        ∫ s in (0 : ℝ)..t,
          |wholeLineCauchyHeatOp (t - s) (F s).1 x| :=
      intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ _s in (0 : ℝ)..t, M := by
      refine intervalIntegral.integral_mono_on ht.le hint.abs hconst ?_
      intro s hs
      apply wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
        (M := M) (f := (F s).1)
      · intro z
        exact (WholeLineBUC.abs_apply_le_norm (F s) z).trans (hFnorm s)
      · exact hM
      · exact (F s).1.continuous.aestronglyMeasurable
      · exact sub_nonneg.mpr hs.2
    _ = M * t := by
      rw [intervalIntegral.integral_const]
      simp
      ring

/-- The value Duhamel history is globally Lipschitz in space; its terminal
gradient singularity is only `(t-s)⁻¹ᐟ²`. -/
theorem wholeLineCauchyValueHistory_lipschitz
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hFnorm : ∀ s, ‖F s‖ ≤ M) (x y : ℝ) :
    |wholeLineCauchyValueHistory F t x -
        wholeLineCauchyValueHistory F t y| ≤
      ((2 / Real.sqrt (4 * Real.pi)) * M *
        (2 * Real.sqrt t)) * |x - y| := by
  let K : ℝ := (2 / Real.sqrt (4 * Real.pi)) * M * |x - y|
  have hxint := wholeLineCauchyValueHistory_intervalIntegrable
    hF ht hM hFnorm x
  have hyint := wholeLineCauchyValueHistory_intervalIntegrable
    hF ht hM hFnorm y
  have hdiffint : IntervalIntegrable
      (fun s : ℝ =>
        wholeLineCauchyHeatOp (t - s) (F s).1 x -
          wholeLineCauchyHeatOp (t - s) (F s).1 y) volume 0 t :=
    hxint.sub hyint
  have hkernelint :=
    ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t
  have hmajorint : IntervalIntegrable
      (fun s : ℝ => K * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t :=
    hkernelint.const_mul K
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      |wholeLineCauchyHeatOp (t - s) (F s).1 x -
          wholeLineCauchyHeatOp (t - s) (F s).1 y| ≤
        K * (t - s) ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    have hsource : ∀ z, |(F s).1 z| ≤ M := by
      intro z
      exact (WholeLineBUC.abs_apply_le_norm (F s) z).trans (hFnorm s)
    have hop := wholeLineCauchyHeatOp_lipschitz
      (sub_pos.mpr hs.2) hM (F s).1.continuous.aestronglyMeasurable
      hsource x y
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hop
  unfold wholeLineCauchyValueHistory
  rw [← intervalIntegral.integral_sub hxint hyint]
  calc
    |∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatOp (t - s) (F s).1 x -
          wholeLineCauchyHeatOp (t - s) (F s).1 y)| ≤
        ∫ s in (0 : ℝ)..t,
          |wholeLineCauchyHeatOp (t - s) (F s).1 x -
            wholeLineCauchyHeatOp (t - s) (F s).1 y| :=
      intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, K * (t - s) ^ (-(1 / 2 : ℝ)) := by
      exact intervalIntegral.integral_mono_on_of_le_Ioo ht.le
        hdiffint.abs hmajorint hpoint
    _ = K * (2 * Real.sqrt t) := by
      rw [intervalIntegral.integral_const_mul,
        ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht.le]
    _ = ((2 / Real.sqrt (4 * Real.pi)) * M *
        (2 * Real.sqrt t)) * |x - y| := by
      dsimp [K]
      ring

/-- Fractional Holder consequence for the value Duhamel history. -/
theorem wholeLineCauchyValueHistory_Ctheta
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M theta : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hFnorm : ∀ s, ‖F s‖ ≤ M) (x y : ℝ) :
    |wholeLineCauchyValueHistory F t x -
        wholeLineCauchyValueHistory F t y| ≤
      max ((2 / Real.sqrt (4 * Real.pi)) * M * (2 * Real.sqrt t))
          (2 * (M * t)) * |x - y| ^ theta := by
  apply holder_of_local_lipschitz_of_bounded_cauchy
    htheta0 htheta1.le (by positivity)
  · exact wholeLineCauchyValueHistory_abs_le hF ht hM hFnorm
  · intro a b _hab
    exact wholeLineCauchyValueHistory_lipschitz hF ht hM hFnorm a b

/-- Explicit spatial Holder coefficient produced by the first positive-time
bootstrap. -/
def wholeLineCauchySliceHolderConst
    (p : CMParams) (M : ℝ) (u₀ : WholeLineBUC) (t theta : ℝ) : ℝ :=
  let MF : ℝ := M ^ p.m * M ^ p.γ
  let MR : ℝ := M + M * (1 + M ^ p.α)
  let Hheat : ℝ := max
    ((2 / Real.sqrt (4 * Real.pi)) * ‖u₀‖ * t ^ (-(1 / 2 : ℝ)))
    (2 * ‖u₀‖)
  let Hgrad : ℝ :=
    ((2 : ℝ) ^ (1 - theta) *
        ((5 * Real.sqrt 2 / 2) ^ theta *
          (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) *
      MF * (t ^ ((1 - theta) / 2 : ℝ) / ((1 - theta) / 2)))
  let Hvalue : ℝ := max
    ((2 / Real.sqrt (4 * Real.pi)) * MR * (2 * Real.sqrt t))
    (2 * (MR * t))
  Hheat + |p.χ| * Hgrad + Hvalue

/-- Every positive-time slice of the canonical BUC fixed point satisfies the
explicit global fractional Holder bound. -/
theorem wholeLineCauchyBUCMildFixedPoint_slice_Ctheta_explicit
    (p : CMParams) {M T theta : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    0 ≤ wholeLineCauchySliceHolderConst p M u₀ z.1 theta ∧
      ∀ x y : ℝ,
      |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x -
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y| ≤
        wholeLineCauchySliceHolderConst p M u₀ z.1 theta *
          |x - y| ^ theta := by
  let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hFcont : Continuous F := by
    dsimp [F]
    exact wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hRcont : Continuous R := by
    dsimp [R]
    exact wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    dsimp [F, MF, wholeLineCauchyFluxSourceTrajectory]
    exact wholeLineCauchyTruncatedFluxBUC_norm_le p hM _
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    dsimp [R, MR, wholeLineCauchyReactionSourceTrajectory]
    exact wholeLineCauchyTruncatedReactionBUC_norm_le p hM _
  let Hheat : ℝ := max
    ((2 / Real.sqrt (4 * Real.pi)) * ‖u₀‖ *
      z.1 ^ (-(1 / 2 : ℝ))) (2 * ‖u₀‖)
  let Hgrad : ℝ :=
    ((2 : ℝ) ^ (1 - theta) *
        ((5 * Real.sqrt 2 / 2) ^ theta *
          (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) *
      MF * (z.1 ^ ((1 - theta) / 2 : ℝ) /
        ((1 - theta) / 2)))
  let Hvalue : ℝ := max
    ((2 / Real.sqrt (4 * Real.pi)) * MR * (2 * Real.sqrt z.1))
    (2 * (MR * z.1))
  let H : ℝ := Hheat + |p.χ| * Hgrad + Hvalue
  have hH_eq : H = wholeLineCauchySliceHolderConst p M u₀ z.1 theta := rfl
  have hHheat : 0 ≤ Hheat := by
    dsimp [Hheat]
    exact le_max_of_le_left (by positivity)
  have hHgrad : 0 ≤ Hgrad := by
    have hden : 0 < (1 - theta) / 2 := by linarith
    have hMF0 : 0 ≤ MF := by
      dsimp [MF]
      positivity
    dsimp [Hgrad]
    positivity
  have hHvalue : 0 ≤ Hvalue := by
    dsimp [Hvalue]
    exact le_max_of_le_left (by positivity)
  constructor
  · rw [← hH_eq]
    dsimp [H]
    positivity
  · intro x y
    have hdatum : ∀ q, |u₀.1 q| ≤ ‖u₀‖ :=
      fun q => WholeLineBUC.abs_apply_le_norm u₀ q
    have hheat := wholeLineCauchyHeatOp_Ctheta
      hz (norm_nonneg u₀) htheta0 htheta1 u₀.1.continuous.aestronglyMeasurable
      hdatum x y
    have hgrad := wholeLineCauchyGradientHistory_Ctheta
      hFcont hz hMF htheta0 htheta1 hFnorm x y
    have hvalue := wholeLineCauchyValueHistory_Ctheta
      hRcont hz hMR htheta0 htheta1 hRnorm x y
    have hxeq := wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
      p hM hT u₀ hsmall z x hz
    have hyeq := wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
      p hM hT u₀ hsmall z y hz
    have hheat' :
        |wholeLineCauchyHeatOp z.1 u₀.1 x -
            wholeLineCauchyHeatOp z.1 u₀.1 y| ≤
          Hheat * |x - y| ^ theta := by
      simpa [Hheat] using hheat
    have hgrad' :
        |wholeLineCauchyGradientHistory F z.1 x -
            wholeLineCauchyGradientHistory F z.1 y| ≤
          Hgrad * |x - y| ^ theta := by
      simpa [Hgrad, mul_assoc, mul_left_comm, mul_comm] using hgrad
    have hvalue' :
        |wholeLineCauchyValueHistory R z.1 x -
            wholeLineCauchyValueHistory R z.1 y| ≤
          Hvalue * |x - y| ^ theta := by
      simpa [Hvalue] using hvalue
    rw [hxeq, hyeq]
    calc
      |(wholeLineCauchyHeatOp z.1 u₀.1 x +
            -p.χ * wholeLineCauchyGradientHistory F z.1 x +
            wholeLineCauchyValueHistory R z.1 x) -
          (wholeLineCauchyHeatOp z.1 u₀.1 y +
            -p.χ * wholeLineCauchyGradientHistory F z.1 y +
            wholeLineCauchyValueHistory R z.1 y)| =
        |(wholeLineCauchyHeatOp z.1 u₀.1 x -
            wholeLineCauchyHeatOp z.1 u₀.1 y) +
          (-p.χ) * (wholeLineCauchyGradientHistory F z.1 x -
            wholeLineCauchyGradientHistory F z.1 y) +
          (wholeLineCauchyValueHistory R z.1 x -
            wholeLineCauchyValueHistory R z.1 y)| := by ring_nf
      _ ≤ |wholeLineCauchyHeatOp z.1 u₀.1 x -
            wholeLineCauchyHeatOp z.1 u₀.1 y| +
          |(-p.χ) * (wholeLineCauchyGradientHistory F z.1 x -
            wholeLineCauchyGradientHistory F z.1 y)| +
          |wholeLineCauchyValueHistory R z.1 x -
            wholeLineCauchyValueHistory R z.1 y| := by
        calc
          |(wholeLineCauchyHeatOp z.1 u₀.1 x -
                wholeLineCauchyHeatOp z.1 u₀.1 y) +
              (-p.χ) * (wholeLineCauchyGradientHistory F z.1 x -
                wholeLineCauchyGradientHistory F z.1 y) +
              (wholeLineCauchyValueHistory R z.1 x -
                wholeLineCauchyValueHistory R z.1 y)| ≤
              |(wholeLineCauchyHeatOp z.1 u₀.1 x -
                  wholeLineCauchyHeatOp z.1 u₀.1 y) +
                (-p.χ) * (wholeLineCauchyGradientHistory F z.1 x -
                  wholeLineCauchyGradientHistory F z.1 y)| +
                |wholeLineCauchyValueHistory R z.1 x -
                  wholeLineCauchyValueHistory R z.1 y| := abs_add_le _ _
          _ ≤ (|wholeLineCauchyHeatOp z.1 u₀.1 x -
                  wholeLineCauchyHeatOp z.1 u₀.1 y| +
                |(-p.χ) * (wholeLineCauchyGradientHistory F z.1 x -
                  wholeLineCauchyGradientHistory F z.1 y)|) +
                |wholeLineCauchyValueHistory R z.1 x -
                  wholeLineCauchyValueHistory R z.1 y| := by
            exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ Hheat * |x - y| ^ theta +
          |p.χ| * (Hgrad * |x - y| ^ theta) +
          Hvalue * |x - y| ^ theta := by
        rw [abs_mul, abs_neg]
        exact add_le_add
          (add_le_add hheat'
            (mul_le_mul_of_nonneg_left hgrad' (abs_nonneg p.χ))) hvalue'
      _ = wholeLineCauchySliceHolderConst p M u₀ z.1 theta *
            |x - y| ^ theta := by
        rw [← hH_eq]
        dsimp [H]
        ring

/-- Existential wrapper retained for callers that do not need the displayed
coefficient. -/
theorem wholeLineCauchyBUCMildFixedPoint_slice_Ctheta
    (p : CMParams) {M T theta : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y : ℝ,
      |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x -
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y| ≤
        H * |x - y| ^ theta := by
  rcases wholeLineCauchyBUCMildFixedPoint_slice_Ctheta_explicit
      p hM hT u₀ hsmall z hz htheta0 htheta1 with ⟨hH, hholder⟩
  exact ⟨wholeLineCauchySliceHolderConst p M u₀ z.1 theta, hH, hholder⟩

/-- The explicit slice coefficient has a uniform upper bound on every compact
positive-time window. -/
theorem exists_wholeLineCauchySliceHolderConst_window_bound
    (p : CMParams) {M a b theta : ℝ} (u₀ : WholeLineBUC)
    (ha : 0 < a) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t ∈ Set.Icc a b,
      wholeLineCauchySliceHolderConst p M u₀ t theta ≤ H := by
  have hne : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht
    exact ne_of_gt (ha.trans_le ht.1)
  have hpowNeg : ContinuousOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)))
      (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (hne t ht))
  have hpowPos : ContinuousOn (fun t : ℝ => t ^ ((1 - theta) / 2 : ℝ))
      (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (hne t ht))
  have hsqrt : ContinuousOn (fun t : ℝ => Real.sqrt t) (Set.Icc a b) :=
    Real.continuous_sqrt.continuousOn
  have hcont : ContinuousOn
      (fun t : ℝ => wholeLineCauchySliceHolderConst p M u₀ t theta)
      (Set.Icc a b) := by
    unfold wholeLineCauchySliceHolderConst
    dsimp only
    fun_prop
  have hbdd : BddAbove
      ((fun t : ℝ => wholeLineCauchySliceHolderConst p M u₀ t theta) ''
        Set.Icc a b) :=
    isCompact_Icc.bddAbove_image hcont
  rcases hbdd with ⟨B, hB⟩
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro t ht
  exact (hB (Set.mem_image_of_mem _ ht)).trans (le_max_right _ _)

section WholeLineCauchyHolderBootstrapAxiomAudit

#print axioms wholeLineCauchyHeatGradOp_lipschitz
#print axioms wholeLineCauchyHeatGradOp_Linf_to_Ctheta
#print axioms wholeLineCauchyGradientHistory_Ctheta
#print axioms wholeLineCauchyValueHistory_Ctheta
#print axioms wholeLineCauchyBUCMildFixedPoint_slice_Ctheta_explicit
#print axioms wholeLineCauchyBUCMildFixedPoint_slice_Ctheta
#print axioms exists_wholeLineCauchySliceHolderConst_window_bound

end WholeLineCauchyHolderBootstrapAxiomAudit

end ShenWork.Paper1
