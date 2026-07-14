import ShenWork.Paper1.WholeLineCauchyFluxC1Bootstrap

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time C2 bootstrap for the whole-line Cauchy solution

The first structural step integrates one spatial derivative off the Gaussian
and onto the now-`C1` physical flux.  The boundary term at both infinities is
handled by Mathlib's whole-line integration-by-parts theorem in its integrable
form; Gaussian derivative integrability and boundedness of the source provide
all three required products.
-/

/-- Whole-line Gaussian integration by parts for the modified heat Hessian:
for a bounded `C1` source with bounded continuous derivative, one derivative
can be transferred from the kernel to the source. -/
theorem wholeLineCauchyHeatHessOp_eq_gradOp_deriv
    {f : ℝ → ℝ} {t x C D : ℝ}
    (ht : 0 < t)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdcont : Continuous (deriv f)) :
    wholeLineCauchyHeatHessOp t f x =
      wholeLineCauchyHeatGradOp t (deriv f) x := by
  let k : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => heatKernel t z) (x - y)
  let k' : ℝ → ℝ := fun y =>
    -deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y)
  have hkderiv : ∀ y, HasDerivAt k (k' y) y := by
    intro y
    have hinner : HasDerivAt (fun q : ℝ => x - q) (-1) y := by
      simpa using (hasDerivAt_const y x).sub (hasDerivAt_id y)
    have hcomp :=
      (ShenWork.IntervalNeumannFullKernel.heatKernel_secondDeriv_hasDerivAt
        ht (x - y)).comp y hinner
    change HasDerivAt
      (fun q : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - q))
      (-deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y)) y
    convert hcomp using 1
    rw [ShenWork.IntervalNeumannFullKernel.deriv_deriv_heatKernel ht]
    ring
  have hkfd : Integrable (fun y => k y * deriv f y) := by
    have hbase := heatKernel_deriv_mul_bounded_integrable ht x hfd
      hfdcont.aestronglyMeasurable
    exact hbase.congr (Filter.Eventually.of_forall fun y => by
      dsimp [k]
      rw [deriv_heatKernel_translated_left ht, deriv_heatKernel ht])
  have hk'f : Integrable (fun y => k' y * f y) := by
    have hbase :=
      ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
        ht x hf (continuous_iff_continuousAt.2
          (fun y => (hfderiv y).continuousAt)).aestronglyMeasurable
    simpa [k'] using hbase.neg
  have hkf : Integrable (fun y => k y * f y) := by
    have hbase := heatKernel_deriv_mul_bounded_integrable ht x hf
      (continuous_iff_continuousAt.2
        (fun y => (hfderiv y).continuousAt)).aestronglyMeasurable
    exact hbase.congr (Filter.Eventually.of_forall fun y => by
      dsimp [k]
      rw [deriv_heatKernel_translated_left ht, deriv_heatKernel ht])
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := k) (v := f) (u' := k') (v' := deriv f)
    (fun y _ => hkderiv y) (fun y _ => hfderiv y) hkfd hk'f hkf
  have hbase :
      (∫ y : ℝ, k y * deriv f y) =
        ∫ y : ℝ,
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y) * f y := by
    rw [hibp]
    rw [show (fun y : ℝ => k' y * f y) = fun y =>
        -(deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x - y) * f y) by
      funext y
      dsimp [k']
      ring]
    rw [integral_neg, neg_neg]
  unfold wholeLineCauchyHeatHessOp wholeLineCauchyHeatGradOp
  have hgrad : (∫ y : ℝ, Real.exp (-t) *
      (deriv (fun z : ℝ => heatKernel t (z - y)) x * deriv f y)) =
      Real.exp (-t) * ∫ y : ℝ, k y * deriv f y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [deriv_heatKernel_translated_left ht]
    dsimp [k]
    rw [deriv_heatKernel ht]
  rw [hgrad, hbase]

/-- Exact integral of the interpolated Hessian singularity. -/
theorem integral_sub_rpow_hess_Ctheta_to_Ceta
    {t theta eta : ℝ} (_ht : 0 ≤ t)
    (hrel : eta * (1 + theta) < theta) :
    (∫ s in (0 : ℝ)..t,
        (t - s) ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ)) =
      t ^ ((theta - eta * (1 + theta)) / 2 : ℝ) /
        ((theta - eta * (1 + theta)) / 2) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun q : ℝ =>
      q ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith :
    (-1 : ℝ) < -1 + (theta - eta * (1 + theta)) / 2))]
  have hexp :
      (-1 + (theta - eta * (1 + theta)) / 2 : ℝ) + 1 =
        (theta - eta * (1 + theta)) / 2 := by ring
  have hne : ((theta - eta * (1 + theta)) / 2 : ℝ) ≠ 0 := by
    linarith
  rw [hexp, Real.zero_rpow hne, sub_zero]

/-- On a compact positive-time window, the Hessian history of the canonical
chemotaxis flux has one common spatial `C^eta` coefficient.  The old history
has lag at least `a/2`; the recent history uses the common source Holder
modulus on `[a/2,b]`. -/
theorem wholeLineCauchyFluxHessianHistory_Ceta_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc a b, ∀ x y : ℝ,
      |(∫ r in (0 : ℝ)..s,
          wholeLineCauchyHeatHessOp (s - r)
            (wholeLineCauchyFluxSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) r).1 x) -
        (∫ r in (0 : ℝ)..s,
          wholeLineCauchyHeatHessOp (s - r)
            (wholeLineCauchyFluxSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) r).1 y)| ≤
        K * |x - y| ^ eta := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by
    dsimp [MF]
    positivity
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ r, ‖F r‖ ≤ MF := by
    intro r
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U r)
  have hhalf : 0 < a / 2 := by positivity
  rcases exists_wholeLineCauchyFluxSourceTrajectory_window_Ctheta
      p hM hT hhalf hbT u₀ hsmall htheta0 htheta1 with
    ⟨HF, hHF, hFholder⟩
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let C2 : ℝ := 5 * Real.sqrt 2 / 2
  let C3 : ℝ := heatThirdTailConstant
  let aexp : ℝ := -1 + theta / 2
  let eexp : ℝ := -1 + (theta - eta * (1 + theta)) / 2
  let delta : ℝ := (theta - eta * (1 + theta)) / 2
  let A0 : ℝ := C2 * (a / 2) ^ (-(1 : ℝ)) * MF
  let B0 : ℝ := C3 * (a / 2) ^ (-(3 / 2 : ℝ)) * MF
  let E0 : ℝ := max B0 (2 * A0)
  let D : ℝ := (2 * W * HF) ^ (1 - eta) * (C3 * MF) ^ eta
  let K : ℝ := E0 * b + D * (b ^ delta / delta)
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hW : 0 ≤ W := by
    dsimp [W]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact heatThirdTailConstant_nonneg
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hE0 : 0 ≤ E0 := le_trans hB0 (le_max_left _ _)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg hE0 hb0)
      (mul_nonneg hD (div_nonneg (Real.rpow_nonneg hb0 _) hdelta.le))
  refine ⟨K, hK, ?_⟩
  intro s hs x y
  have hs0 : 0 < s := ha.trans_le hs.1
  have hsT : s ≤ T := hs.2.trans hbT
  let normBound : ℝ → ℝ := fun r =>
    A0 + W * (s - r) ^ aexp * HF
  let diffBound : ℝ → ℝ := fun r =>
    E0 + D * (s - r) ^ eexp
  have hNormInt : IntervalIntegrable normBound volume 0 s := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := s) htheta0
    have hscaled := (hk.const_mul W).mul_const HF
    have hconst : IntervalIntegrable (fun _ : ℝ => A0) volume 0 s :=
      intervalIntegrable_const
    simpa [normBound, aexp, mul_assoc] using hconst.add hscaled
  have hDiffInt : IntervalIntegrable diffBound volume 0 s := by
    have hk := intervalIntegrable_sub_rpow_hess_Ctheta_to_Ceta
      (t := s) hrel
    have hscaled := hk.const_mul D
    have hconst : IntervalIntegrable (fun _ : ℝ => E0) volume 0 s :=
      intervalIntegrable_const
    simpa [diffBound, eexp, mul_assoc] using hconst.add hscaled
  have hNormPoint : ∀ r, 0 ≤ r → r < s → ∀ q : ℝ,
      ‖wholeLineCauchyHeatHessOp (s - r) (F r).1 q‖ ≤ normBound r := by
    intro r hr0 hrs q
    have hlag : 0 < s - r := sub_pos.mpr hrs
    by_cases hrHalf : r ≤ s / 2
    · have hsHalf : a / 2 ≤ s / 2 := by linarith [hs.1]
      have hlagHalf : a / 2 ≤ s - r := by linarith
      have hpow : (s - r) ^ (-(1 : ℝ)) ≤
          (a / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hglobal := wholeLineCauchyHeatHessOp_abs_le
        hlag hMF (F r).1.continuous.aestronglyMeasurable
        (fun w => (WholeLineBUC.abs_apply_le_norm (F r) w).trans (hFnorm r))
        (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (s - r) (F r).1 q| ≤
            (C2 * (s - r) ^ (-(1 : ℝ))) * MF := by
          simpa [C2, mul_assoc] using hglobal
        _ ≤ A0 := by
          dsimp [A0]
          gcongr
        _ ≤ normBound r := by
          dsimp [normBound]
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hW
              (Real.rpow_nonneg hlag.le _)) hHF)
    · have hrWindow : r ∈ Set.Icc (a / 2) b := by
        constructor
        · have hsr : s / 2 < r := lt_of_not_ge hrHalf
          linarith [hs.1]
        · exact hrs.le.trans hs.2
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag htheta0 htheta1 hHF
        (F r).1.continuous.aestronglyMeasurable
        (fun w => (WholeLineBUC.abs_apply_le_norm (F r) w).trans (hFnorm r))
        (hFholder r hrWindow) (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (s - r) (F r).1 q| ≤
            W * (s - r) ^ aexp * HF := by
          simpa [W, aexp] using hcancel
        _ ≤ normBound r := by
          dsimp [normBound]
          linarith
  have hHessInt : ∀ q : ℝ, IntervalIntegrable
      (fun r : ℝ => wholeLineCauchyHeatHessOp (s - r) (F r).1 q)
      volume 0 s := by
    intro q
    refine IntervalIntegrable.mono_fun'
      (f := fun r : ℝ => wholeLineCauchyHeatHessOp (s - r) (F r).1 q)
      (g := normBound) hNormInt
      (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable
        hFcont s q).restrict ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards with r hr
    rw [Set.uIoc_of_le hs0.le] at hr
    rcases lt_or_eq_of_le hr.2 with hrs | rfl
    · exact hNormPoint r hr.1.le hrs q
    · rw [sub_self, wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl]
      simp only [norm_zero]
      dsimp [normBound]
      exact add_nonneg hA0
        (mul_nonneg (mul_nonneg hW
          (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)) hHF)
  have hDiffPoint : ∀ r, 0 ≤ r → r < s → ∀ q w : ℝ,
      |wholeLineCauchyHeatHessOp (s - r) (F r).1 q -
          wholeLineCauchyHeatHessOp (s - r) (F r).1 w| ≤
        diffBound r * |q - w| ^ eta := by
    intro r hr0 hrs q w
    have hlag : 0 < s - r := sub_pos.mpr hrs
    by_cases hrHalf : r ≤ s / 2
    · have hlagHalf : a / 2 ≤ s - r := by linarith [hs.1]
      have hpow1 : (s - r) ^ (-(1 : ℝ)) ≤
          (a / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hpow3 : (s - r) ^ (-(3 / 2 : ℝ)) ≤
          (a / 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hrBound : ∀ v, |wholeLineCauchyHeatHessOp
          (s - r) (F r).1 v| ≤ A0 := by
        intro v
        have hglobal := wholeLineCauchyHeatHessOp_abs_le
          hlag hMF (F r).1.continuous.aestronglyMeasurable
          (fun w => (WholeLineBUC.abs_apply_le_norm (F r) w).trans (hFnorm r))
          (x := v)
        calc
          |wholeLineCauchyHeatHessOp (s - r) (F r).1 v| ≤
              (C2 * (s - r) ^ (-(1 : ℝ))) * MF := by
            simpa [C2, mul_assoc] using hglobal
          _ ≤ A0 := by
            dsimp [A0]
            gcongr
      have hrLip : ∀ v z, |wholeLineCauchyHeatHessOp
          (s - r) (F r).1 v -
          wholeLineCauchyHeatHessOp (s - r) (F r).1 z| ≤
          B0 * |v - z| := by
        intro v z
        have hlip := wholeLineCauchyHeatHessOp_lipschitz
          hlag hMF (F r).1.continuous.aestronglyMeasurable
          (fun w => (WholeLineBUC.abs_apply_le_norm (F r) w).trans (hFnorm r)) v z
        calc
          |wholeLineCauchyHeatHessOp (s - r) (F r).1 v -
              wholeLineCauchyHeatHessOp (s - r) (F r).1 z| ≤
              (C3 * (s - r) ^ (-(3 / 2 : ℝ)) * MF) * |v - z| := by
            simpa [C3, mul_assoc] using hlip
          _ ≤ B0 * |v - z| := by
            dsimp [B0]
            gcongr
      have hearly := holder_of_local_lipschitz_of_bounded_cauchy
        heta0 heta1.le hB0 hrBound (fun v z _ => hrLip v z) q w
      exact hearly.trans (mul_le_mul_of_nonneg_right
        (le_add_of_le_of_nonneg (le_refl E0)
          (mul_nonneg hD (Real.rpow_nonneg hlag.le _)))
        (Real.rpow_nonneg (abs_nonneg _) _))
    · have hrWindow : r ∈ Set.Icc (a / 2) b := by
        constructor
        · have hsr : s / 2 < r := lt_of_not_ge hrHalf
          linarith [hs.1]
        · exact hrs.le.trans hs.2
      have hlate := wholeLineCauchyHeatHessOp_Ctheta_to_Ceta
        hlag hMF hHF htheta0 htheta1 heta0 heta1
        (F r).1.continuous.aestronglyMeasurable
        (fun v => (WholeLineBUC.abs_apply_le_norm (F r) v).trans (hFnorm r))
        (hFholder r hrWindow) q w
      have hlate' :
          |wholeLineCauchyHeatHessOp (s - r) (F r).1 q -
              wholeLineCauchyHeatHessOp (s - r) (F r).1 w| ≤
            D * (s - r) ^ eexp * |q - w| ^ eta := by
        simpa [D, W, C3, eexp, mul_assoc, mul_left_comm, mul_comm] using hlate
      exact hlate'.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hE0)
        (Real.rpow_nonneg (abs_nonneg _) _))
  have hsub :
      (∫ r in (0 : ℝ)..s,
          wholeLineCauchyHeatHessOp (s - r) (F r).1 x) -
        (∫ r in (0 : ℝ)..s,
          wholeLineCauchyHeatHessOp (s - r) (F r).1 y) =
      ∫ r in (0 : ℝ)..s,
        (wholeLineCauchyHeatHessOp (s - r) (F r).1 x -
          wholeLineCauchyHeatHessOp (s - r) (F r).1 y) := by
    rw [intervalIntegral.integral_sub (hHessInt x) (hHessInt y)]
  rw [hsub, ← Real.norm_eq_abs]
  have hmajor : IntervalIntegrable
      (fun r : ℝ => diffBound r * |x - y| ^ eta) volume 0 s :=
    hDiffInt.mul_const _
  have hintegral :
      (∫ r in (0 : ℝ)..s, diffBound r) =
        E0 * s + D * (s ^ delta / delta) := by
    have hfun : (fun r : ℝ => diffBound r) =
        (fun _ : ℝ => E0) + fun r => D * (s - r) ^ eexp := by
      funext r
      simp [diffBound]
    have hsing : IntervalIntegrable
        (fun r : ℝ => D * (s - r) ^ eexp) volume 0 s := by
      have hbase := (intervalIntegrable_sub_rpow_hess_Ctheta_to_Ceta
        (t := s) hrel).const_mul D
      simpa [eexp] using hbase
    rw [hfun]
    change (∫ r in (0 : ℝ)..s, E0 + D * (s - r) ^ eexp) = _
    rw [intervalIntegral.integral_add intervalIntegrable_const hsing]
    rw [intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul]
    rw [integral_sub_rpow_hess_Ctheta_to_Ceta hs0.le hrel]
    simp [delta]
    ring
  have hcoeff : E0 * s + D * (s ^ delta / delta) ≤ K := by
    dsimp [K]
    have hspow : s ^ delta ≤ b ^ delta :=
      Real.rpow_le_rpow hs0.le hs.2 hdelta.le
    exact add_le_add
      (mul_le_mul_of_nonneg_left hs.2 hE0)
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hspow hdelta.le) hD)
  calc
    ‖∫ r in (0 : ℝ)..s,
        (wholeLineCauchyHeatHessOp (s - r) (F r).1 x -
          wholeLineCauchyHeatHessOp (s - r) (F r).1 y)‖ ≤
        ∫ r in (0 : ℝ)..s, diffBound r * |x - y| ^ eta := by
      apply intervalIntegral.norm_integral_le_of_norm_le hs0.le _ hmajor
      filter_upwards with r
      intro hr
      rcases lt_or_eq_of_le hr.2 with hrs | rfl
      · simpa [Real.norm_eq_abs] using hDiffPoint r hr.1.le hrs x y
      · simp only [sub_self,
            wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl, norm_zero]
        exact mul_nonneg
          (by
            dsimp [diffBound]
            exact add_nonneg hE0
              (mul_nonneg hD
                (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)))
          (Real.rpow_nonneg (abs_nonneg _) _)
    _ = (E0 * s + D * (s ^ delta / delta)) * |x - y| ^ eta := by
      rw [intervalIntegral.integral_mul_const, hintegral]
    _ ≤ K * |x - y| ^ eta :=
      mul_le_mul_of_nonneg_right hcoeff
        (Real.rpow_nonneg (abs_nonneg _) _)

/-- Every slice in a compact positive-time window has a spatial derivative
with one common global `C^eta` coefficient. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc a b, ∀ x y : ℝ,
      |deriv (fun w : ℝ =>
          (wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 w) x -
        deriv (fun w : ℝ =>
          (wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 w) y| ≤
        K * |x - y| ^ eta := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  let Ceta : ℝ :=
    (2 : ℝ) ^ (1 - eta) *
      ((5 * Real.sqrt 2 / 2) ^ eta *
        (2 / Real.sqrt (4 * Real.pi)) ^ (1 - eta))
  let heatExp : ℝ := -((1 + eta) / 2)
  let reacExp : ℝ := (1 - eta) / 2
  let Kheat : ℝ := Ceta * a ^ heatExp * ‖u₀‖
  let Kreac : ℝ := Ceta * MR * (b ^ reacExp / reacExp)
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hMR : 0 ≤ MR := by
    dsimp [MR]
    positivity
  have hCeta : 0 ≤ Ceta := by
    dsimp [Ceta]
    positivity
  have hheatExp : heatExp ≤ 0 := by
    dsimp [heatExp]
    linarith
  have hreacExp : 0 < reacExp := by
    dsimp [reacExp]
    linarith
  have hKheat : 0 ≤ Kheat := by
    dsimp [Kheat]
    positivity
  have hKreac : 0 ≤ Kreac := by
    dsimp [Kreac]
    exact mul_nonneg (mul_nonneg hCeta hMR)
      (div_nonneg (Real.rpow_nonneg hb0 _) hreacExp.le)
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  rcases wholeLineCauchyFluxHessianHistory_Ceta_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel with
    ⟨Kflux, hKflux, hflux⟩
  let K : ℝ := Kheat + |p.χ| * Kflux + Kreac
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro s hs x y
  have hs0 : 0 < s := ha.trans_le hs.1
  have hsT : s ≤ T := hs.2.trans hbT
  let z : Set.Icc (0 : ℝ) T := ⟨s, hs0.le, hsT⟩
  have hext : wholeLineBUCTrajectoryExtend hT U s = U z :=
    wholeLineBUCTrajectoryExtend_eq hT U z.2
  have hdatum : ∀ q, |u₀.1 q| ≤ ‖u₀‖ :=
    fun q => WholeLineBUC.abs_apply_le_norm u₀ q
  have hheat :
      |wholeLineCauchyHeatGradOp s u₀.1 x -
          wholeLineCauchyHeatGradOp s u₀.1 y| ≤
        Kheat * |x - y| ^ eta := by
    have hraw := wholeLineCauchyHeatGradOp_Linf_to_Ctheta
      hs0 (norm_nonneg u₀) heta0 heta1
      u₀.1.continuous.aestronglyMeasurable hdatum x y
    have hpow : s ^ heatExp ≤ a ^ heatExp := by
      exact Real.rpow_le_rpow_of_nonpos ha hs.1 hheatExp
    have hraw' :
        |wholeLineCauchyHeatGradOp s u₀.1 x -
            wholeLineCauchyHeatGradOp s u₀.1 y| ≤
          (Ceta * s ^ heatExp * ‖u₀‖) * |x - y| ^ eta := by
      simpa [Ceta, heatExp, mul_assoc, mul_left_comm, mul_comm] using hraw
    exact hraw'.trans (mul_le_mul_of_nonneg_right
      (by
        dsimp [Kheat]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hCeta) (norm_nonneg u₀))
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hreac :
      |wholeLineCauchyGradientHistory R s x -
          wholeLineCauchyGradientHistory R s y| ≤
        Kreac * |x - y| ^ eta := by
    have hraw := wholeLineCauchyGradientHistory_Ctheta
      hRcont hs0 hMR heta0 heta1 hRnorm x y
    have hpow : s ^ reacExp ≤ b ^ reacExp :=
      Real.rpow_le_rpow hs0.le hs.2 hreacExp.le
    have hraw' :
        |wholeLineCauchyGradientHistory R s x -
            wholeLineCauchyGradientHistory R s y| ≤
          (Ceta * MR * (s ^ reacExp / reacExp)) * |x - y| ^ eta := by
      simpa [Ceta, reacExp, mul_assoc, mul_left_comm, mul_comm] using hraw
    exact hraw'.trans (mul_le_mul_of_nonneg_right
      (by
        dsimp [Kreac]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hpow hreacExp.le)
          (mul_nonneg hCeta hMR))
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hderiv : ∀ q : ℝ,
      deriv (fun w : ℝ =>
        (wholeLineBUCTrajectoryExtend hT U s).1 w) q =
        wholeLineCauchyHeatGradOp s u₀.1 q +
          (-p.χ) *
            (∫ r in (0 : ℝ)..s,
              wholeLineCauchyHeatHessOp (s - r) (F r).1 q) +
          wholeLineCauchyGradientHistory R s q := by
    intro q
    have h := (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hs0 q).deriv
    simpa [U, F, R, hext, wholeLineCauchyGradientHistory] using h
  rw [hderiv x, hderiv y]
  let Hx : ℝ := wholeLineCauchyHeatGradOp s u₀.1 x
  let Hy : ℝ := wholeLineCauchyHeatGradOp s u₀.1 y
  let Fx : ℝ := ∫ r in (0 : ℝ)..s,
    wholeLineCauchyHeatHessOp (s - r) (F r).1 x
  let Fy : ℝ := ∫ r in (0 : ℝ)..s,
    wholeLineCauchyHeatHessOp (s - r) (F r).1 y
  let Rx : ℝ := wholeLineCauchyGradientHistory R s x
  let Ry : ℝ := wholeLineCauchyGradientHistory R s y
  have htriangle :
      |(Hx + (-p.χ) * Fx + Rx) - (Hy + (-p.χ) * Fy + Ry)| ≤
        |Hx - Hy| + |p.χ| * |Fx - Fy| + |Rx - Ry| := by
    calc
      |(Hx + (-p.χ) * Fx + Rx) - (Hy + (-p.χ) * Fy + Ry)| =
          |(Hx - Hy) + (-p.χ) * (Fx - Fy) + (Rx - Ry)| := by ring_nf
      _ ≤ |(Hx - Hy) + (-p.χ) * (Fx - Fy)| + |Rx - Ry| :=
        abs_add_le _ _
      _ ≤ (|Hx - Hy| + |(-p.χ) * (Fx - Fy)|) + |Rx - Ry| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = |Hx - Hy| + |p.χ| * |Fx - Fy| + |Rx - Ry| := by
        rw [abs_mul, abs_neg]
  calc
    |wholeLineCauchyHeatGradOp s u₀.1 x + (-p.χ) * Fx + Rx -
        (wholeLineCauchyHeatGradOp s u₀.1 y + (-p.χ) * Fy + Ry)| ≤
        |Hx - Hy| + |p.χ| * |Fx - Fy| + |Rx - Ry| := by
      simpa [Hx, Hy] using htriangle
    _ ≤ Kheat * |x - y| ^ eta +
          |p.χ| * (Kflux * |x - y| ^ eta) +
          Kreac * |x - y| ^ eta := by
      exact add_le_add
        (add_le_add hheat (mul_le_mul_of_nonneg_left
          (hflux s hs x y) (abs_nonneg p.χ))) hreac
    _ = K * |x - y| ^ eta := by
      dsimp [K]
      ring

/-- On a physical positive-time window, the common derivative Holder bound
and the population strip give one common global bound for `u_x`. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ s ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x ∈
          Set.Icc (0 : ℝ) M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc a b, ∀ x,
      |deriv (fun w : ℝ =>
        (wholeLineBUCTrajectoryExtend hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 w) x| ≤ B := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel with
    ⟨H, hH, hholder⟩
  let B : ℝ := H + 2 * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro s hs x
  have hs0 : 0 < s := ha.trans_le hs.1
  have hsT : s ≤ T := hs.2.trans hbT
  let z : Set.Icc (0 : ℝ) T := ⟨s, hs0.le, hsT⟩
  have hext : wholeLineBUCTrajectoryExtend hT U s = U z :=
    wholeLineBUCTrajectoryExtend_eq hT U z.2
  let f : ℝ → ℝ := fun w =>
    (wholeLineBUCTrajectoryExtend hT U s).1 w
  have hbound : ∀ q, |f q| ≤ M := by
    intro q
    rw [abs_of_nonneg (hstrip s hs q).1]
    exact (hstrip s hs q).2
  have hdiff : ∀ q, DifferentiableAt ℝ f q := by
    intro q
    have h := (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hs0 q).differentiableAt
    simpa [f, U, hext] using h
  have hfholder : ∀ q r,
      |deriv f q - deriv f r| ≤ H * |q - r| ^ eta := by
    intro q r
    simpa [f, U] using hholder s hs q r
  dsimp [B]
  exact deriv_abs_le_of_bounded_of_deriv_holder
    hH heta0 hbound hdiff hfholder x

section WholeLineCauchyC2BootstrapAxiomAudit

#print axioms wholeLineCauchyHeatHessOp_eq_gradOp_deriv
#print axioms integral_sub_rpow_hess_Ctheta_to_Ceta
#print axioms wholeLineCauchyFluxHessianHistory_Ceta_window
#print axioms wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta_window
#print axioms
  wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window

end WholeLineCauchyC2BootstrapAxiomAudit

end ShenWork.Paper1
