import ShenWork.Paper1.WholeLineCauchyFluxHolderBootstrap

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Holder regularity of the positive-time spatial derivative

The first spatial derivative contains a Hessian Duhamel history.  To control
its spatial Holder modulus, interpolate the cancellative Hessian sup bound
against the third-kernel Lipschitz bound.  The resulting time exponent is
integrable after choosing the output exponent strictly below
`theta / (1 + theta)`.
-/

lemma one_div_mul_sqrt_eq_rpow_neg_three_half
    {t : ℝ} (ht : 0 < t) :
    1 / (t * Real.sqrt t) = t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hst : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  have hmul : t * t ^ (1 / 2 : ℝ) = t ^ (3 / 2 : ℝ) := by
    calc
      t * t ^ (1 / 2 : ℝ) = t ^ (1 : ℝ) * t ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + 1 / 2) :=
        (Real.rpow_add ht (1 : ℝ) (1 / 2 : ℝ)).symm
      _ = t ^ (3 / 2 : ℝ) := by
        congr 1
        ring
  rw [hmul]
  rw [one_div]

/-- The whole-line modified heat Hessian is globally Lipschitz at positive
lag, with the third-kernel `t^(-3/2)` scale. -/
theorem wholeLineCauchyHeatHessOp_lipschitz
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x y : ℝ) :
    |wholeLineCauchyHeatHessOp t f x - wholeLineCauchyHeatHessOp t f y| ≤
      (heatThirdTailConstant * t ^ (-(3 / 2 : ℝ)) * M) * |x - y| := by
  let g : ℝ → ℝ := fun z => wholeLineCauchyHeatHessOp t f z
  let C : ℝ := heatThirdTailConstant * t ^ (-(3 / 2 : ℝ)) * M
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt g (deriv g z) Set.univ z := by
    intro z _hz
    exact (wholeLineCauchyHeatHessOp_hasDerivAt ht hf_meas hf
      (x := z)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv g z‖ ≤ C := by
    intro z _hz
    have hz := wholeLineCauchyHeatHessOp_hasDerivAt ht hf_meas hf (x := z)
    rw [Real.norm_eq_abs, hz.deriv]
    have hthird := wholeLineCauchyHeatThirdOp_abs_le ht hM hf_meas hf (x := z)
    calc
      |wholeLineCauchyHeatThirdOp t f z| ≤
          (heatThirdTailConstant / (t * Real.sqrt t)) * M := hthird
      _ = C := by
        rw [show heatThirdTailConstant / (t * Real.sqrt t) =
            heatThirdTailConstant * (1 / (t * Real.sqrt t)) by ring,
          one_div_mul_sqrt_eq_rpow_neg_three_half ht]
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (𝕜 := ℝ) (G := ℝ) (f := g) (s := Set.univ)
    hderiv hbound convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [g, C, Real.norm_eq_abs, abs_sub_comm] using hmv

/-- Interpolating the cancellative Hessian sup estimate with the
third-kernel Lipschitz estimate gives a `C^eta` Hessian bound. -/
theorem wholeLineCauchyHeatHessOp_Ctheta_to_Ceta
    {f : ℝ → ℝ} {t M H theta eta : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hf_holder : ∀ a b, |f a - f b| ≤ H * |a - b| ^ theta)
    (x y : ℝ) :
    |wholeLineCauchyHeatHessOp t f x -
        wholeLineCauchyHeatHessOp t f y| ≤
      ((2 * ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta * H) ^
          (1 - eta) *
        (heatThirdTailConstant * M) ^ eta) *
        t ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ) *
        |x - y| ^ eta := by
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let C3 : ℝ := heatThirdTailConstant
  let aexp : ℝ := -1 + theta / 2
  let A : ℝ := (W * H) * t ^ aexp
  let B : ℝ := (C3 * M) * t ^ (-(3 / 2 : ℝ))
  have hW : 0 ≤ W := by
    dsimp [W]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact heatThirdTailConstant_nonneg
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hxA : |wholeLineCauchyHeatHessOp t f x| ≤ A := by
    have h := wholeLineCauchyHeatHessOp_Ctheta_abs_le
      ht htheta0 htheta1 hH hf_meas hf hf_holder (x := x)
    simpa [A, W, aexp, mul_assoc, mul_left_comm, mul_comm] using h
  have hyA : |wholeLineCauchyHeatHessOp t f y| ≤ A := by
    have h := wholeLineCauchyHeatHessOp_Ctheta_abs_le
      ht htheta0 htheta1 hH hf_meas hf hf_holder (x := y)
    simpa [A, W, aexp, mul_assoc, mul_left_comm, mul_comm] using h
  have hval : |wholeLineCauchyHeatHessOp t f x -
      wholeLineCauchyHeatHessOp t f y| ≤ 2 * A := by
    calc
      |wholeLineCauchyHeatHessOp t f x - wholeLineCauchyHeatHessOp t f y| ≤
          |wholeLineCauchyHeatHessOp t f x| +
            |wholeLineCauchyHeatHessOp t f y| := abs_sub _ _
      _ ≤ A + A := add_le_add hxA hyA
      _ = 2 * A := by ring
  have hlip : |wholeLineCauchyHeatHessOp t f x -
      wholeLineCauchyHeatHessOp t f y| ≤ B * |x - y| := by
    simpa [B, C3, mul_assoc, mul_left_comm, mul_comm] using
      wholeLineCauchyHeatHessOp_lipschitz ht hM hf_meas hf x y
  let a : ℝ := 2 * A
  let b : ℝ := B * |x - y|
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hchain :
      |wholeLineCauchyHeatHessOp t f x -
          wholeLineCauchyHeatHessOp t f y| ≤
        a ^ (1 - eta) * b ^ eta :=
    (le_min hval hlip).trans
      (min_le_rpow_interp ha hb heta0.le heta1.le)
  have hatime :
      (t ^ aexp) ^ (1 - eta) = t ^ (aexp * (1 - eta)) := by
    rw [← Real.rpow_mul ht.le]
  have hbtime :
      (t ^ (-(3 / 2 : ℝ))) ^ eta = t ^ (-(3 / 2 : ℝ) * eta) := by
    rw [← Real.rpow_mul ht.le]
  have hapow :
      a ^ (1 - eta) =
        (2 * W * H) ^ (1 - eta) * t ^ (aexp * (1 - eta)) := by
    rw [show a = (2 * W * H) * t ^ aexp by
      dsimp [a, A]
      ring]
    rw [Real.mul_rpow (by positivity)
      (Real.rpow_nonneg ht.le _), hatime]
  have hbpow :
      b ^ eta = (C3 * M) ^ eta * t ^ (-(3 / 2 : ℝ) * eta) *
        |x - y| ^ eta := by
    rw [show b = ((C3 * M) * t ^ (-(3 / 2 : ℝ))) * |x - y| by rfl]
    rw [Real.mul_rpow hB (abs_nonneg _),
      Real.mul_rpow (mul_nonneg hC3 hM)
        (Real.rpow_nonneg ht.le _), hbtime]
  have htime :
      t ^ (aexp * (1 - eta)) * t ^ (-(3 / 2 : ℝ) * eta) =
        t ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ) := by
    rw [← Real.rpow_add ht]
    dsimp [aexp]
    congr 1
    ring
  rw [hapow, hbpow] at hchain
  rw [show
      (2 * W * H) ^ (1 - eta) * t ^ (aexp * (1 - eta)) *
          ((C3 * M) ^ eta * t ^ (-(3 / 2 : ℝ) * eta) *
            |x - y| ^ eta) =
        ((2 * W * H) ^ (1 - eta) * (C3 * M) ^ eta) *
          (t ^ (aexp * (1 - eta)) * t ^ (-(3 / 2 : ℝ) * eta)) *
          |x - y| ^ eta by ring,
    htime] at hchain
  simpa [W, C3] using hchain

/-- The new Hessian Holder time exponent is integrable precisely under the
strict interpolation restriction used by the next Duhamel rung. -/
theorem intervalIntegrable_sub_rpow_hess_Ctheta_to_Ceta
    {t theta eta : ℝ} (hrel : eta * (1 + theta) < theta) :
    IntervalIntegrable
      (fun s : ℝ =>
        (t - s) ^ (-1 + (theta - eta * (1 + theta)) / 2 : ℝ))
      volume 0 t := by
  have hexp : (-1 : ℝ) <
      -1 + (theta - eta * (1 + theta)) / 2 := by linarith
  have hbase := intervalIntegral.intervalIntegrable_rpow'
    (a := 0) (b := t) hexp
  have hshift := (hbase.comp_sub_left t).symm
  simpa using hshift

/-- The Hessian history of the canonical chemotaxis flux is spatially
`C^eta` at every positive target time. -/
theorem wholeLineCauchyFluxHessianHistory_Ceta
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ,
      |(∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatHessOp (z.1 - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) -
        (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatHessOp (z.1 - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 y)| ≤
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
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < z.1 / 2 := by positivity
  rcases exists_wholeLineCauchyFluxSourceTrajectory_window_Ctheta
      p hM hT hhalf z.2.2 u₀ hsmall htheta0 htheta1 with
    ⟨HF, hHF, hFholder⟩
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let C2 : ℝ := 5 * Real.sqrt 2 / 2
  let C3 : ℝ := heatThirdTailConstant
  let aexp : ℝ := -1 + theta / 2
  let eexp : ℝ := -1 + (theta - eta * (1 + theta)) / 2
  let A0 : ℝ := C2 * (z.1 / 2) ^ (-(1 : ℝ)) * MF
  let B0 : ℝ := C3 * (z.1 / 2) ^ (-(3 / 2 : ℝ)) * MF
  let E0 : ℝ := max B0 (2 * A0)
  let D : ℝ := (2 * W * HF) ^ (1 - eta) * (C3 * MF) ^ eta
  let normBound : ℝ → ℝ := fun s =>
    A0 + W * (z.1 - s) ^ aexp * HF
  let diffBound : ℝ → ℝ := fun s =>
    E0 + D * (z.1 - s) ^ eexp
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
  have hNormInt : IntervalIntegrable normBound volume 0 z.1 := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := z.1) htheta0
    have hscaled := (hk.const_mul W).mul_const HF
    have hconst : IntervalIntegrable (fun _ : ℝ => A0) volume 0 z.1 :=
      intervalIntegrable_const
    simpa [normBound, aexp, mul_assoc] using hconst.add hscaled
  have hDiffInt : IntervalIntegrable diffBound volume 0 z.1 := by
    have hk := intervalIntegrable_sub_rpow_hess_Ctheta_to_Ceta
      (t := z.1) hrel
    have hscaled := hk.const_mul D
    have hconst : IntervalIntegrable (fun _ : ℝ => E0) volume 0 z.1 :=
      intervalIntegrable_const
    simpa [diffBound, eexp, mul_assoc] using hconst.add hscaled
  have hNormPoint : ∀ s, 0 ≤ s → s < z.1 → ∀ q : ℝ,
      ‖wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q‖ ≤ normBound s := by
    intro s hs0 hst q
    have hlag : 0 < z.1 - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ z.1 / 2
    · have hlagHalf : z.1 / 2 ≤ z.1 - s := by linarith
      have hpow : (z.1 - s) ^ (-(1 : ℝ)) ≤
          (z.1 / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hglobal := wholeLineCauchyHeatHessOp_abs_le
        hlag hMF (F s).1.continuous.aestronglyMeasurable
        (fun r => (WholeLineBUC.abs_apply_le_norm (F s) r).trans (hFnorm s))
        (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q| ≤
            (C2 * (z.1 - s) ^ (-(1 : ℝ))) * MF := by
          simpa [C2, mul_assoc] using hglobal
        _ ≤ A0 := by
          dsimp [A0]
          gcongr
        _ ≤ normBound s := by
          dsimp [normBound]
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hW
              (Real.rpow_nonneg hlag.le _)) hHF)
    · have hsWindow : s ∈ Set.Icc (z.1 / 2) z.1 :=
        ⟨le_of_not_ge hsHalf, hst.le⟩
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag htheta0 htheta1 hHF
        (F s).1.continuous.aestronglyMeasurable
        (fun r => (WholeLineBUC.abs_apply_le_norm (F s) r).trans (hFnorm s))
        (hFholder s hsWindow) (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q| ≤
            W * (z.1 - s) ^ aexp * HF := by
          simpa [W, aexp] using hcancel
        _ ≤ normBound s := by
          dsimp [normBound]
          linarith
  have hHessInt : ∀ q : ℝ, IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q)
      volume 0 z.1 := by
    intro q
    refine IntervalIntegrable.mono_fun'
      (f := fun s : ℝ => wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q)
      (g := normBound) hNormInt
      (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable
        hFcont z.1 q).restrict ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards with s hs
    rw [Set.uIoc_of_le hz.le] at hs
    rcases lt_or_eq_of_le hs.2 with hst | rfl
    · exact hNormPoint s hs.1.le hst q
    · rw [sub_self, wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl]
      simp only [norm_zero]
      dsimp [normBound]
      exact add_nonneg hA0
        (mul_nonneg (mul_nonneg hW
          (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)) hHF)
  have hDiffPoint : ∀ s, 0 ≤ s → s < z.1 → ∀ x y : ℝ,
      |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 x -
          wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 y| ≤
        diffBound s * |x - y| ^ eta := by
    intro s hs0 hst x y
    have hlag : 0 < z.1 - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ z.1 / 2
    · have hlagHalf : z.1 / 2 ≤ z.1 - s := by linarith
      have hpow1 : (z.1 - s) ^ (-(1 : ℝ)) ≤
          (z.1 / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hpow3 : (z.1 - s) ^ (-(3 / 2 : ℝ)) ≤
          (z.1 / 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hsBound : ∀ q, |wholeLineCauchyHeatHessOp
          (z.1 - s) (F s).1 q| ≤ A0 := by
        intro q
        have hglobal := wholeLineCauchyHeatHessOp_abs_le
          hlag hMF (F s).1.continuous.aestronglyMeasurable
          (fun r => (WholeLineBUC.abs_apply_le_norm (F s) r).trans (hFnorm s))
          (x := q)
        calc
          |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q| ≤
              (C2 * (z.1 - s) ^ (-(1 : ℝ))) * MF := by
            simpa [C2, mul_assoc] using hglobal
          _ ≤ A0 := by
            dsimp [A0]
            gcongr
      have hsLip : ∀ q r, |wholeLineCauchyHeatHessOp
          (z.1 - s) (F s).1 q -
          wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 r| ≤
          B0 * |q - r| := by
        intro q r
        have hlip := wholeLineCauchyHeatHessOp_lipschitz
          hlag hMF (F s).1.continuous.aestronglyMeasurable
          (fun w => (WholeLineBUC.abs_apply_le_norm (F s) w).trans (hFnorm s)) q r
        calc
          |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q -
              wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 r| ≤
              (C3 * (z.1 - s) ^ (-(3 / 2 : ℝ)) * MF) * |q - r| := by
            simpa [C3, mul_assoc] using hlip
          _ ≤ B0 * |q - r| := by
            dsimp [B0]
            gcongr
      have hearly := holder_of_local_lipschitz_of_bounded_cauchy
        heta0 heta1.le hB0 hsBound (fun q r _ => hsLip q r) x y
      exact hearly.trans (mul_le_mul_of_nonneg_right
        (le_add_of_le_of_nonneg (le_refl E0)
          (mul_nonneg hD (Real.rpow_nonneg hlag.le _)))
        (Real.rpow_nonneg (abs_nonneg _) _))
    · have hsWindow : s ∈ Set.Icc (z.1 / 2) z.1 :=
        ⟨le_of_not_ge hsHalf, hst.le⟩
      have hlate := wholeLineCauchyHeatHessOp_Ctheta_to_Ceta
        hlag hMF hHF htheta0 htheta1 heta0 heta1
        (F s).1.continuous.aestronglyMeasurable
        (fun r => (WholeLineBUC.abs_apply_le_norm (F s) r).trans (hFnorm s))
        (hFholder s hsWindow) x y
      have hlate' :
          |wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 x -
              wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 y| ≤
            D * (z.1 - s) ^ eexp * |x - y| ^ eta := by
        simpa [D, W, C3, eexp, mul_assoc, mul_left_comm, mul_comm] using hlate
      exact hlate'.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hE0)
        (Real.rpow_nonneg (abs_nonneg _) _))
  let K : ℝ := ∫ s in (0 : ℝ)..z.1, diffBound s
  have hK : 0 ≤ K := by
    dsimp [K]
    apply intervalIntegral.integral_nonneg hz.le
    intro s hs
    dsimp [diffBound]
    exact add_nonneg hE0
      (mul_nonneg hD (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
  refine ⟨K, hK, ?_⟩
  intro x y
  have hsub :
      (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 x) -
        (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 y) =
      ∫ s in (0 : ℝ)..z.1,
        (wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 x -
          wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 y) := by
    rw [intervalIntegral.integral_sub (hHessInt x) (hHessInt y)]
  rw [hsub, ← Real.norm_eq_abs]
  have hmajor : IntervalIntegrable
      (fun s : ℝ => diffBound s * |x - y| ^ eta) volume 0 z.1 :=
    hDiffInt.mul_const _
  calc
    ‖∫ s in (0 : ℝ)..z.1,
        (wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 x -
          wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 y)‖ ≤
        ∫ s in (0 : ℝ)..z.1, diffBound s * |x - y| ^ eta := by
      apply intervalIntegral.norm_integral_le_of_norm_le hz.le _ hmajor
      filter_upwards with s
      intro hs
      rcases lt_or_eq_of_le hs.2 with hst | rfl
      · simpa [Real.norm_eq_abs] using hDiffPoint s hs.1.le hst x y
      · simp only [sub_self,
            wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl, norm_zero]
        exact mul_nonneg
          (by
            dsimp [diffBound]
            exact add_nonneg hE0
              (mul_nonneg hD
                (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)))
          (Real.rpow_nonneg (abs_nonneg _) _)
    _ = K * |x - y| ^ eta := by
      dsimp [K]
      rw [intervalIntegral.integral_mul_const]

section WholeLineCauchyC1HolderBootstrapAxiomAudit

#print axioms wholeLineCauchyHeatHessOp_lipschitz
#print axioms wholeLineCauchyHeatHessOp_Ctheta_to_Ceta
#print axioms intervalIntegrable_sub_rpow_hess_Ctheta_to_Ceta
#print axioms wholeLineCauchyFluxHessianHistory_Ceta

end WholeLineCauchyC1HolderBootstrapAxiomAudit

end ShenWork.Paper1
