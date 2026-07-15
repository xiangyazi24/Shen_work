import ShenWork.Paper1.WholeLineCauchyCanonicalSegments
import ShenWork.Paper1.WholeLineCauchyC2Bootstrap
import ShenWork.Paper1.WholeLineCauchyBUCHeatContinuity

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Quantitative positive-time BUC modulus for the canonical Cauchy solution

The estimate is obtained from the exact canonical restart, rather than from
the qualitative time-continuity theorem.  On a positive-time window the
spatial derivative has a common bound.  The restarted homogeneous heat term
therefore moves by `O(sqrt h)` in BUC; the divergence and value Duhamel legs
move by `O(sqrt h)` and `O(h)`, respectively.
-/

private theorem one_sub_exp_neg_le_self
    (t : ℝ) :
    1 - Real.exp (-t) ≤ t := by
  have h := Real.add_one_le_exp (-t)
  linarith

private theorem le_sqrt_of_mem_Icc_zero_one
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t ≤ Real.sqrt t := by
  have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt1 : Real.sqrt t ≤ 1 := by
    simpa using Real.sqrt_le_sqrt ht.2
  nlinarith [Real.sq_sqrt ht.1]

private theorem sqrt_sqrt_rpow_eq_quarter_rpow
    {d rho : ℝ} (hd : 0 ≤ d) :
    (Real.sqrt (Real.sqrt d)) ^ rho = d ^ (rho / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hd, ← Real.rpow_mul hd]
  congr 1
  ring

/-- A bounded Lipschitz datum moves by an explicit `O(h) + O(sqrt h)`
amount under the modified whole-line heat flow. -/
theorem wholeLineCauchyHeatBUCTotal_dist_self_le_of_lipschitz
    {t M L : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L)
    (f : WholeLineBUC) (hfnorm : ‖f‖ ≤ M)
    (hlip : ∀ x y : ℝ, |f.1 y - f.1 x| ≤ L * |y - x|) :
    dist (wholeLineCauchyHeatBUCTotal t f) f ≤
      M * t + 2 * L * Real.sqrt t := by
  by_cases ht0 : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let H : WholeLineBUC := wholeLineHeatBUC t htpos f
  have hordinary : dist H f ≤
      L * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
    simpa [H] using
      (wholeLineHeatBUC_dist_le_of_linear_modulus
        (t := t) (A := 0) (C := L) htpos f (by
          intro x y
          simpa using hlip x y))
  have hordinary' : dist H f ≤ 2 * L * Real.sqrt t := by
    calc
      dist H f ≤ L * (4 * t / Real.sqrt (4 * Real.pi * t)) := hordinary
      _ ≤ L * (2 * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left
          (heatKernel_first_abs_moment_le_two_sqrt htpos) hL
      _ = 2 * L * Real.sqrt t := by ring
  have hexp0 : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  have hexp1 : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have habsexp : |Real.exp (-t) - 1| ≤ t := by
    rw [abs_of_nonpos (by linarith)]
    simpa [sub_eq_add_neg] using one_sub_exp_neg_le_self t
  have htotal : wholeLineCauchyHeatBUCTotal t f =
      Real.exp (-t) • H := by
    simp [wholeLineCauchyHeatBUCTotal, htpos, H,
      wholeLineCauchyHeatBUC_eq_smul]
  rw [htotal]
  have hdist_smul :
      dist (Real.exp (-t) • H) (Real.exp (-t) • f) =
        |Real.exp (-t)| * dist H f := by
    rw [WholeLineBUC.dist_eq_norm_sub]
    have heq : Real.exp (-t) • H - Real.exp (-t) • f =
        Real.exp (-t) • (H - f) := by module
    rw [heq, norm_smul, Real.norm_eq_abs,
      ← WholeLineBUC.dist_eq_norm_sub]
  have hdist_self : dist (Real.exp (-t) • f) f =
      |Real.exp (-t) - 1| * ‖f‖ := by
    rw [WholeLineBUC.dist_eq_norm_sub]
    have heq : Real.exp (-t) • f - f =
        (Real.exp (-t) - 1) • f := by module
    rw [heq, norm_smul, Real.norm_eq_abs]
  calc
    dist (Real.exp (-t) • H) f ≤
        dist (Real.exp (-t) • H) (Real.exp (-t) • f) +
          dist (Real.exp (-t) • f) f := dist_triangle _ _ _
    _ = Real.exp (-t) * dist H f +
        |Real.exp (-t) - 1| * ‖f‖ := by
      rw [hdist_smul, hdist_self, abs_of_nonneg hexp0]
    _ ≤ 1 * (2 * L * Real.sqrt t) + t * M := by
      exact add_le_add
        (mul_le_mul hexp1 hordinary' (dist_nonneg) (by norm_num))
        (mul_le_mul habsexp hfnorm (norm_nonneg _) ht)
    _ = M * t + 2 * L * Real.sqrt t := by ring

/-- The canonical displacement on a restart interval of length at most one
is bounded by an explicit multiple of the square root of its length. -/
theorem wholeLineCauchyBUCMildDisplacement_le_sqrt
    (p : CMParams) {M h : ℝ} (hM : 0 ≤ M)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) :
    wholeLineCauchyBUCMildDisplacement p M h ≤
      (2 * |p.χ| *
          ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) +
        (M + M * (1 + M ^ p.α))) * Real.sqrt h := by
  have hsqrt : h ≤ Real.sqrt h := le_sqrt_of_mem_Icc_zero_one hh
  have hA : 0 ≤
      (2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ) := by
    positivity
  have hR : 0 ≤ M + M * (1 + M ^ p.α) := by positivity
  unfold wholeLineCauchyBUCMildDisplacement
  calc
    |p.χ| *
          (((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
            (2 * Real.sqrt h)) +
        (M + M * (1 + M ^ p.α)) * h
        ≤ |p.χ| *
          (((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
            (2 * Real.sqrt h)) +
          (M + M * (1 + M ^ p.α)) * Real.sqrt h := by
            gcongr
    _ = (2 * |p.χ| *
          ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) +
        (M + M * (1 + M ^ p.α))) * Real.sqrt h := by ring

/-- Coefficient selected after the common positive-window spatial derivative
bound has been produced. -/
def wholeLineCauchyBUCTimeSqrtConst
    (p : CMParams) (M B : ℝ) : ℝ :=
  M + 2 * B +
    2 * |p.χ| *
      ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) +
    (M + M * (1 + M ^ p.α))

theorem wholeLineCauchyBUCTimeSqrtConst_nonneg
    (p : CMParams) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) :
    0 ≤ wholeLineCauchyBUCTimeSqrtConst p M B := by
  unfold wholeLineCauchyBUCTimeSqrtConst
  positivity

/-- On every compact strictly-positive time window, the canonical Cauchy
fixed point is uniformly `1/2`-Hölder in time in the genuine BUC metric.

The constant is obtained internally from the already proved common spatial
derivative bound; no time-regularity or generator bound is assumed. -/
theorem exists_wholeLineCauchyBUCMildFixedPoint_time_sqrt_holder_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        |t - s| ≤ 1 →
        dist
          (wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t)
          (wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s) ≤
          H * |t - s| ^ (1 / 2 : ℝ) := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  have hstripWindow : ∀ q ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U q).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro q hq x
    have hq0 : 0 ≤ q := ha.le.trans hq.1
    have hqT : q ≤ T := hq.2.trans hbT
    let zq : Set.Icc (0 : ℝ) T := ⟨q, hq0, hqT⟩
    have hext : wholeLineBUCTrajectoryExtend hT U q = U zq :=
      wholeLineBUCTrajectoryExtend_eq hT U zq.2
    rw [hext]
    exact hstrip zq x
  rcases
      wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window
        p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
          heta0 heta1 hrel hstripWindow with
    ⟨B, hB, hderiv⟩
  let H : ℝ := wholeLineCauchyBUCTimeSqrtConst p M B
  have hH : 0 ≤ H :=
    wholeLineCauchyBUCTimeSqrtConst_nonneg p hM hB
  refine ⟨H, hH, ?_⟩
  have hforward : ∀ {s t : ℝ}, s ∈ Set.Icc a b → t ∈ Set.Icc a b →
      s ≤ t → t - s ≤ 1 →
      dist (wholeLineBUCTrajectoryExtend hT U t)
          (wholeLineBUCTrajectoryExtend hT U s) ≤
        H * Real.sqrt (t - s) := by
    intro s t hs ht hst hdt
    let h : ℝ := t - s
    have hh0 : 0 ≤ h := by dsimp [h]; linarith
    have hh1 : h ≤ 1 := by simpa [h] using hdt
    by_cases hhzero : h = 0
    · have hts : t = s := by dsimp [h] at hhzero; linarith
      subst t
      simp
    have hh : 0 < h := lt_of_le_of_ne hh0 (Ne.symm hhzero)
    have hs0 : 0 < s := ha.trans_le hs.1
    have htT : t ≤ T := ht.2.trans hbT
    have hshT : s + h ≤ T := by dsimp [h]; linarith
    have hhT : h ≤ T := by
      dsimp [h]
      have hs_nonneg : 0 ≤ s := hs0.le
      linarith
    have hsmallh : wholeLineCauchyBUCMildRate p M h < 1 :=
      (wholeLineCauchyBUCMildRate_mono p hM hh0 hhT).trans_lt hsmall
    let zs : Set.Icc (0 : ℝ) T :=
      ⟨s, hs0.le, (le_add_of_nonneg_right hh0).trans hshT⟩
    let zt : Set.Icc (0 : ℝ) T := ⟨t, (ha.trans_le ht.1).le, htT⟩
    let V : WholeLineBUCTrajectory h :=
      wholeLineCauchyBUCMildFixedPoint p hM hh0 (U zs) hsmallh
    let zh : Set.Icc (0 : ℝ) h := ⟨h, hh0, le_rfl⟩
    have hshift := wholeLineCauchyBUCMildFixedPoint_shift_eq
      p hM hT u₀ hsmall hs0 hh hshT hsmallh hstrip
    have hshiftAt := congrArg (fun W : WholeLineBUCTrajectory h => W zh) hshift
    have hVt : V zh = U zt := by
      simpa [V, U, zs, zt, zh, h] using hshiftAt.symm
    have hnorm : ‖U zs‖ ≤ M := by
      change ‖(U zs).1‖ ≤ M
      refine (BoundedContinuousFunction.norm_le hM).2 ?_
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (hstrip zs x).1]
      exact (hstrip zs x).2
    have hdiff : ∀ x, DifferentiableAt ℝ (U zs).1 x := by
      intro x
      simpa [U] using
        (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
          p hM hT u₀ hsmall zs hs0 x).differentiableAt
    have hderivB : ∀ x, |deriv (U zs).1 x| ≤ B := by
      intro x
      have hext : wholeLineBUCTrajectoryExtend hT U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT U zs.2
      have hbx := hderiv s hs x
      rw [hext] at hbx
      exact hbx
    have hlip : ∀ x y : ℝ, |(U zs).1 y - (U zs).1 x| ≤
        B * |y - x| := by
      intro x y
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Set.univ) (f := (U zs).1) (C := B)
        (fun w _ => hdiff w)
        (fun w _ => by rw [Real.norm_eq_abs]; exact hderivB w)
        convex_univ (Set.mem_univ x) (Set.mem_univ y)
      simpa [Real.norm_eq_abs] using hmv
    have hheat :=
      wholeLineCauchyHeatBUCTotal_dist_self_le_of_lipschitz
        hh0 hB (U zs) hnorm hlip
    have hhom := wholeLineCauchyBUCMildFixedPoint_dist_homogeneous_le
      p hM hh0 (U zs) hsmallh zh
    have hdisp := wholeLineCauchyBUCMildDisplacement_le_sqrt
      p hM (show h ∈ Set.Icc (0 : ℝ) 1 from ⟨hh0, hh1⟩)
    have hhsqrt : h ≤ Real.sqrt h :=
      le_sqrt_of_mem_Icc_zero_one ⟨hh0, hh1⟩
    have hheat' : dist (wholeLineCauchyHeatBUCTotal h (U zs)) (U zs) ≤
        (M + 2 * B) * Real.sqrt h := by
      calc
        dist (wholeLineCauchyHeatBUCTotal h (U zs)) (U zs) ≤
            M * h + 2 * B * Real.sqrt h := hheat
        _ ≤ M * Real.sqrt h + 2 * B * Real.sqrt h := by
          gcongr
        _ = (M + 2 * B) * Real.sqrt h := by ring
    rw [hVt] at hhom
    calc
      dist (wholeLineBUCTrajectoryExtend hT U t)
          (wholeLineBUCTrajectoryExtend hT U s) = dist (U zt) (U zs) := by
            rw [wholeLineBUCTrajectoryExtend_eq hT U zt.2,
              wholeLineBUCTrajectoryExtend_eq hT U zs.2]
      _ ≤ dist (U zt) (wholeLineCauchyHeatBUCTotal h (U zs)) +
          dist (wholeLineCauchyHeatBUCTotal h (U zs)) (U zs) :=
            dist_triangle _ _ _
      _ ≤ wholeLineCauchyBUCMildDisplacement p M h +
          (M + 2 * B) * Real.sqrt h := add_le_add hhom hheat'
      _ ≤
          (2 * |p.χ| *
                ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) +
              (M + M * (1 + M ^ p.α))) * Real.sqrt h +
            (M + 2 * B) * Real.sqrt h := add_le_add hdisp le_rfl
      _ = H * Real.sqrt (t - s) := by
        dsimp [H, wholeLineCauchyBUCTimeSqrtConst, h]
        ring
  intro s hs t ht hdist
  by_cases hst : s ≤ t
  · have hdt : t - s ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hst)] at hdist
      exact hdist
    have hbound := hforward hs ht hst hdt
    simpa [abs_of_nonneg (sub_nonneg.mpr hst), Real.sqrt_eq_rpow, U] using hbound
  · have hts : t ≤ s := le_of_not_ge hst
    have hdt : s - t ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hts)] at hdist
      linarith
    have hbound := hforward ht hs hts hdt
    rw [dist_comm] at hbound
    have habs : |t - s| = s - t := by
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    simpa [habs, Real.sqrt_eq_rpow, U] using hbound

/-- Pointwise form of the positive-window `1/2`-Holder estimate. -/
theorem exists_wholeLineCauchyBUCMildFixedPoint_time_pointwise_sqrt_holder_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        |t - s| ≤ 1 →
        |(wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1 x -
            (wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| ≤
          H * |t - s| ^ (1 / 2 : ℝ) := by
  rcases
      exists_wholeLineCauchyBUCMildFixedPoint_time_sqrt_holder_positive_window
        p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
          heta0 heta1 hrel hstrip with
    ⟨H, hH, htime⟩
  refine ⟨H, hH, ?_⟩
  intro s hs t ht x hst
  exact
    (WholeLineBUC.pointwise_abs_sub_le_dist
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t)
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s) x).trans
      (htime s hs t ht hst)

/-- Quantitative time modulus for the spatial derivative on a compact
positive-time window.  The fourth-root loss comes from the elementary
one-dimensional interpolation between the BUC time modulus and the common
spatial `C^eta` modulus of the derivatives. -/
theorem exists_wholeLineCauchyBUCMildFixedPoint_spatial_deriv_time_modulus_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        |t - s| ≤ 1 →
        |deriv (fun w : ℝ =>
              (wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1 w) x -
            deriv (fun w : ℝ =>
              (wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 w) x| ≤
          C * (Real.sqrt (Real.sqrt |t - s|)) ^ eta := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  rcases
      exists_wholeLineCauchyBUCMildFixedPoint_time_sqrt_holder_positive_window
        p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
          heta0 heta1 hrel hstrip with
    ⟨H, hH, htime⟩
  rcases
      wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta_window
        p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
          heta0 heta1 hrel with
    ⟨K, hK, hholder⟩
  let C : ℝ := 2 * K + 2 * H
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro s hs t ht x hdist
  by_cases hts : t = s
  · subst t
    simp [Real.zero_rpow heta0.ne']
  let d : ℝ := |t - s|
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdpos : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hts)
  have hd1 : d ≤ 1 := by simpa [d] using hdist
  let r : ℝ := Real.sqrt (Real.sqrt d)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hsqrt1 : Real.sqrt d ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hd1
  have hr1 : r ≤ 1 := by
    dsimp [r]
    simpa using Real.sqrt_le_sqrt hsqrt1
  have hrr : r * r = Real.sqrt d := by
    dsimp [r]
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg d)]
  have hrpow : r ≤ r ^ eta := by
    have hp := Real.rpow_le_rpow_of_exponent_ge'
      hr0 hr1 heta0.le heta1.le
    simpa using hp
  let ft : ℝ → ℝ := fun w =>
    (wholeLineBUCTrajectoryExtend hT U t).1 w
  let fs : ℝ → ℝ := fun w =>
    (wholeLineBUCTrajectoryExtend hT U s).1 w
  have htpos : 0 < t := ha.trans_le ht.1
  have hspos : 0 < s := ha.trans_le hs.1
  let zt : Set.Icc (0 : ℝ) T :=
    ⟨t, htpos.le, ht.2.trans hbT⟩
  let zs : Set.Icc (0 : ℝ) T :=
    ⟨s, hspos.le, hs.2.trans hbT⟩
  have hft : ∀ y, HasDerivAt ft (deriv ft y) y := by
    intro y
    have hext : wholeLineBUCTrajectoryExtend hT U t = U zt :=
      wholeLineBUCTrajectoryExtend_eq hT U zt.2
    have hsp :=
      (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
        p hM hT u₀ hsmall zt htpos y).differentiableAt.hasDerivAt
    simpa [ft, U, hext] using hsp
  have hfs : ∀ y, HasDerivAt fs (deriv fs y) y := by
    intro y
    have hext : wholeLineBUCTrajectoryExtend hT U s = U zs :=
      wholeLineBUCTrajectoryExtend_eq hT U zs.2
    have hsp :=
      (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
        p hM hT u₀ hsmall zs hspos y).differentiableAt.hasDerivAt
    simpa [fs, U, hext] using hsp
  have hval : ∀ y, |ft y - fs y| ≤ H * Real.sqrt d := by
    intro y
    have hp := WholeLineBUC.pointwise_abs_sub_le_dist
      (wholeLineBUCTrajectoryExtend hT U t)
      (wholeLineBUCTrajectoryExtend hT U s) y
    calc
      |ft y - fs y| ≤
          dist (wholeLineBUCTrajectoryExtend hT U t)
            (wholeLineBUCTrajectoryExtend hT U s) := by
              simpa [ft, fs] using hp
      _ ≤ H * |t - s| ^ (1 / 2 : ℝ) := htime s hs t ht hdist
      _ = H * Real.sqrt d := by
        simp only [d, Real.sqrt_eq_rpow]
  have hinterp := deriv_sub_abs_le_of_common_holder
    hK heta0 hrpos hft hfs (hholder t ht) (hholder s hs) hval x
  have hdiv : (H * Real.sqrt d) / r = H * r := by
    rw [← hrr]
    field_simp
  calc
    |deriv (fun w : ℝ =>
          (wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1 w) x -
        deriv (fun w : ℝ =>
          (wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 w) x| =
        |deriv ft x - deriv fs x| := by rfl
    _ ≤ 2 * K * r ^ eta + 2 * (H * Real.sqrt d) / r := hinterp
    _ = 2 * K * r ^ eta + 2 * ((H * Real.sqrt d) / r) := by ring
    _ = 2 * K * r ^ eta + 2 * H * r := by rw [hdiv]; ring
    _ ≤ 2 * K * r ^ eta + 2 * H * r ^ eta := by gcongr
    _ = C * (Real.sqrt (Real.sqrt |t - s|)) ^ eta := by
      dsimp [C, r, d]
      ring

/-- The differentiated physical chemotaxis flux has a genuine power time
modulus on every compact positive-time window.  This is the quantitative
upgrade of the earlier epsilon-delta continuity theorem needed by the
weight-gap interpolation argument. -/
theorem wholeLineCauchyFluxSourceTrajectory_deriv_time_holder_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        |t - s| ≤ 1 →
        |deriv
              (wholeLineCauchyFluxSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1 x -
            deriv
              (wholeLineCauchyFluxSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| ≤
          C * |t - s| ^ alpha := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  have hstripWindow : ∀ q ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U q).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro q hq x
    have hq0 : 0 ≤ q := ha.le.trans hq.1
    have hqT : q ≤ T := hq.2.trans hbT
    let zq : Set.Icc (0 : ℝ) T := ⟨q, hq0, hqT⟩
    have hext : wholeLineBUCTrajectoryExtend hT U q = U zq :=
      wholeLineBUCTrajectoryExtend_eq hT U zq.2
    rw [hext]
    exact hstrip zq x
  rcases
      exists_wholeLineCauchyBUCMildFixedPoint_time_sqrt_holder_positive_window
        p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
          heta0 heta1 hrel hstrip with
    ⟨Hu, hHu, hutime⟩
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstripWindow with
    ⟨rho, K, hrho0, hrho1, hK, hFholder⟩
  let L : ℝ := wholeLineCauchyFluxLip p M
  have hL : 0 ≤ L := wholeLineCauchyFluxLip_nonneg p hM
  let alpha : ℝ := rho / 4
  have halpha0 : 0 < alpha := by dsimp [alpha]; positivity
  have halpha1 : alpha ≤ 1 := by dsimp [alpha]; linarith
  let C : ℝ := 2 * K + 2 * (L * Hu)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨alpha, C, halpha0, halpha1, hC, ?_⟩
  intro s hs t ht x hdist
  by_cases hts : t = s
  · subst t
    simp [Real.zero_rpow halpha0.ne']
  let d : ℝ := |t - s|
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdpos : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hts)
  have hd1 : d ≤ 1 := by simpa [d] using hdist
  let r : ℝ := Real.sqrt (Real.sqrt d)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hsqrt1 : Real.sqrt d ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hd1
  have hr1 : r ≤ 1 := by
    dsimp [r]
    simpa using Real.sqrt_le_sqrt hsqrt1
  have hrr : r * r = Real.sqrt d := by
    dsimp [r]
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg d)]
  have hrpow : r ≤ r ^ rho := by
    have hp := Real.rpow_le_rpow_of_exponent_ge'
      hr0 hr1 hrho0.le hrho1.le
    simpa using hp
  have hFdist : dist (F t) (F s) ≤ L * Hu * Real.sqrt d := by
    calc
      dist (F t) (F s) ≤ L *
          dist (wholeLineBUCTrajectoryExtend hT U t)
            (wholeLineBUCTrajectoryExtend hT U s) := by
              simpa [F, L, wholeLineCauchyFluxSourceTrajectory] using
                (wholeLineCauchyTruncatedFluxBUC_dist_le p hM
                  (wholeLineBUCTrajectoryExtend hT U t)
                  (wholeLineBUCTrajectoryExtend hT U s))
      _ ≤ L * (Hu * |t - s| ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hutime s hs t ht hdist) hL
      _ = L * Hu * Real.sqrt d := by
        simp only [d, Real.sqrt_eq_rpow]
        ring
  have hval : ∀ y, |(F t).1 y - (F s).1 y| ≤
      L * Hu * Real.sqrt d := by
    intro y
    exact (WholeLineBUC.pointwise_abs_sub_le_dist (F t) (F s) y).trans hFdist
  have htpos : 0 < t := ha.trans_le ht.1
  have hspos : 0 < s := ha.trans_le hs.1
  let zt : Set.Icc (0 : ℝ) T :=
    ⟨t, htpos.le, ht.2.trans hbT⟩
  let zs : Set.Icc (0 : ℝ) T :=
    ⟨s, hspos.le, hs.2.trans hbT⟩
  have hFt : ∀ y, HasDerivAt (F t).1 (deriv (F t).1 y) y := by
    intro y
    have hsp :=
      (wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
        p hM hT u₀ hsmall zt htpos (hstrip zt) y).differentiableAt.hasDerivAt
    simpa [F, U] using hsp
  have hFs : ∀ y, HasDerivAt (F s).1 (deriv (F s).1 y) y := by
    intro y
    have hsp :=
      (wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
        p hM hT u₀ hsmall zs hspos (hstrip zs) y).differentiableAt.hasDerivAt
    simpa [F, U] using hsp
  have hinterp := deriv_sub_abs_le_of_common_holder
    hK hrho0 hrpos hFt hFs
      (by simpa [F, U] using hFholder t ht)
      (by simpa [F, U] using hFholder s hs)
      hval x
  have hdiv : (L * Hu * Real.sqrt d) / r = L * Hu * r := by
    rw [← hrr]
    field_simp
  calc
    |deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1 x -
        deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| =
        |deriv (F t).1 x - deriv (F s).1 x| := by rfl
    _ ≤ 2 * K * r ^ rho + 2 * (L * Hu * Real.sqrt d) / r := hinterp
    _ = 2 * K * r ^ rho + 2 * ((L * Hu * Real.sqrt d) / r) := by ring
    _ = 2 * K * r ^ rho + 2 * (L * Hu) * r := by rw [hdiv]; ring
    _ ≤ 2 * K * r ^ rho + 2 * (L * Hu) * r ^ rho := by gcongr
    _ = C * d ^ alpha := by
      rw [show r ^ rho = d ^ (rho / 4) from
        sqrt_sqrt_rpow_eq_quarter_rpow hd0]
      dsimp [C, alpha]
      ring
    _ = C * |t - s| ^ alpha := by rfl

/-- Co-moving evaluation preserves a positive power time modulus for the
differentiated physical flux.  The extra spatial displacement is controlled
by the common spatial Holder modulus already available on the window. -/
theorem wholeLineCauchyFluxSourceTrajectory_deriv_coMoving_time_holder_positive_window
    (p : CMParams) {M T a b theta eta : ℝ} (c : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ q C : ℝ, 0 < q ∧ q ≤ 1 ∧ 0 ≤ C ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        |t - s| ≤ 1 →
        |deriv
              (wholeLineCauchyFluxSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1
              (x + c * t) -
            deriv
              (wholeLineCauchyFluxSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1
              (x + c * s)| ≤
          C * |t - s| ^ q := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  have hstripWindow : ∀ z ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z hz x
    have hz0 : 0 ≤ z := ha.le.trans hz.1
    have hzT : z ≤ T := hz.2.trans hbT
    let zz : Set.Icc (0 : ℝ) T := ⟨z, hz0, hzT⟩
    have hext : wholeLineBUCTrajectoryExtend hT U z = U zz :=
      wholeLineBUCTrajectoryExtend_eq hT U zz.2
    rw [hext]
    exact hstrip zz x
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_time_holder_positive_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstrip with
    ⟨alpha, Ct, halpha0, halpha1, hCt, htime⟩
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstripWindow with
    ⟨rho, K, hrho0, hrho1, hK, hspace⟩
  let q : ℝ := min alpha rho
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqalpha : q ≤ alpha := min_le_left _ _
  have hqrho : q ≤ rho := min_le_right _ _
  have hq1 : q ≤ 1 := hqalpha.trans halpha1
  let C : ℝ := Ct + K * |c| ^ rho
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨q, C, hq0, hq1, hC, ?_⟩
  intro s hs t ht x hdist
  by_cases hts : t = s
  · subst t
    simp [Real.zero_rpow hq0.ne']
  let d : ℝ := |t - s|
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdpos : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hts)
  have hd1 : d ≤ 1 := by simpa [d] using hdist
  have hdalpha : d ^ alpha ≤ d ^ q :=
    Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 hq0.le hqalpha
  have hdrho : d ^ rho ≤ d ^ q :=
    Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 hq0.le hqrho
  have hshift : |(x + c * t) - (x + c * s)| = |c| * d := by
    rw [show (x + c * t) - (x + c * s) = c * (t - s) by ring,
      abs_mul]
  have hspatial :
      |deriv (F s).1 (x + c * t) - deriv (F s).1 (x + c * s)| ≤
        K * |c| ^ rho * d ^ q := by
    calc
      |deriv (F s).1 (x + c * t) - deriv (F s).1 (x + c * s)| ≤
          K * |(x + c * t) - (x + c * s)| ^ rho := by
            simpa [F, U] using hspace s hs (x + c * t) (x + c * s)
      _ = K * (|c| ^ rho * d ^ rho) := by
        rw [hshift, Real.mul_rpow (abs_nonneg c) hd0]
      _ ≤ K * (|c| ^ rho * d ^ q) := by gcongr
      _ = K * |c| ^ rho * d ^ q := by ring
  have htemporal :
      |deriv (F t).1 (x + c * t) - deriv (F s).1 (x + c * t)| ≤
        Ct * d ^ q := by
    calc
      |deriv (F t).1 (x + c * t) - deriv (F s).1 (x + c * t)| ≤
          Ct * |t - s| ^ alpha := by
            simpa [F, U] using htime s hs t ht (x + c * t) hdist
      _ = Ct * d ^ alpha := by rfl
      _ ≤ Ct * d ^ q := mul_le_mul_of_nonneg_left hdalpha hCt
  calc
    |deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1
          (x + c * t) -
        deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1
          (x + c * s)| =
        |deriv (F t).1 (x + c * t) - deriv (F s).1 (x + c * s)| := by rfl
    _ ≤ |deriv (F t).1 (x + c * t) - deriv (F s).1 (x + c * t)| +
          |deriv (F s).1 (x + c * t) - deriv (F s).1 (x + c * s)| := by
            rw [show
              deriv (F t).1 (x + c * t) - deriv (F s).1 (x + c * s) =
                (deriv (F t).1 (x + c * t) - deriv (F s).1 (x + c * t)) +
                (deriv (F s).1 (x + c * t) - deriv (F s).1 (x + c * s)) by
                  ring]
            exact abs_add_le _ _
    _ ≤ Ct * d ^ q + K * |c| ^ rho * d ^ q :=
      add_le_add htemporal hspatial
    _ = C * |t - s| ^ q := by
      dsimp [C, d]
      ring

section WholeLineWeightedRegularityBUCTimeHolderAxiomAudit

#print axioms wholeLineCauchyHeatBUCTotal_dist_self_le_of_lipschitz
#print axioms wholeLineCauchyBUCMildDisplacement_le_sqrt
#print axioms
  exists_wholeLineCauchyBUCMildFixedPoint_time_sqrt_holder_positive_window
#print axioms
  exists_wholeLineCauchyBUCMildFixedPoint_time_pointwise_sqrt_holder_positive_window
#print axioms
  exists_wholeLineCauchyBUCMildFixedPoint_spatial_deriv_time_modulus_positive_window
#print axioms
  wholeLineCauchyFluxSourceTrajectory_deriv_time_holder_positive_window
#print axioms
  wholeLineCauchyFluxSourceTrajectory_deriv_coMoving_time_holder_positive_window

end WholeLineWeightedRegularityBUCTimeHolderAxiomAudit

end ShenWork.Paper1
