import ShenWork.Paper1.WholeLineCauchyStrictPositivity
import ShenWork.Paper1.WholeLineCauchyGlobalGluing
import ShenWork.Paper1.WholeLineWeightedRegularityRestart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical strict positivity from a left-hand initial floor

The already established canonical solution is nonnegative.  This file supplies
the missing strong-positivity upgrade under the paper's weaker one-sided datum
condition `StrictlyPositiveAtLeft`.  The comparison barrier is a decreasing
smooth left step evolved by the modified heat semigroup in the worst admissible
drift frame.  Its monotonicity makes the drift term exactly
`-K * |partial_x w|`; hence no uniform positive floor on the whole line is
introduced.
-/

/-- A smooth decreasing left step: it is `delta` on `(-infinity,A-1]`, zero on
`[A,infinity)`, and takes values in `[0,delta]` when `delta >= 0`. -/
def wholeLineSmoothLeftStep (δ A x : ℝ) : ℝ :=
  δ * Real.smoothTransition (A - x)

theorem wholeLineSmoothLeftStep_contDiff
    (δ A : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (wholeLineSmoothLeftStep δ A) := by
  unfold wholeLineSmoothLeftStep
  fun_prop

theorem wholeLineSmoothLeftStep_antitone
    {δ A : ℝ} (hδ : 0 ≤ δ) :
    Antitone (wholeLineSmoothLeftStep δ A) := by
  intro x y hxy
  unfold wholeLineSmoothLeftStep
  exact mul_le_mul_of_nonneg_left
    (Real.smoothTransition.monotone (by linarith)) hδ

theorem wholeLineSmoothLeftStep_nonneg
    {δ A x : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ wholeLineSmoothLeftStep δ A x := by
  exact mul_nonneg hδ (Real.smoothTransition.nonneg _)

theorem wholeLineSmoothLeftStep_le
    {δ A x : ℝ} (hδ : 0 ≤ δ) :
    wholeLineSmoothLeftStep δ A x ≤ δ := by
  simpa [wholeLineSmoothLeftStep] using
    (mul_le_mul_of_nonneg_left
      (Real.smoothTransition.le_one (A - x)) hδ)

@[simp] theorem wholeLineSmoothLeftStep_eq_zero_of_le
    {δ A x : ℝ} (hAx : A ≤ x) :
    wholeLineSmoothLeftStep δ A x = 0 := by
  unfold wholeLineSmoothLeftStep
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

@[simp] theorem wholeLineSmoothLeftStep_eq_delta_of_le
    {δ A x : ℝ} (hx : x ≤ A - 1) :
    wholeLineSmoothLeftStep δ A x = δ := by
  unfold wholeLineSmoothLeftStep
  rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem wholeLineSmoothLeftStep_hasDerivAt
    (δ A x : ℝ) :
    HasDerivAt (wholeLineSmoothLeftStep δ A)
      (deriv (wholeLineSmoothLeftStep δ A) x) x :=
  ((wholeLineSmoothLeftStep_contDiff δ A
    (n := (1 : ℕ∞))).differentiable (by norm_num) x).hasDerivAt

theorem wholeLineSmoothLeftStep_deriv_continuous
    (δ A : ℝ) :
    Continuous (deriv (wholeLineSmoothLeftStep δ A)) :=
  (wholeLineSmoothLeftStep_contDiff δ A (n := (1 : ℕ∞))).continuous_deriv
    le_rfl

theorem wholeLineSmoothLeftStep_deriv_nonpos
    {δ A x : ℝ} (hδ : 0 ≤ δ) :
    deriv (wholeLineSmoothLeftStep δ A) x ≤ 0 :=
  (wholeLineSmoothLeftStep_antitone hδ).deriv_nonpos

/-- The derivative of the smooth left step is compactly supported in its
unit transition interval. -/
theorem wholeLineSmoothLeftStep_deriv_hasCompactSupport
    (δ A : ℝ) :
    HasCompactSupport (deriv (wholeLineSmoothLeftStep δ A)) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (A - 1) A))
  intro x hx
  simp only [Set.mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · have hev : wholeLineSmoothLeftStep δ A =ᶠ[𝓝 x] fun _ : ℝ => δ := by
      filter_upwards [Iio_mem_nhds (lt_of_not_ge hx)] with y hy
      exact wholeLineSmoothLeftStep_eq_delta_of_le hy.le
    rw [hev.deriv_eq]
    simp
  · have hev : wholeLineSmoothLeftStep δ A =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge hx)] with y hy
      exact wholeLineSmoothLeftStep_eq_zero_of_le hy.le
    rw [hev.deriv_eq]
    simp

theorem exists_wholeLineSmoothLeftStep_deriv_bound
    (δ A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ x, |deriv (wholeLineSmoothLeftStep δ A) x| ≤ D := by
  obtain ⟨D, hD⟩ :=
    (wholeLineSmoothLeftStep_deriv_hasCompactSupport δ A).exists_bound_of_continuous
      (wholeLineSmoothLeftStep_deriv_continuous δ A)
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro x
  rw [← Real.norm_eq_abs]
  exact (hD x).trans (le_max_left _ _)

theorem wholeLineSmoothLeftStep_uniformContinuous
    (δ A : ℝ) :
    UniformContinuous (wholeLineSmoothLeftStep δ A) := by
  obtain ⟨D, hD0, hD⟩ := exists_wholeLineSmoothLeftStep_deriv_bound δ A
  let C : ℝ≥0 := ⟨D, hD0⟩
  have hlip : LipschitzWith C (wholeLineSmoothLeftStep δ A) := by
    apply lipschitzWith_of_nnnorm_deriv_le
    · exact (wholeLineSmoothLeftStep_contDiff δ A
        (n := (1 : ℕ∞))).differentiable (by norm_num)
    · intro x
      change ‖deriv (wholeLineSmoothLeftStep δ A) x‖ ≤ D
      simpa [Real.norm_eq_abs] using hD x
  exact hlip.uniformContinuous

/-- The smooth left step as an element of the canonical BUC phase space. -/
def wholeLineSmoothLeftStepBUC (δ A : ℝ) : WholeLineBUC :=
  wholeLineBUCOfUniformBound (wholeLineSmoothLeftStep δ A)
    (wholeLineSmoothLeftStep_uniformContinuous δ A) |δ|
    (fun x => by
      rw [wholeLineSmoothLeftStep, abs_mul]
      have hs0 := Real.smoothTransition.nonneg (A - x)
      have hs1 := Real.smoothTransition.le_one (A - x)
      rw [abs_of_nonneg hs0]
      nlinarith [abs_nonneg δ])

@[simp] theorem wholeLineSmoothLeftStepBUC_apply
    (δ A x : ℝ) :
    (wholeLineSmoothLeftStepBUC δ A).1 x =
      wholeLineSmoothLeftStep δ A x := rfl

/-- Comparison for two bounded drift sub/supersolutions with the same
zeroth-order loss.  The absolute drift is stable under subtraction because
`|u_x|-|w_x| <= |u_x-w_x|`. -/
theorem wholeLine_ge_of_drift_abs_subsuper
    {T Kzero Kdrift B : ℝ} {u w : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hKzero : 0 ≤ Kzero) (hKdrift : 0 ≤ Kdrift)
    (hB : 0 ≤ B)
    (hcontu : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hcontw : Continuous (fun q : ℝ × ℝ => w q.1 q.2))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ u t x)
    (hwupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ B)
    (hinit : ∀ x, w 0 x ≤ u 0 x)
    (htimeu : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1u : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2u : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (htimew : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => w s x) t) t)
    (hspace1w : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => w t y)
        (deriv (fun y : ℝ => w t y) x) x)
    (hspace2w : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => w t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x) x)
    (hpdeu : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => u s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x -
          Kzero * u t x - Kdrift * |deriv (fun y : ℝ => u t y) x|)
    (hpdew : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => w s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x -
          Kzero * w t x - Kdrift * |deriv (fun y : ℝ => w t y) x|) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ u t x := by
  let q : ℝ → ℝ → ℝ := fun t x =>
    Real.exp (Kzero * t) * (w t x - u t x)
  have hcontq : Continuous (fun r : ℝ × ℝ => q r.1 r.2) := by
    dsimp [q]
    fun_prop
  let Aq : ℝ := Real.exp (Kzero * T) * B
  have hupperq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, q t x ≤ Aq := by
    intro t ht x
    have hexp_le : Real.exp (Kzero * t) ≤ Real.exp (Kzero * T) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKzero)
    have hdiff : w t x - u t x ≤ B := by
      linarith [hwupper t ht x, hnonneg t ht x]
    have hexp0 : 0 ≤ Real.exp (Kzero * t) := (Real.exp_pos _).le
    have hBexp : Real.exp (Kzero * t) * B ≤
        Real.exp (Kzero * T) * B :=
      mul_le_mul_of_nonneg_right hexp_le hB
    dsimp [q, Aq]
    exact (mul_le_mul_of_nonneg_left hdiff hexp0).trans hBexp
  have hinitq : ∀ x, q 0 x ≤ 0 := by
    intro x
    simpa [q] using sub_nonpos.mpr (hinit x)
  have htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t := by
    intro t x ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (Kzero * s))
        (Kzero * Real.exp (Kzero * t)) t := by
      convert (Real.hasDerivAt_exp (Kzero * t)).comp t
        ((hasDerivAt_id t).const_mul Kzero) using 1
      all_goals ring
    have hraw := hexp.mul
      ((htimew (t := t) (x := x) ht).sub
        (htimeu (t := t) (x := x) ht))
    simpa [q] using hraw.differentiableAt.hasDerivAt
  have hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x := by
    intro t x ht
    have hraw :=
      ((hspace1w (t := t) (x := x) ht).sub
        (hspace1u (t := t) (x := x) ht)).const_mul
          (Real.exp (Kzero * t))
    simpa [q] using hraw.differentiableAt.hasDerivAt
  have hderivq : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → ∀ y,
      deriv (fun z : ℝ => q t z) y =
        Real.exp (Kzero * t) *
          (deriv (fun z : ℝ => w t z) y -
            deriv (fun z : ℝ => u t z) y) := by
    intro t ht y
    have hraw := ((hspace1w (t := t) (x := y) ht).sub
      (hspace1u (t := t) (x := y) ht)).const_mul
        (Real.exp (Kzero * t))
    simpa [q] using hraw.deriv
  have hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x := by
    intro t x ht
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => q t z) y) =
        fun y : ℝ => Real.exp (Kzero * t) *
          (deriv (fun z : ℝ => w t z) y -
            deriv (fun z : ℝ => u t z) y) := by
      funext y
      exact hderivq ht y
    have hraw :=
      ((hspace2w (t := t) (x := x) ht).sub
        (hspace2u (t := t) (x := x) ht)).const_mul
          (Real.exp (Kzero * t))
    rw [hfun]
    exact hraw.differentiableAt.hasDerivAt
  have hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => q s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          Kdrift * |deriv (fun y : ℝ => q t y) x| := by
    intro t x ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (Kzero * s))
        (Kzero * Real.exp (Kzero * t)) t := by
      convert (Real.hasDerivAt_exp (Kzero * t)).comp t
        ((hasDerivAt_id t).const_mul Kzero) using 1
      all_goals ring
    have hqt : deriv (fun s : ℝ => q s x) t =
        Kzero * Real.exp (Kzero * t) * (w t x - u t x) +
          Real.exp (Kzero * t) *
            (deriv (fun s : ℝ => w s x) t -
              deriv (fun s : ℝ => u s x) t) := by
      have hraw := hexp.mul
        ((htimew (t := t) (x := x) ht).sub
          (htimeu (t := t) (x := x) ht))
      simpa [q] using hraw.deriv
    have hqx : deriv (fun y : ℝ => q t y) x =
        Real.exp (Kzero * t) *
          (deriv (fun y : ℝ => w t y) x -
            deriv (fun y : ℝ => u t y) x) := hderivq ht x
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => q t z) y) =
        fun y : ℝ => Real.exp (Kzero * t) *
          (deriv (fun z : ℝ => w t z) y -
            deriv (fun z : ℝ => u t z) y) := by
      funext y
      exact hderivq ht y
    have hqxx : deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x =
        Real.exp (Kzero * t) *
          (deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x -
            deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) := by
      rw [hfun]
      exact (((hspace2w (t := t) (x := x) ht).sub
        (hspace2u (t := t) (x := x) ht)).const_mul
        (Real.exp (Kzero * t))).deriv
    have hqabs : |deriv (fun y : ℝ => q t y) x| =
        Real.exp (Kzero * t) *
          |deriv (fun y : ℝ => w t y) x -
            deriv (fun y : ℝ => u t y) x| := by
      rw [hqx, abs_mul, abs_of_pos (Real.exp_pos _)]
    have habs :
        |deriv (fun y : ℝ => u t y) x| -
            |deriv (fun y : ℝ => w t y) x| ≤
          |deriv (fun y : ℝ => w t y) x -
            deriv (fun y : ℝ => u t y) x| := by
      have := abs_sub_abs_le_abs_sub
        (deriv (fun y : ℝ => u t y) x)
        (deriv (fun y : ℝ => w t y) x)
      simpa [abs_sub_comm] using this
    have hbase :
        Kzero * (w t x - u t x) +
            (deriv (fun s : ℝ => w s x) t -
              deriv (fun s : ℝ => u s x) t) ≤
          (deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x -
            deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) +
            Kdrift *
              |deriv (fun y : ℝ => w t y) x -
                deriv (fun y : ℝ => u t y) x| := by
      have hw := hpdew (t := t) (x := x) ht
      have hu := hpdeu (t := t) (x := x) ht
      have hka := mul_le_mul_of_nonneg_left habs hKdrift
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hbase
      (Real.exp_pos (Kzero * t)).le
    rw [hqt, hqxx, hqabs]
    nlinarith
  have hq_nonpos_Ico : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, q t x ≤ 0 := by
    intro t ht x
    let S : ℝ := (t + T) / 2
    have hS0 : 0 < S := by dsimp [S]; linarith [ht.1, hT]
    have htS : t ≤ S := by dsimp [S]; linarith [ht.2]
    have hST : S < T := by dsimp [S]; linarith [ht.2]
    have hupperS : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ y, q s y ≤ Aq := by
      intro s hs y
      exact hupperq s ⟨hs.1, hs.2.trans hST.le⟩ y
    have hsup : wholeLineSlabSup S q ≤ 0 :=
      wholeLineSlabSup_le_of_drift_subsolution hS0 hKdrift hcontq
        hupperS hinitq
        (fun _ _ hs => htimeq ⟨hs.1, hs.2.trans_lt hST⟩)
        (fun _ _ hs => hspace1q ⟨hs.1, hs.2.trans_lt hST⟩)
        (fun _ _ hs => hspace2q ⟨hs.1, hs.2.trans_lt hST⟩)
        (fun _ _ hs => hpdeq ⟨hs.1, hs.2.trans_lt hST⟩)
    have hle : q t x ≤ wholeLineSlabSup S q :=
      le_wholeLineSlabSup hS0.le hupperS ⟨ht.1, htS⟩ x
    exact hle.trans hsup
  intro t ht x
  have hqle : q t x ≤ 0 := by
    by_cases hlt : t < T
    · exact hq_nonpos_Ico t ⟨ht.1, hlt⟩ x
    · have htT : t = T := le_antisymm ht.2 (le_of_not_gt hlt)
      subst t
      have htimeCont : Continuous (fun s : ℝ => q s x) :=
        hcontq.comp (continuous_id.prodMk continuous_const)
      have htend : Tendsto (fun s : ℝ => q s x) (𝓝[<] T) (𝓝 (q T x)) :=
        htimeCont.continuousAt.mono_left inf_le_left
      have hevent : ∀ᶠ s in 𝓝[<] T, q s x ≤ 0 := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_gt_nhds hT).filter_mono inf_le_left] with s hsT hs0
        exact hq_nonpos_Ico s ⟨hs0.le, hsT⟩ x
      exact le_of_tendsto htend hevent
  dsimp [q] at hqle
  apply sub_nonpos.mp
  nlinarith [Real.exp_pos (Kzero * t)]

/-- The explicit lower comparison orbit.  `wholeLineCauchyMovingHeatOp` has
generator `dxx + Kdrift * dx - 1`; the scalar prefactor changes the
zeroth-order coefficient from `-1` to `-Kzero`. -/
def wholeLineSmoothLeftHeatBarrier
    (Kzero Kdrift δ A t x : ℝ) : ℝ :=
  Real.exp ((1 - Kzero) * t) *
    wholeLineCauchyMovingHeatBUCTotalVal Kdrift t
      (wholeLineSmoothLeftStepBUC δ A) x

@[simp] theorem wholeLineSmoothLeftHeatBarrier_zero
    (Kzero Kdrift δ A x : ℝ) :
    wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A 0 x =
      wholeLineSmoothLeftStep δ A x := by
  simp [wholeLineSmoothLeftHeatBarrier]

theorem wholeLineCauchyHeatBUCTotal_continuous
    (f : WholeLineBUC) :
    Continuous (fun t : ℝ => wholeLineCauchyHeatBUCTotal t f) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hev : (fun s : ℝ => wholeLineCauchyHeatBUCTotal s f) =ᶠ[𝓝 t]
        fun _ : ℝ => f := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact wholeLineCauchyHeatBUCTotal_of_nonpos hs.le f
    exact continuousAt_const.congr_of_eventuallyEq hev
  · exact wholeLineCauchyHeatBUCTotal_continuousAt_zero f
  · exact wholeLineCauchyHeatBUCTotal_continuousAt_of_pos ht f

theorem wholeLineSmoothLeftHeatBarrier_continuous
    (Kzero Kdrift δ A : ℝ) :
    Continuous (fun q : ℝ × ℝ =>
      wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A q.1 q.2) := by
  have hpair : Continuous (fun q : ℝ × ℝ =>
      (wholeLineCauchyHeatBUCTotal q.1
          (wholeLineSmoothLeftStepBUC δ A),
        q.2 + Kdrift * q.1)) :=
    ((wholeLineCauchyHeatBUCTotal_continuous
      (wholeLineSmoothLeftStepBUC δ A)).comp continuous_fst).prodMk
        (continuous_snd.add (continuous_const.mul continuous_fst))
  have heval : Continuous (fun z : WholeLineBUC × ℝ => z.1.1 z.2) := by
    fun_prop
  unfold wholeLineSmoothLeftHeatBarrier
  exact (Real.continuous_exp.comp
      ((continuous_const.sub continuous_const).mul continuous_fst)).mul
    (heval.comp hpair)

theorem wholeLineSmoothLeftHeatBarrier_le_delta
    {Kzero Kdrift δ A T t x : ℝ}
    (hKzero : 0 ≤ Kzero) (hδ : 0 ≤ δ)
    (_hT : 0 ≤ T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t x ≤ δ := by
  by_cases ht0 : t = 0
  · subst t
    simpa using wholeLineSmoothLeftStep_le (A := A) (x := x) hδ
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hφnonneg : ∀ y, 0 ≤ wholeLineSmoothLeftStep δ A y :=
      fun y => wholeLineSmoothLeftStep_nonneg hδ
    have hφle : ∀ y, wholeLineSmoothLeftStep δ A y ≤ δ :=
      fun y => wholeLineSmoothLeftStep_le hδ
    have hφbd : ∀ y, |wholeLineSmoothLeftStep δ A y| ≤ δ := by
      intro y
      rw [abs_of_nonneg (hφnonneg y)]
      exact hφle y
    have hraw : wholeLineCauchyMovingHeatBUCTotalVal Kdrift t
        (wholeLineSmoothLeftStepBUC δ A) x ≤ Real.exp (-t) * δ := by
      rw [wholeLineCauchyMovingHeatBUCTotalVal_of_pos htpos]
      exact modifiedSemigroup_upper_bound hφle hφbd
        (wholeLineSmoothLeftStep_contDiff δ A
          (n := (0 : ℕ∞))).continuous.aestronglyMeasurable htpos _
    have hscale0 : 0 ≤ Real.exp ((1 - Kzero) * t) := (Real.exp_pos _).le
    calc
      wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t x
          ≤ Real.exp ((1 - Kzero) * t) * (Real.exp (-t) * δ) := by
            exact mul_le_mul_of_nonneg_left hraw hscale0
      _ = Real.exp (-(Kzero * t)) * δ := by
            rw [← mul_assoc, ← Real.exp_add]
            congr 1
            ring
      _ ≤ 1 * δ := by
            apply mul_le_mul_of_nonneg_right _ hδ
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
              (mul_nonneg hKzero ht.1))
      _ = δ := one_mul _

theorem wholeLineSmoothLeftHeatBarrier_pos
    {Kzero Kdrift δ A t x : ℝ}
    (hδ : 0 < δ) (ht : 0 < t) :
    0 < wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t x := by
  have hheat : 0 < wholeLineCauchyMovingHeatBUCTotalVal Kdrift t
      (wholeLineSmoothLeftStepBUC δ A) x := by
    rw [wholeLineCauchyMovingHeatBUCTotalVal_of_pos ht]
    unfold wholeLineCauchyMovingHeatOp
    apply wholeLineCauchyHeatOp_pos_of_nonneg_of_pos_atBot ht
      (M := δ) (δ := δ) (A := A - 1)
    · intro y
      change |wholeLineSmoothLeftStep δ A y| ≤ δ
      rw [abs_of_nonneg (wholeLineSmoothLeftStep_nonneg hδ.le)]
      exact wholeLineSmoothLeftStep_le hδ.le
    · exact (wholeLineSmoothLeftStep_contDiff δ A
        (n := (0 : ℕ∞))).continuous.aestronglyMeasurable
    · exact fun y => wholeLineSmoothLeftStep_nonneg hδ.le
    · exact hδ
    · intro y hy
      exact le_of_eq (wholeLineSmoothLeftStep_eq_delta_of_le
        hy).symm
  exact mul_pos (Real.exp_pos _) hheat

theorem wholeLineSmoothLeftHeatBarrier_spatial_hasDerivAt
    {Kzero Kdrift δ A t x : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) :
    HasDerivAt
      (fun y : ℝ => wholeLineSmoothLeftHeatBarrier
        Kzero Kdrift δ A t y)
      (Real.exp ((1 - Kzero) * t) *
        wholeLineCauchyHeatGradOp t (wholeLineSmoothLeftStep δ A)
          (x + Kdrift * t)) x := by
  have hφmeas : AEStronglyMeasurable (wholeLineSmoothLeftStep δ A) volume :=
    (wholeLineSmoothLeftStep_contDiff δ A
      (n := (0 : ℕ∞))).continuous.aestronglyMeasurable
  have hφbd : ∀ y, |wholeLineSmoothLeftStep δ A y| ≤ δ := by
    intro y
    rw [abs_of_nonneg (wholeLineSmoothLeftStep_nonneg hδ)]
    exact wholeLineSmoothLeftStep_le hδ
  have hbase := wholeLineCauchyHeatOp_hasDerivAt ht hφmeas hφbd
    (x := x + Kdrift * t)
  have hinner : HasDerivAt (fun y : ℝ => y + Kdrift * t) 1 x := by
    simpa using (hasDerivAt_id x).add_const (Kdrift * t)
  have hraw := (hbase.comp x hinner).const_mul
    (Real.exp ((1 - Kzero) * t))
  have hfun : (fun y : ℝ => wholeLineSmoothLeftHeatBarrier
      Kzero Kdrift δ A t y) =
      fun y : ℝ => Real.exp ((1 - Kzero) * t) *
        wholeLineCauchyHeatOp t (wholeLineSmoothLeftStep δ A)
          (y + Kdrift * t) := by
    funext y
    rw [wholeLineSmoothLeftHeatBarrier,
      wholeLineCauchyMovingHeatBUCTotalVal_of_pos ht]
    rfl
  rw [hfun]
  simpa using hraw

theorem wholeLineSmoothLeftHeatBarrier_spatial_deriv_eq
    {Kzero Kdrift δ A t x : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) :
    deriv (fun y : ℝ => wholeLineSmoothLeftHeatBarrier
      Kzero Kdrift δ A t y) x =
      Real.exp ((1 - Kzero) * t) *
        wholeLineCauchyHeatGradOp t (wholeLineSmoothLeftStep δ A)
          (x + Kdrift * t) :=
  (wholeLineSmoothLeftHeatBarrier_spatial_hasDerivAt hδ ht).deriv

theorem wholeLineSmoothLeftHeatBarrier_spatial_deriv_nonpos
    {Kzero Kdrift δ A t x : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) :
    deriv (fun y : ℝ => wholeLineSmoothLeftHeatBarrier
      Kzero Kdrift δ A t y) x ≤ 0 := by
  obtain ⟨D, _hD0, hD⟩ := exists_wholeLineSmoothLeftStep_deriv_bound δ A
  have hgrad := wholeLineCauchyHeatGradOp_eq_heatOp_deriv
    (x := x + Kdrift * t) ht
    (fun y => by
      rw [abs_of_nonneg (wholeLineSmoothLeftStep_nonneg hδ)]
      exact wholeLineSmoothLeftStep_le hδ)
    hD (wholeLineSmoothLeftStep_hasDerivAt δ A)
    (wholeLineSmoothLeftStep_deriv_continuous δ A)
  have hneg : wholeLineCauchyHeatOp t
      (deriv (wholeLineSmoothLeftStep δ A)) (x + Kdrift * t) ≤ 0 := by
    have hnn := modifiedSemigroup_nonneg
      (fun y => neg_nonneg.mpr
        (wholeLineSmoothLeftStep_deriv_nonpos (A := A) (x := y) hδ))
      ht (x + Kdrift * t)
    rw [modifiedSemigroup_neg] at hnn
    exact neg_nonneg.mp hnn
  rw [wholeLineSmoothLeftHeatBarrier_spatial_deriv_eq hδ ht, hgrad]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg

theorem wholeLineSmoothLeftHeatBarrier_spatial_second_hasDerivAt
    {Kzero Kdrift δ A t x : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) :
    HasDerivAt
      (fun y : ℝ => deriv (fun z : ℝ =>
        wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t z) y)
      (Real.exp ((1 - Kzero) * t) *
        wholeLineCauchyHeatHessOp t (wholeLineSmoothLeftStep δ A)
          (x + Kdrift * t)) x := by
  have hφmeas : AEStronglyMeasurable (wholeLineSmoothLeftStep δ A) volume :=
    (wholeLineSmoothLeftStep_contDiff δ A
      (n := (0 : ℕ∞))).continuous.aestronglyMeasurable
  have hφbd : ∀ y, |wholeLineSmoothLeftStep δ A y| ≤ δ := by
    intro y
    rw [abs_of_nonneg (wholeLineSmoothLeftStep_nonneg hδ)]
    exact wholeLineSmoothLeftStep_le hδ
  have hbase := wholeLineCauchyHeatGradOp_hasDerivAt ht hφmeas hφbd
    (x := x + Kdrift * t)
  have hinner : HasDerivAt (fun y : ℝ => y + Kdrift * t) 1 x := by
    simpa using (hasDerivAt_id x).add_const (Kdrift * t)
  have hraw := (hbase.comp x hinner).const_mul
    (Real.exp ((1 - Kzero) * t))
  have hevent :
      (fun y : ℝ => deriv (fun z : ℝ =>
        wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t z) y) =ᶠ[𝓝 x]
      fun y : ℝ => Real.exp ((1 - Kzero) * t) *
        wholeLineCauchyHeatGradOp t (wholeLineSmoothLeftStep δ A)
          (y + Kdrift * t) :=
    Filter.Eventually.of_forall fun y =>
      wholeLineSmoothLeftHeatBarrier_spatial_deriv_eq hδ ht
  simpa using hraw.congr_of_eventuallyEq hevent

theorem wholeLineSmoothLeftHeatBarrier_time_hasDerivAt
    {Kzero Kdrift δ A t x : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ => wholeLineSmoothLeftHeatBarrier
        Kzero Kdrift δ A s x)
      (Real.exp ((1 - Kzero) * t) *
        (wholeLineCauchyHeatHessOp t (wholeLineSmoothLeftStep δ A)
            (x + Kdrift * t) +
          Kdrift * wholeLineCauchyHeatOp t
            (deriv (wholeLineSmoothLeftStep δ A)) (x + Kdrift * t) -
          Kzero * wholeLineCauchyHeatOp t
            (wholeLineSmoothLeftStep δ A) (x + Kdrift * t))) t := by
  obtain ⟨D, hD0, hD⟩ := exists_wholeLineSmoothLeftStep_deriv_bound δ A
  have hmove := wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C1
    (c := Kdrift) (f := wholeLineSmoothLeftStep δ A) (x := x)
    ht hδ hD0
    (fun y => by
      rw [abs_of_nonneg (wholeLineSmoothLeftStep_nonneg hδ)]
      exact wholeLineSmoothLeftStep_le hδ)
    hD (wholeLineSmoothLeftStep_hasDerivAt δ A)
    (wholeLineSmoothLeftStep_deriv_continuous δ A)
  have hscale : HasDerivAt
      (fun s : ℝ => Real.exp ((1 - Kzero) * s))
      ((1 - Kzero) * Real.exp ((1 - Kzero) * t)) t := by
    convert (Real.hasDerivAt_exp ((1 - Kzero) * t)).comp t
      ((hasDerivAt_id t).const_mul (1 - Kzero)) using 1
    all_goals ring
  have hraw := hscale.mul hmove
  have hev :
      (fun s : ℝ => wholeLineSmoothLeftHeatBarrier
        Kzero Kdrift δ A s x) =ᶠ[𝓝 t]
      fun s : ℝ => Real.exp ((1 - Kzero) * s) *
        wholeLineCauchyMovingHeatOp Kdrift s
          (wholeLineSmoothLeftStep δ A) x := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [wholeLineSmoothLeftHeatBarrier,
      wholeLineCauchyMovingHeatBUCTotalVal_of_pos hs]
    change Real.exp ((1 - Kzero) * s) *
        wholeLineCauchyMovingHeatOp Kdrift s
          (wholeLineSmoothLeftStep δ A) x = _
    rfl
  have htransport := hraw.congr_of_eventuallyEq hev
  apply htransport.congr_deriv
  unfold wholeLineCauchyMovingHeatOp
  ring

theorem wholeLineSmoothLeftHeatBarrier_pde
    {Kzero Kdrift δ A t x : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) :
    deriv (fun s : ℝ => wholeLineSmoothLeftHeatBarrier
      Kzero Kdrift δ A s x) t =
      deriv (fun y : ℝ => deriv (fun z : ℝ =>
        wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t z) y) x -
        Kzero * wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t x -
        Kdrift * |deriv (fun y : ℝ =>
          wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t y) x| := by
  have htderiv := (wholeLineSmoothLeftHeatBarrier_time_hasDerivAt
    (Kzero := Kzero) (Kdrift := Kdrift) (A := A) (x := x) hδ ht).deriv
  have hxderiv := wholeLineSmoothLeftHeatBarrier_spatial_deriv_eq
    (Kzero := Kzero) (Kdrift := Kdrift) (A := A) (x := x) hδ ht
  have hxxderiv := (wholeLineSmoothLeftHeatBarrier_spatial_second_hasDerivAt
    (Kzero := Kzero) (Kdrift := Kdrift) (A := A) (x := x) hδ ht).deriv
  have hxnonpos := wholeLineSmoothLeftHeatBarrier_spatial_deriv_nonpos
    (Kzero := Kzero) (Kdrift := Kdrift) (A := A) (x := x) hδ ht
  have hgrad := wholeLineCauchyHeatGradOp_eq_heatOp_deriv
    (x := x + Kdrift * t) ht
    (fun y => by
      rw [abs_of_nonneg (wholeLineSmoothLeftStep_nonneg hδ)]
      exact wholeLineSmoothLeftStep_le hδ)
    (Classical.choose_spec
      (exists_wholeLineSmoothLeftStep_deriv_bound δ A)).2
    (wholeLineSmoothLeftStep_hasDerivAt δ A)
    (wholeLineSmoothLeftStep_deriv_continuous δ A)
  rw [htderiv, hxxderiv]
  rw [abs_of_nonpos hxnonpos, hxderiv]
  rw [wholeLineSmoothLeftHeatBarrier,
    wholeLineCauchyMovingHeatBUCTotalVal_of_pos ht]
  unfold wholeLineCauchyMovingHeatOp
  rw [show ((wholeLineSmoothLeftStepBUC δ A).1 : ℝ → ℝ) =
      wholeLineSmoothLeftStep δ A by rfl]
  rw [hgrad]
  ring

/-- A nonnegative bounded classical drift supersolution whose initial slice
has a positive left-hand floor is instantly positive everywhere.  Moreover,
every slice on the closed finite horizon retains a (time-dependent) positive
left-hand floor; this second conclusion is what makes canonical restart
induction possible. -/
theorem wholeLine_pos_and_left_of_initial_posAtBot_of_drift_supersolution
    {T Kzero Kdrift : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hKzero : 0 ≤ Kzero) (hKdrift : 0 ≤ Kdrift)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ u t x)
    (hleft : StrictlyPositiveAtLeft (u 0))
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => u s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x -
          Kzero * u t x - Kdrift * |deriv (fun y : ℝ => u t y) x|) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, 0 < t → ∀ x, 0 < u t x) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, StrictlyPositiveAtLeft (u t)) := by
  rcases hleft with ⟨δ, hδ, hδev⟩
  rcases eventually_atBot.1 hδev with ⟨A, hA⟩
  let w : ℝ → ℝ → ℝ := fun t x =>
    wholeLineSmoothLeftHeatBarrier Kzero Kdrift δ A t x
  have hwcont : Continuous (fun q : ℝ × ℝ => w q.1 q.2) := by
    simpa [w] using wholeLineSmoothLeftHeatBarrier_continuous
      Kzero Kdrift δ A
  have hwupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ δ := by
    intro t ht x
    simpa [w] using wholeLineSmoothLeftHeatBarrier_le_delta
      hKzero hδ.le hT.le ht
  have hwinit : ∀ x, w 0 x ≤ u 0 x := by
    intro x
    rcases le_total x A with hx | hx
    · calc
        w 0 x = wholeLineSmoothLeftStep δ A x := by simp [w]
        _ ≤ δ := wholeLineSmoothLeftStep_le hδ.le
        _ ≤ u 0 x := hA x hx
    · calc
        w 0 x = wholeLineSmoothLeftStep δ A x := by simp [w]
        _ = 0 := wholeLineSmoothLeftStep_eq_zero_of_le hx
        _ ≤ u 0 x := hnonneg 0 ⟨le_rfl, hT.le⟩ x
  have hwtime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => w s x) t) t := by
    intro t x ht
    exact (wholeLineSmoothLeftHeatBarrier_time_hasDerivAt
      (Kzero := Kzero) (Kdrift := Kdrift) (δ := δ) (A := A) (x := x)
      hδ.le ht.1).differentiableAt.hasDerivAt
  have hwspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => w t y)
        (deriv (fun y : ℝ => w t y) x) x := by
    intro t x ht
    exact (wholeLineSmoothLeftHeatBarrier_spatial_hasDerivAt
      (Kzero := Kzero) (Kdrift := Kdrift) (δ := δ) (A := A) (x := x)
      hδ.le ht.1).differentiableAt.hasDerivAt
  have hwspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => w t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x) x := by
    intro t x ht
    exact (wholeLineSmoothLeftHeatBarrier_spatial_second_hasDerivAt
      (Kzero := Kzero) (Kdrift := Kdrift) (δ := δ) (A := A) (x := x)
      hδ.le ht.1).differentiableAt.hasDerivAt
  have hwpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => w s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => w t z) y) x -
          Kzero * w t x - Kdrift * |deriv (fun y : ℝ => w t y) x| := by
    intro t x ht
    exact le_of_eq (wholeLineSmoothLeftHeatBarrier_pde
      (Kzero := Kzero) (Kdrift := Kdrift) (δ := δ) (A := A) (x := x)
      hδ.le ht.1)
  have hge : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ u t x :=
    wholeLine_ge_of_drift_abs_subsuper hT hKzero hKdrift hδ.le
      hcont hwcont hnonneg hwupper hwinit htime hspace1 hspace2
      hwtime hwspace1 hwspace2 hpde hwpde
  constructor
  · intro t ht htpos x
    exact (wholeLineSmoothLeftHeatBarrier_pos
      (Kzero := Kzero) (Kdrift := Kdrift) (A := A) (x := x) hδ htpos).trans_le
        (hge t ht x)
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact ⟨δ, hδ, eventually_atBot.2 ⟨A, hA⟩⟩
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hwanti : Antitone (w t) := by
        apply antitone_of_deriv_nonpos
        · intro x
          exact (wholeLineSmoothLeftHeatBarrier_spatial_hasDerivAt
            (Kzero := Kzero) (Kdrift := Kdrift) (δ := δ) (A := A)
            (t := t) (x := x) hδ.le htpos).differentiableAt
        · intro x
          exact wholeLineSmoothLeftHeatBarrier_spatial_deriv_nonpos
            (Kzero := Kzero) (Kdrift := Kdrift) (δ := δ) (A := A)
            (t := t) (x := x) hδ.le htpos
      let d : ℝ := w t 0
      have hd : 0 < d := by
        dsimp [d, w]
        exact wholeLineSmoothLeftHeatBarrier_pos hδ htpos
      refine ⟨d, hd, eventually_atBot.2 ⟨0, ?_⟩⟩
      intro x hx
      exact (hwanti hx).trans (hge t ht x)

/-- A canonical local BUC segment generated from a nonnegative datum with a
positive left-hand floor is positive at every positive time and preserves the
left-hand floor on every closed-time slice. -/
theorem wholeLineCauchyBUCMildFixedPoint_pos_and_left_of_posAtBot
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T), ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    (∀ (z : Set.Icc (0 : ℝ) T), 0 < z.1 → ∀ x,
      0 < (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x) ∧
    (∀ (z : Set.Icc (0 : ℝ) T),
      StrictlyPositiveAtLeft
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1) := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let ue : ℝ → ℝ → ℝ :=
    fun t x => (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  let Kzero : ℝ := wholeLineCauchyStrictPositivityZeroRate p M
  let Kdrift : ℝ := wholeLineCauchyStrictPositivityDriftRate p M
  have hUnonneg : ∀ z : Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ (U z).1 x := by
    simpa [U] using wholeLineCauchyBUCMildFixedPoint_nonnegative
      p hM hT u₀ hu₀ hsmall
  have hcont : Continuous (fun q : ℝ × ℝ => ue q.1 q.2) := by
    have hmap : Continuous
        (fun q : ℝ × ℝ => (Set.projIcc 0 T hT.le q.1, q.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [ue, wholeLineBUCTrajectoryExtend] using
      (wholeLineBUCTrajectory_jointContinuous U).comp hmap
  have hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ ue t x := by
    intro t ht x
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U ht
    simpa [ue, hext] using hUnonneg z x
  have hleftue : StrictlyPositiveAtLeft (ue 0) := by
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzero⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hzero
    have hUzero : U ⟨0, hzero⟩ = u₀ := by
      simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
        p hM hT.le u₀ hsmall hzero
    simpa [ue, hext, hUzero] using hleft
  have htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => ue s x)
        (deriv (fun s : ℝ => ue s x) t) t := by
    intro t x ht
    have hphysical := wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
      p hM hT.le u₀ hsmall ht.1 ht.2
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hstrip x
    simpa [ue, U] using hphysical.differentiableAt.hasDerivAt
  have hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => ue t y)
        (deriv (fun y : ℝ => ue t y) x) x := by
    intro t x ht
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hspatial := wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT.le u₀ hsmall z ht.1 x
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => ue t y) x := by
      simpa [ue, U, hext] using hspatial.differentiableAt
    exact hdiff.hasDerivAt
  have hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => ue t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => ue t z) y) x) x := by
    intro t x ht
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hwindow : ∀ s ∈ Set.Icc (t / 2) t, ∀ y,
        (wholeLineBUCTrajectoryExtend hT.le U s).1 y ∈ Set.Icc (0 : ℝ) M := by
      intro s hs y
      have hs0 : 0 ≤ s := le_trans (by linarith [ht.1] : 0 ≤ t / 2) hs.1
      have hsT : s ≤ T := hs.2.trans ht.2.le
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
      have hsext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT.le U zs.2
      simpa [hsext, U] using hstrip zs y
    have hsecond :=
      wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
        p hM hT.le u₀ hsmall z ht.1
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by simpa [U] using hwindow) x
    have hslice : (fun y : ℝ => ue t y) = fun y : ℝ => (U z).1 y := by
      funext y
      simp [ue, hext]
    rw [hslice]
    exact hsecond.differentiableAt.hasDerivAt
  have hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => ue s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => ue t z) y) x -
          Kzero * ue t x - Kdrift * |deriv (fun y : ℝ => ue t y) x| := by
    intro t x ht
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hslice : (fun y : ℝ => ue t y) = fun y : ℝ => (U z).1 y := by
      funext y
      simp [ue, hext]
    have hux : HasDerivAt (U z).1 (deriv (U z).1 x) x :=
      (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
        p hM hT.le u₀ hsmall z ht.1 x).differentiableAt.hasDerivAt
    have hflux : deriv (wholeLineChemotaxisFlux p (U z).1) x =
        p.m * ((U z).1 x) ^ (p.m - 1) * deriv (U z).1 x *
            deriv (frozenElliptic p (U z).1) x +
          ((U z).1 x) ^ p.m *
            (frozenElliptic p (U z).1 x - ((U z).1 x) ^ p.γ) :=
      wholeLineChemotaxisFlux_deriv_eq_of_nonneg p
        (WholeLineBUC.isCUnifBdd (U z)) (hUnonneg z) hux
    have hphysical := wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
      p hM hT.le u₀ hsmall ht.1 ht.2
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hstrip x
    have hpdeEq : deriv (fun s : ℝ => ue s x) t =
        deriv (fun y : ℝ => deriv (fun w : ℝ => (U z).1 w) y) x -
          p.χ * deriv (wholeLineChemotaxisFlux p (U z).1) x +
            wholeLineLogisticSource p (U z).1 x := by
      simpa [ue, U] using hphysical.deriv
    rw [hflux] at hpdeEq
    have huM := hstrip z x
    have hv0 : 0 ≤ frozenElliptic p (U z).1 x :=
      frozenElliptic_nonneg p (hUnonneg z) x
    have hvM : frozenElliptic p (U z).1 x ≤ M ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM _)
        (U z).1.continuous (hUnonneg z)
      intro y
      exact Real.rpow_le_rpow (hstrip z y).1 (hstrip z y).2
        (zero_le_one.trans p.hγ)
    have hvx : |deriv (frozenElliptic p (U z).1) x| ≤ M ^ p.γ :=
      frozenElliptic_deriv_abs_le_rpow_of_Icc p hM
        (WholeLineBUC.isCUnifBdd (U z)) (hstrip z) x
    have hlower := wholeLineCauchy_physical_pde_drift_lower_bound p hM
      huM.1 huM.2 hv0 hvM hvx
      (ut := deriv (fun s : ℝ => ue s x) t)
      (uxx := deriv (fun y : ℝ => deriv (fun w : ℝ => (U z).1 w) y) x)
      (ux := deriv (U z).1 x)
      (vx := deriv (frozenElliptic p (U z).1) x)
      (v := frozenElliptic p (U z).1 x)
      (by simpa [wholeLineLogisticSource, reactionFun] using hpdeEq)
    have hueq : ue t x = (U z).1 x := congrFun hslice x
    have huxeq : deriv (fun y : ℝ => ue t y) x = deriv (U z).1 x := by
      rw [hslice]
    have huxxeq : deriv (fun y : ℝ => deriv (fun w : ℝ => ue t w) y) x =
        deriv (fun y : ℝ => deriv (fun w : ℝ => (U z).1 w) y) x := by
      rw [hslice]
    dsimp [Kzero, Kdrift]
    rw [hueq, huxeq, huxxeq]
    exact hlower
  have hKzero : 0 ≤ Kzero := by
    dsimp [Kzero, wholeLineCauchyStrictPositivityZeroRate]
    positivity
  have hKdrift : 0 ≤ Kdrift := by
    dsimp [Kdrift, wholeLineCauchyStrictPositivityDriftRate]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
        (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hM _)
  have hcore := wholeLine_pos_and_left_of_initial_posAtBot_of_drift_supersolution
    hT hKzero hKdrift hcont hnonneg hleftue htime hspace1 hspace2 hpde
  constructor
  · intro z hz x
    have hext : wholeLineBUCTrajectoryExtend hT.le U z.1 = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    simpa [ue, U, hext] using hcore.1 z.1 z.2 hz x
  · intro z
    have hext : wholeLineBUCTrajectoryExtend hT.le U z.1 = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    simpa [ue, U, hext] using hcore.2 z.1 z.2

/-- One-sided positivity is preserved by every canonical restart datum, and
each complete canonical segment is positive at positive local time. -/
theorem wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1) :
    ∀ n,
      StrictlyPositiveAtLeft (wholeLineCauchyGlobalDatum p u₀ n).1 ∧
      (∀ z, 0 < z.1 → ∀ x,
        0 < (wholeLineCauchyGlobalSegment p u₀ n z).1 x) ∧
      (∀ z, StrictlyPositiveAtLeft
        (wholeLineCauchyGlobalSegment p u₀ n z).1) := by
  intro n
  induction n with
  | zero =>
      have hdatum : StrictlyPositiveAtLeft
          (wholeLineCauchyGlobalDatum p u₀ 0).1 := by
        simpa [wholeLineCauchyGlobalDatum] using hleft
      have hb := wholeLineCauchyGlobalDatum_segment_bounds
        p hregime u₀ hu₀ 0
      have hlocal := wholeLineCauchyBUCMildFixedPoint_pos_and_left_of_posAtBot
        p (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ 0) hb.1.1 hdatum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hb.2.1)
      refine ⟨hdatum, ?_, ?_⟩
      · simpa [wholeLineCauchyGlobalSegment] using hlocal.1
      · simpa [wholeLineCauchyGlobalSegment] using hlocal.2
  | succ n ih =>
      let d := wholeLineCauchyGlobalStep p u₀
      let zd : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
        ⟨d, (wholeLineCauchyGlobalStep_pos p u₀).le,
          by
            dsimp [d, wholeLineCauchyGlobalStep]
            linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]⟩
      have hdatum : StrictlyPositiveAtLeft
          (wholeLineCauchyGlobalDatum p u₀ (n + 1)).1 := by
        simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment,
          d, zd] using ih.2.2 zd
      have hb := wholeLineCauchyGlobalDatum_segment_bounds
        p hregime u₀ hu₀ (n + 1)
      have hlocal := wholeLineCauchyBUCMildFixedPoint_pos_and_left_of_posAtBot
        p (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ (n + 1)) hb.1.1 hdatum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hb.2.1)
      refine ⟨by simpa [Nat.succ_eq_add_one] using hdatum, ?_, ?_⟩
      · simpa [wholeLineCauchyGlobalSegment, Nat.succ_eq_add_one] using
          hlocal.1
      · simpa [wholeLineCauchyGlobalSegment, Nat.succ_eq_add_one] using
          hlocal.2

/-- The canonical glued solution is strictly positive at every positive
physical time under the paper's one-sided initial floor. -/
theorem wholeLineCauchyGlobal_pos_of_posAtBot
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < wholeLineCauchyGlobalU p u₀ t x := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, (wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht.le),
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le).le⟩
  have hqpos : 0 < q := by
    simpa [q] using wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hpos :=
    (wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
      p hregime u₀ hu₀ hleft n).2.1 z hqpos x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht.le)
  have heq' : wholeLineCauchyGlobalU p u₀ t x =
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    simpa [wholeLineCauchyGlobalU, n, q, z] using heq
  rw [heq']
  exact hpos

/-- Exact paper-facing wrapper: the canonical pair fills the strict positive
conjunct of `IsGlobalCauchySolutionFrom` from nonnegativity plus
`StrictlyPositiveAtLeft`, with no whole-line uniform floor assumption. -/
theorem wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1) :
    IsGlobalCauchySolutionFrom p u₀.1
      (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) := by
  refine ⟨wholeLineCauchyGlobal_isGlobalClassicalSolution
      p hregime u₀ hu₀,
    wholeLineCauchyGlobal_hasInitialDatum p u₀,
    wholeLineCauchyGlobal_hasUniformInitialTrace p u₀, ?_⟩
  intro t x ht
  exact wholeLineCauchyGlobal_pos_of_posAtBot
    p hregime u₀ hu₀ hleft ht x

section AxiomAudit

#print axioms wholeLineSmoothLeftStep_uniformContinuous
#print axioms wholeLineSmoothLeftStepBUC_apply
#print axioms wholeLine_ge_of_drift_abs_subsuper
#print axioms wholeLineSmoothLeftHeatBarrier_continuous
#print axioms wholeLineSmoothLeftHeatBarrier_le_delta
#print axioms wholeLineSmoothLeftHeatBarrier_pos
#print axioms wholeLineSmoothLeftHeatBarrier_spatial_deriv_nonpos
#print axioms wholeLineSmoothLeftHeatBarrier_time_hasDerivAt
#print axioms wholeLineSmoothLeftHeatBarrier_pde
#print axioms wholeLine_pos_and_left_of_initial_posAtBot_of_drift_supersolution
#print axioms wholeLineCauchyBUCMildFixedPoint_pos_and_left_of_posAtBot
#print axioms wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
#print axioms wholeLineCauchyGlobal_pos_of_posAtBot
#print axioms wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot

end AxiomAudit

end ShenWork.Paper1
