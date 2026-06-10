/-
  ShenWork/Paper2/IntervalRestartSeriesLipschitz.lean

  **Sup-norm Lipschitz-in-horizon bound for the restart cosine series.**

  This is the analytic engine behind `hinterior` (the fixed-base spectral restart
  bound, `IntervalPicardLimitSliceTimeContinuity.mildSlice_restart_bound`).

  Given a base coefficient sequence `a₀` (bounded by `B₀`) and a time source
  `a : ℝ → ℕ → ℝ` (continuous in time, with a summable per-mode envelope `env` on
  the relevant range), the restart cosine value

      U r x := ∑ₙ restartDuhamelCoeff a₀ a (r − τ) n · cosineMode n x

  is Lipschitz in `r` **uniformly in `x`**, with constant `|s − s₀| · C(τ)` where

      C(τ) = 2·B₀·(∑ₙ λₙ e^{-λₙ·m})  +  2·(∑ₙ env n),   m = the damping floor.

  The two ingredients:
  * **Homogeneous part.** `|e^{-(x)λ} − e^{-(y)λ}| ≤ λ·|x−y|·e^{-λ·min(x,y)}`
    (MVT); summed against `|a₀ n| ≤ B₀` and the heat-damped weight
    `∑ λₙ e^{-λₙ m} < ∞` (`unitIntervalCosineEigenvalue_mul_exp_summable`).
  * **Duhamel part.** `|duh(x)ₙ − duh(y)ₙ| ≤ 2·|x−y|·env n` — the λ-factor cancels
    against the integral `∫ λ e^{-λ(y−r)} dr ≤ 1`, so the bound is summable in `n`
    by the envelope alone.

  No `sorry`, no `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.Paper2.IntervalPicardLimitRestartBdd

open MeasureTheory Filter Topology Set intervalIntegral

noncomputable section

namespace ShenWork.IntervalRestartSeriesLipschitz

open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.CosineSpectrum (cosineMode)

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. Scalar exponential estimates. -/

/-- `|e^{-t} − 1| ≤ t` for `t ≥ 0`. -/
theorem abs_exp_neg_sub_one_le {t : ℝ} (ht : 0 ≤ t) : |Real.exp (-t) - 1| ≤ t := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - t ≤ Real.exp (-t) := by have := Real.add_one_le_exp (-t); linarith
  rw [abs_of_nonpos (by linarith)]; linarith

/-- **MVT exponential difference.**  For `lam ≥ 0` and any `x, y`,
`|e^{-x·lam} − e^{-y·lam}| ≤ lam·|x−y|·e^{-min(x,y)·lam}`. -/
theorem abs_exp_diff_le {lam x y : ℝ} (hlam : 0 ≤ lam) :
    |Real.exp (-(x*lam)) - Real.exp (-(y*lam))|
      ≤ lam * |x - y| * Real.exp (-(min x y * lam)) := by
  rcases le_total y x with hyx | hxy
  · have hmin : min x y = y := min_eq_right hyx
    have hfac : Real.exp (-(x*lam)) - Real.exp (-(y*lam))
        = Real.exp (-(y*lam)) * (Real.exp (-((x-y)*lam)) - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    rw [hfac, hmin, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hxy0 : 0 ≤ (x-y)*lam := mul_nonneg (by linarith) hlam
    have hb := abs_exp_neg_sub_one_le hxy0
    calc Real.exp (-(y*lam)) * |Real.exp (-((x-y)*lam)) - 1|
        ≤ Real.exp (-(y*lam)) * ((x-y)*lam) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
      _ = lam * |x-y| * Real.exp (-(y*lam)) := by
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]; ring
  · have hmin : min x y = x := min_eq_left hxy
    have hfac : Real.exp (-(x*lam)) - Real.exp (-(y*lam))
        = Real.exp (-(x*lam)) * (1 - Real.exp (-((y-x)*lam))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    rw [hfac, hmin, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hyx0 : 0 ≤ (y-x)*lam := mul_nonneg (by linarith) hlam
    have hb : |1 - Real.exp (-((y-x)*lam))| ≤ (y-x)*lam := by
      rw [abs_sub_comm]; exact abs_exp_neg_sub_one_le hyx0
    calc Real.exp (-(x*lam)) * |1 - Real.exp (-((y-x)*lam))|
        ≤ Real.exp (-(x*lam)) * ((y-x)*lam) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
      _ = lam * |x-y| * Real.exp (-(x*lam)) := by
          rw [abs_of_nonpos (by linarith : x - y ≤ 0)]; ring

/-! ## 2. The Duhamel-coefficient difference bound (λ-factor cancels). -/

/-- **Tail integral bound.**  `|∫_y^x e^{-(x−r)·lam}·a r dr| ≤ (x − y)·E` for
`y ≤ x`, `lam ≥ 0`, and `|a r| ≤ E` on `[y, x]`. -/
theorem abs_tail_integral_le {lam x y E : ℝ} {a : ℝ → ℝ}
    (hyx : y ≤ x) (hlam : 0 ≤ lam)
    (hbnd : ∀ r ∈ Set.uIcc y x, |a r| ≤ E) :
    |∫ r in y..x, Real.exp (-((x-r)*lam)) * a r| ≤ (x - y) * E := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ r in y..x, Real.exp (-((x-r)*lam)) * a r‖
      ≤ E * |x - y| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro r hr
        rw [Set.uIoc_of_le hyx] at hr
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hxr : 0 ≤ x - r := by linarith [hr.2]
        have hexp1 : Real.exp (-((x-r)*lam)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hxr hlam]
        calc Real.exp (-((x-r)*lam)) * |a r| ≤ 1 * E := by
              apply mul_le_mul hexp1
                (hbnd r (by rw [Set.uIcc_of_le hyx]; exact ⟨le_of_lt hr.1, hr.2⟩))
                (abs_nonneg _) (by norm_num)
          _ = E := one_mul _
    _ = (x - y) * E := by rw [abs_of_nonneg (by linarith)]; ring

/-- **Common-interval bound.**  `|∫_0^y (e^{-(x−r)·lam} − e^{-(y−r)·lam})·a r dr|
≤ (x − y)·E` for `0 ≤ y ≤ x`, `lam ≥ 0`, `|a r| ≤ E` on `[0, y]`.  The `lam`
factor from the MVT cancels against `∫_0^y lam·e^{-(y−r)·lam} dr ≤ 1`. -/
theorem abs_common_integral_le {lam x y E : ℝ} {a : ℝ → ℝ}
    (hyx : y ≤ x) (hy0 : 0 ≤ y) (hlam : 0 ≤ lam) (hE : 0 ≤ E)
    (hbnd : ∀ r ∈ Set.uIcc (0:ℝ) y, |a r| ≤ E) :
    |∫ r in (0:ℝ)..y, (Real.exp (-((x-r)*lam)) - Real.exp (-((y-r)*lam))) * a r|
      ≤ (x - y) * E := by
  set g : ℝ → ℝ := fun r => (x - y) * E * (lam * Real.exp (-((y-r)*lam))) with hg
  have hpt : ∀ r ∈ Set.Ioc (0:ℝ) y,
      ‖(Real.exp (-((x-r)*lam)) - Real.exp (-((y-r)*lam))) * a r‖ ≤ g r := by
    intro r hr
    rw [Real.norm_eq_abs, abs_mul]
    have hfac : Real.exp (-((x-r)*lam)) - Real.exp (-((y-r)*lam))
        = Real.exp (-((y-r)*lam)) * (Real.exp (-((x-y)*lam)) - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    have hxy0 : 0 ≤ (x-y)*lam := mul_nonneg (by linarith) hlam
    have hb := abs_exp_neg_sub_one_le hxy0
    have h1 : |Real.exp (-((x-r)*lam)) - Real.exp (-((y-r)*lam))|
        ≤ Real.exp (-((y-r)*lam)) * ((x-y)*lam) := by
      rw [hfac, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    have harbnd : |a r| ≤ E :=
      hbnd r (by rw [Set.uIcc_of_le hy0]; exact ⟨le_of_lt hr.1, hr.2⟩)
    calc |Real.exp (-((x-r)*lam)) - Real.exp (-((y-r)*lam))| * |a r|
        ≤ (Real.exp (-((y-r)*lam)) * ((x-y)*lam)) * E := by
          apply mul_le_mul h1 harbnd (abs_nonneg _)
          exact mul_nonneg (Real.exp_nonneg _) hxy0
      _ = g r := by rw [hg]; ring
  have hgint_able : IntervalIntegrable g volume 0 y := by
    apply Continuous.intervalIntegrable; rw [hg]; fun_prop
  have hint : |∫ r in (0:ℝ)..y, (Real.exp (-((x-r)*lam)) - Real.exp (-((y-r)*lam))) * a r|
      ≤ ∫ r in (0:ℝ)..y, g r := by
    rw [← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_of_norm_le hy0
      (Filter.Eventually.of_forall hpt) hgint_able
  have hgint : ∫ r in (0:ℝ)..y, g r
      = (x-y)*E * ∫ r in (0:ℝ)..y, lam * Real.exp (-((y-r)*lam)) := by
    rw [hg, intervalIntegral.integral_const_mul]
  have hexpint : ∫ r in (0:ℝ)..y, lam * Real.exp (-((y-r)*lam)) ≤ 1 := by
    have hderiv : ∀ r ∈ Set.uIcc (0:ℝ) y, HasDerivAt (fun r => Real.exp (-((y-r)*lam)))
        (lam * Real.exp (-((y-r)*lam))) r := by
      intro r _
      have hinner : HasDerivAt (fun r : ℝ => -((y-r)*lam)) lam r := by
        have h1 : HasDerivAt (fun r : ℝ => (y - r) * lam) ((-1) * lam) r :=
          (((hasDerivAt_id r).const_sub y).mul_const lam)
        simpa using h1.neg
      have := (Real.hasDerivAt_exp (-((y-r)*lam))).comp r hinner
      simpa [mul_comm] using this
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have e1 : Real.exp (-((y-y)*lam)) = 1 := by simp
    have hnn : 0 ≤ Real.exp (-((y-(0:ℝ))*lam)) := Real.exp_nonneg _
    rw [e1]; linarith
  have hxyE : 0 ≤ (x-y)*E := mul_nonneg (by linarith) hE
  calc |∫ r in (0:ℝ)..y, (Real.exp (-((x-r)*lam)) - Real.exp (-((y-r)*lam))) * a r|
      ≤ ∫ r in (0:ℝ)..y, g r := hint
    _ = (x-y)*E * ∫ r in (0:ℝ)..y, lam * Real.exp (-((y-r)*lam)) := hgint
    _ ≤ (x-y)*E * 1 := mul_le_mul_of_nonneg_left hexpint hxyE
    _ = (x-y)*E := by ring

/-- **Duhamel coefficient difference (single mode).**  For `0 ≤ y ≤ x`, a source
`a` whose mode `n` is continuous in time with `|a r n| ≤ E` on `[0, x]`,

    `|duhamelSpectralCoeff a x n − duhamelSpectralCoeff a y n| ≤ 2·(x − y)·E`. -/
theorem abs_duhamelSpectralCoeff_diff_le {a : ℝ → ℕ → ℝ} {x y E : ℝ} {n : ℕ}
    (hyx : y ≤ x) (hy0 : 0 ≤ y)
    (hacont : ContinuousOn (fun r => a r n) (Set.uIcc (0:ℝ) x))
    (hbnd : ∀ r ∈ Set.uIcc (0:ℝ) x, |a r n| ≤ E) :
    |duhamelSpectralCoeff a x n - duhamelSpectralCoeff a y n| ≤ 2 * (x - y) * E := by
  have hlam : 0 ≤ (λ_ n) := by unfold unitIntervalCosineEigenvalue; positivity
  have hE : 0 ≤ E := le_trans (abs_nonneg _) (hbnd 0 (by
    rw [Set.uIcc_of_le (le_trans hy0 hyx)]; exact ⟨le_rfl, le_trans hy0 hyx⟩))
  have h0x : (0:ℝ) ≤ x := le_trans hy0 hyx
  -- `a` is `ContinuousOn` every sub-uIcc of `[0, x]`.
  have haOn : ∀ {c d : ℝ}, Set.uIcc c d ⊆ Set.uIcc (0:ℝ) x →
      ContinuousOn (fun r => a r n) (Set.uIcc c d) := fun hsub => hacont.mono hsub
  have hsub0y : Set.uIcc (0:ℝ) y ⊆ Set.uIcc (0:ℝ) x := by
    rw [Set.uIcc_of_le hy0, Set.uIcc_of_le h0x]; exact Set.Icc_subset_Icc_right hyx
  have hsubyx : Set.uIcc y x ⊆ Set.uIcc (0:ℝ) x := by
    rw [Set.uIcc_of_le hyx, Set.uIcc_of_le h0x]; exact Set.Icc_subset_Icc_left hy0
  -- integrability witnesses
  have hint_x : IntervalIntegrable (fun r => Real.exp (-((x-r)*(λ_ n))) * a r n) volume 0 x :=
    ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop) (hacont))
  have hint_xy : IntervalIntegrable (fun r => Real.exp (-((x-r)*(λ_ n))) * a r n) volume 0 y :=
    ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop) (haOn hsub0y))
  have hint_xyx : IntervalIntegrable (fun r => Real.exp (-((x-r)*(λ_ n))) * a r n) volume y x :=
    ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop) (haOn hsubyx))
  have hint_yy : IntervalIntegrable (fun r => Real.exp (-((y-r)*(λ_ n))) * a r n) volume 0 y :=
    ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop) (haOn hsub0y))
  -- The split.
  have hsplit :
      duhamelSpectralCoeff a x n - duhamelSpectralCoeff a y n
        = (∫ r in (0:ℝ)..y,
            (Real.exp (-((x-r)*(λ_ n))) - Real.exp (-((y-r)*(λ_ n)))) * a r n)
          + (∫ r in (y:ℝ)..x, Real.exp (-((x-r)*(λ_ n))) * a r n) := by
    simp only [duhamelSpectralCoeff, neg_mul]
    have hsplit1 : (∫ r in (0:ℝ)..x, Real.exp (-((x-r)*(λ_ n))) * a r n)
        = (∫ r in (0:ℝ)..y, Real.exp (-((x-r)*(λ_ n))) * a r n)
          + (∫ r in (y:ℝ)..x, Real.exp (-((x-r)*(λ_ n))) * a r n) :=
      (intervalIntegral.integral_add_adjacent_intervals hint_xy hint_xyx).symm
    have hsub : (∫ r in (0:ℝ)..y,
          (Real.exp (-((x-r)*(λ_ n))) - Real.exp (-((y-r)*(λ_ n)))) * a r n)
        = (∫ r in (0:ℝ)..y, Real.exp (-((x-r)*(λ_ n))) * a r n)
          - (∫ r in (0:ℝ)..y, Real.exp (-((y-r)*(λ_ n))) * a r n) := by
      rw [← intervalIntegral.integral_sub hint_xy hint_yy]
      congr 1; ext r; ring
    rw [hsplit1, hsub]; ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hc : |∫ r in (0:ℝ)..y,
        (Real.exp (-((x-r)*(λ_ n))) - Real.exp (-((y-r)*(λ_ n)))) * a r n| ≤ (x - y) * E :=
    abs_common_integral_le hyx hy0 hlam hE
      (fun r hr => hbnd r (Set.uIcc_subset_uIcc_left
        (by rw [Set.uIcc_of_le (le_trans hy0 hyx)]; exact ⟨hy0, hyx⟩) hr))
  have ht : |∫ r in (y:ℝ)..x, Real.exp (-((x-r)*(λ_ n))) * a r n| ≤ (x - y) * E :=
    abs_tail_integral_le hyx hlam
      (fun r hr => hbnd r (Set.uIcc_subset_uIcc_right
        (by rw [Set.uIcc_of_le (le_trans hy0 hyx)]; exact ⟨hy0, hyx⟩) hr))
  have : (x - y) * E + (x - y) * E = 2 * (x - y) * E := by ring
  linarith

/-! ## 3. The homogeneous-coefficient difference bound (carries the λ-weight). -/

/-- **Homogeneous coefficient difference (single mode).**  For `0 ≤ m ≤ x` and
`0 ≤ m ≤ y` (so `m ≤ min x y`) and `|a₀ n| ≤ B₀`,

    `|e^{-x·λₙ}·a₀ n − e^{-y·λₙ}·a₀ n| ≤ λₙ·|x−y|·e^{-λₙ·m}·B₀`. -/
theorem abs_homog_diff_le {a₀ : ℕ → ℝ} {x y m B₀ : ℝ} {n : ℕ}
    (hmx : m ≤ x) (hmy : m ≤ y) (hB₀ : |a₀ n| ≤ B₀) :
    |Real.exp (-(x*(λ_ n))) * a₀ n - Real.exp (-(y*(λ_ n))) * a₀ n|
      ≤ (λ_ n) * |x - y| * Real.exp (-(m*(λ_ n))) * B₀ := by
  have hlam : 0 ≤ (λ_ n) := by unfold unitIntervalCosineEigenvalue; positivity
  rw [← sub_mul, abs_mul]
  have hexp := abs_exp_diff_le (lam := (λ_ n)) (x := x) (y := y) hlam
  -- e^{-min·λ} ≤ e^{-m·λ}
  have hmono : Real.exp (-(min x y * (λ_ n))) ≤ Real.exp (-(m * (λ_ n))) := by
    apply Real.exp_le_exp.mpr
    have : m ≤ min x y := le_min hmx hmy
    nlinarith [mul_le_mul_of_nonneg_right this hlam]
  have hB₀nn : 0 ≤ B₀ := le_trans (abs_nonneg _) hB₀
  calc |Real.exp (-(x*(λ_ n))) - Real.exp (-(y*(λ_ n)))| * |a₀ n|
      ≤ ((λ_ n) * |x - y| * Real.exp (-(min x y * (λ_ n)))) * B₀ := by
        apply mul_le_mul hexp hB₀ (abs_nonneg _)
        exact mul_nonneg (mul_nonneg hlam (abs_nonneg _)) (Real.exp_nonneg _)
    _ ≤ ((λ_ n) * |x - y| * Real.exp (-(m * (λ_ n)))) * B₀ := by
        apply mul_le_mul_of_nonneg_right _ hB₀nn
        apply mul_le_mul_of_nonneg_left hmono
        exact mul_nonneg hlam (abs_nonneg _)
    _ = (λ_ n) * |x - y| * Real.exp (-(m*(λ_ n))) * B₀ := by ring

/-! ## 4. Per-mode restart-coefficient difference and the summable majorant. -/

/-- **Per-mode restart coefficient difference.**  Combining the homogeneous and
Duhamel pieces: for `0 ≤ m ≤ y ≤ x` (so `m` is below `min x y`), `|a₀ n| ≤ B₀`,
the source mode `n` continuous in time with `|a r n| ≤ env n` on `[0, x]`,

    `|restartDuhamelCoeff a₀ a x n − restartDuhamelCoeff a₀ a y n|`
      `≤ |x − y| · ((λₙ · e^{-λₙ·m}) · B₀ + 2 · env n)`. -/
theorem abs_restartDuhamelCoeff_diff_le {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {x y m B₀ : ℝ} {env : ℕ → ℝ} {n : ℕ}
    (hmy : m ≤ y) (hyx : y ≤ x) (hm0 : 0 ≤ m) (hB₀ : |a₀ n| ≤ B₀)
    (hacont : ContinuousOn (fun r => a r n) (Set.uIcc (0:ℝ) x))
    (hbnd : ∀ r ∈ Set.uIcc (0:ℝ) x, |a r n| ≤ env n) :
    |restartDuhamelCoeff a₀ a x n - restartDuhamelCoeff a₀ a y n|
      ≤ |x - y| * ((λ_ n) * Real.exp (-(m*(λ_ n))) * B₀ + 2 * env n) := by
  have hmx : m ≤ x := le_trans hmy hyx
  have hy0 : 0 ≤ y := le_trans hm0 hmy
  -- split the restart coefficient into homogeneous + Duhamel
  have hexpand : restartDuhamelCoeff a₀ a x n - restartDuhamelCoeff a₀ a y n
      = (Real.exp (-(x*(λ_ n))) * a₀ n - Real.exp (-(y*(λ_ n))) * a₀ n)
        + (duhamelSpectralCoeff a x n - duhamelSpectralCoeff a y n) := by
    simp only [restartDuhamelCoeff, neg_mul]; ring
  rw [hexpand]
  refine le_trans (abs_add_le _ _) ?_
  have hhom := abs_homog_diff_le (a₀ := a₀) (x := x) (y := y) (m := m) (B₀ := B₀) (n := n)
    hmx hmy hB₀
  have hduh := abs_duhamelSpectralCoeff_diff_le (a := a) (x := x) (y := y) (E := env n) (n := n)
    hyx hy0 hacont hbnd
  -- assemble
  have hxynn : 0 ≤ |x - y| := abs_nonneg _
  have hlam : 0 ≤ (λ_ n) := by unfold unitIntervalCosineEigenvalue; positivity
  calc |Real.exp (-(x*(λ_ n))) * a₀ n - Real.exp (-(y*(λ_ n))) * a₀ n|
        + |duhamelSpectralCoeff a x n - duhamelSpectralCoeff a y n|
      ≤ (λ_ n) * |x - y| * Real.exp (-(m*(λ_ n))) * B₀ + 2 * (x - y) * env n := by
        exact add_le_add hhom hduh
    _ ≤ |x - y| * ((λ_ n) * Real.exp (-(m*(λ_ n))) * B₀ + 2 * env n) := by
        have hxy_le : x - y ≤ |x - y| := le_abs_self _
        have henvnn : 0 ≤ env n := le_trans (abs_nonneg _) (hbnd 0
          (by rw [Set.uIcc_of_le (le_trans hy0 hyx)]; exact ⟨le_rfl, le_trans hy0 hyx⟩))
        have h1 : (λ_ n) * |x - y| * Real.exp (-(m*(λ_ n))) * B₀
            = |x - y| * ((λ_ n) * Real.exp (-(m*(λ_ n))) * B₀) := by ring
        have h2 : 2 * (x - y) * env n ≤ |x - y| * (2 * env n) := by
          have : 2 * (x - y) * env n = (x - y) * (2 * env n) := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_right hxy_le
          positivity
        rw [h1, mul_add]; linarith

/-- **The summable majorant.**  `∑ₙ ((λₙ·e^{-λₙ·m})·B₀ + 2·env n)` converges for
`m > 0` (heat damping) and summable `env`. -/
theorem restartDiff_majorant_summable {m B₀ : ℝ} {env : ℕ → ℝ}
    (hm : 0 < m) (henv : Summable env) :
    Summable (fun n => (λ_ n) * Real.exp (-(m*(λ_ n))) * B₀ + 2 * env n) := by
  have hheat : Summable (fun n : ℕ => (λ_ n) * Real.exp (-(m * (λ_ n)))) := by
    have := ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable hm
    simpa using this
  exact (hheat.mul_right B₀).add (henv.mul_left 2)

/-! ## 4b. Per-series absolute summability (each horizon individually). -/

/-- `∑ₙ e^{-x·λₙ}` converges for `x > 0` (heat smoothing). -/
theorem exp_neg_eigenvalue_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => Real.exp (-(x * (λ_ n)))) := by
  have hlamexp0 :=
    ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
      (τ := x) hx
  have hlamexp : Summable (fun n : ℕ => (λ_ n) * Real.exp (-(x * (λ_ n)))) := by
    simpa only [neg_mul] using hlamexp0
  rw [← summable_nat_add_iff 1]
  rw [← summable_nat_add_iff
    (f := fun n => (λ_ n) * Real.exp (-(x * (λ_ n)))) 1] at hlamexp
  refine Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_) hlamexp
  have hlam1 : (1:ℝ) ≤ (λ_ (n+1)) := by
    unfold unitIntervalCosineEigenvalue
    have hn1 : (1:ℝ) ≤ ((n:ℝ)+1) := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
    have hpi : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    push_cast
    nlinarith [mul_le_mul hn1 hpi (by linarith) (by linarith : (0:ℝ) ≤ ((n:ℝ)+1))]
  calc Real.exp (-(x * (λ_ (n+1))))
      = 1 * Real.exp (-(x * (λ_ (n+1)))) := (one_mul _).symm
    _ ≤ (λ_ (n+1)) * Real.exp (-(x * (λ_ (n+1)))) :=
        mul_le_mul_of_nonneg_right hlam1 (Real.exp_nonneg _)

/-- **Crude per-mode restart bound.**  For `0 < x`, `|a₀ n| ≤ B₀`, `|a r n| ≤ env n`
on `[0, x]`, `a`'s mode `n` continuous-on,

    `|restartDuhamelCoeff a₀ a x n| ≤ e^{-x·λₙ}·B₀ + x·env n`. -/
theorem abs_restartDuhamelCoeff_le {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {x B₀ : ℝ} {env : ℕ → ℝ} {n : ℕ}
    (hx : 0 < x) (hB₀ : |a₀ n| ≤ B₀)
    (hbnd : ∀ r ∈ Set.uIcc (0:ℝ) x, |a r n| ≤ env n) :
    |restartDuhamelCoeff a₀ a x n| ≤ Real.exp (-(x*(λ_ n))) * B₀ + x * env n := by
  have hlam : 0 ≤ (λ_ n) := by unfold unitIntervalCosineEigenvalue; positivity
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · -- homogeneous: |e^{-xλ}·a₀| = e^{-xλ}·|a₀| ≤ e^{-xλ}·B₀
    rw [show Real.exp (-x * (λ_ n)) = Real.exp (-(x*(λ_ n))) by rw [neg_mul], abs_mul,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hB₀ (Real.exp_nonneg _)
  · -- Duhamel: |duhamelSpectralCoeff a x n| ≤ x·env n  (crude bound).
    refine le_trans (ShenWork.IntervalPicardLimitRestartBdd.abs_duhamelSpectralCoeff_le_of_bound
      hx n ?_) (le_of_eq rfl)
    intro s hs hsx
    exact hbnd s (by rw [Set.uIcc_of_le hx.le]; exact ⟨hs, hsx⟩)

/-- **Per-horizon absolute summability** of the restart cosine series.  Each fixed
horizon `x > 0` gives an absolutely-summable series (homogeneous part damped by
`e^{-x·λ}`, Duhamel part by the summable envelope). -/
theorem restartCosineSeries_summable {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {x B₀ : ℝ} {env : ℕ → ℝ}
    (hx : 0 < x) (hB₀ : ∀ n, |a₀ n| ≤ B₀) (henv : Summable env)
    (hbnd : ∀ n, ∀ r ∈ Set.uIcc (0:ℝ) x, |a r n| ≤ env n)
    (z : ℝ) :
    Summable (fun n => restartDuhamelCoeff a₀ a x n * cosineMode n z) := by
  have hmaj : Summable (fun n => Real.exp (-(x*(λ_ n))) * B₀ + x * env n) :=
    ((exp_neg_eigenvalue_summable hx).mul_right B₀).add (henv.mul_left x)
  have hbase : Summable (fun n => |restartDuhamelCoeff a₀ a x n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => abs_restartDuhamelCoeff_le hx (hB₀ n) (fun r hr => hbnd n r hr)) hmaj
  refine hbase.of_norm_bounded (g := fun n => |restartDuhamelCoeff a₀ a x n|) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  have hcos : |cosineMode n z| ≤ 1 := by unfold cosineMode; exact Real.abs_cos_le_one _
  calc |restartDuhamelCoeff a₀ a x n| * |cosineMode n z|
      ≤ |restartDuhamelCoeff a₀ a x n| * 1 :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |restartDuhamelCoeff a₀ a x n| := mul_one _

/-! ## 5. The sup-norm restart-series difference bound. -/

/-- **The capstone bound.**  Under the per-mode hypotheses (`m`-damping floor below
both horizons, base bound `B₀`, time-continuous source modes with summable envelope
`env` on `[0, x]`), the restart cosine series difference is `|x − y|`-Lipschitz
**uniformly in the spatial point `z`**:

    `|∑ₙ (restartDuhamelCoeff a₀ a x n − restartDuhamelCoeff a₀ a y n)·cosineMode n z|`
      `≤ |x − y| · (B₀·∑ₙ λₙ e^{-λₙ m} + 2·∑ₙ env n)`. -/
theorem restartSeries_sup_diff_le {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {x y m B₀ : ℝ} {env : ℕ → ℝ}
    (hmy : m ≤ y) (hyx : y ≤ x) (hm : 0 < m) (hB₀ : ∀ n, |a₀ n| ≤ B₀)
    (henv : Summable env)
    (hacont : ∀ n, ContinuousOn (fun r => a r n) (Set.uIcc (0:ℝ) x))
    (hbnd : ∀ n, ∀ r ∈ Set.uIcc (0:ℝ) x, |a r n| ≤ env n)
    (z : ℝ) :
    |∑' n, (restartDuhamelCoeff a₀ a x n - restartDuhamelCoeff a₀ a y n) * cosineMode n z|
      ≤ |x - y| * (∑' n, ((λ_ n) * Real.exp (-(m*(λ_ n))) * B₀ + 2 * env n)) := by
  set D : ℕ → ℝ := fun n => restartDuhamelCoeff a₀ a x n - restartDuhamelCoeff a₀ a y n with hD
  set maj : ℕ → ℝ := fun n => |x - y| * ((λ_ n) * Real.exp (-(m*(λ_ n))) * B₀ + 2 * env n)
    with hmaj
  have hm0 : 0 ≤ m := le_of_lt hm
  -- per-mode bound |D n| ≤ maj n
  have hpm : ∀ n, |D n| ≤ maj n := fun n =>
    abs_restartDuhamelCoeff_diff_le hmy hyx hm0 (hB₀ n) (hacont n) (fun r hr => hbnd n r hr)
  -- summable majorant
  have hmajsum : Summable maj := by
    rw [hmaj]
    exact (restartDiff_majorant_summable hm henv).mul_left _
  -- summable |D| and D
  have hDabs_sum : Summable (fun n => |D n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpm hmajsum
  have hD_sum : Summable D := by
    refine hDabs_sum.of_norm_bounded (g := fun n => |D n|) ?_
    intro n; rw [Real.norm_eq_abs]
  have hcos : ∀ n : ℕ, |cosineMode n z| ≤ 1 := by
    intro n; unfold cosineMode; exact Real.abs_cos_le_one _
  -- sup bound
  have hsum2 : Summable (fun n => D n * cosineMode n z) := by
    refine hDabs_sum.of_norm_bounded (g := fun n => |D n|) ?_
    intro n; rw [Real.norm_eq_abs, abs_mul]
    calc |D n| * |cosineMode n z| ≤ |D n| * 1 :=
          mul_le_mul_of_nonneg_left (hcos n) (abs_nonneg _)
      _ = |D n| := mul_one _
  have hle1 : ∀ n, |D n * cosineMode n z| ≤ |D n| := by
    intro n; rw [abs_mul]
    calc |D n| * |cosineMode n z| ≤ |D n| * 1 :=
          mul_le_mul_of_nonneg_left (hcos n) (abs_nonneg _)
      _ = |D n| := mul_one _
  have hstep1 : |∑' n, D n * cosineMode n z| ≤ ∑' n, |D n| := by
    calc |∑' n, D n * cosineMode n z| = ‖∑' n, D n * cosineMode n z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' n, ‖D n * cosineMode n z‖ :=
          norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hsum2.abs)
      _ = ∑' n, |D n * cosineMode n z| := by simp_rw [Real.norm_eq_abs]
      _ ≤ ∑' n, |D n| := Summable.tsum_le_tsum hle1 hsum2.abs hDabs_sum
  have hstep2 : ∑' n, |D n| ≤ ∑' n, maj n :=
    Summable.tsum_le_tsum hpm hDabs_sum hmajsum
  have hmaj_eq : ∑' n, maj n
      = |x - y| * (∑' n, ((λ_ n) * Real.exp (-(m*(λ_ n))) * B₀ + 2 * env n)) := by
    rw [hmaj, tsum_mul_left]
  calc |∑' n, D n * cosineMode n z| ≤ ∑' n, |D n| := hstep1
    _ ≤ ∑' n, maj n := hstep2
    _ = |x - y| * (∑' n, ((λ_ n) * Real.exp (-(m*(λ_ n))) * B₀ + 2 * env n)) := hmaj_eq

end ShenWork.IntervalRestartSeriesLipschitz
