import ShenWork.PDE.IntervalDuhamelClosedC2

/-!
# Window-local one-sided Duhamel source packages

This file weakens `DuhamelSourceTimeC1` to a closed-window interface.  The main
consumer is the eigenvalue-weighted Duhamel coefficient summability proof, with
the time integration-by-parts step re-run using the one-sided interval FTC.
-/

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDuhamelClosedC2

noncomputable section

namespace ShenWork.IntervalDuhamelSourceTimeC1On

/-- Window-local one-sided time-`C¹` package for Duhamel source coefficients. -/
structure DuhamelSourceTimeC1On (a : ℝ → ℕ → ℝ) (lo hi : ℝ) where
  adot : ℝ → ℕ → ℝ
  hderiv : ∀ s ∈ Set.Icc lo hi, ∀ n,
    HasDerivWithinAt (fun r => a r n) (adot s n) (Set.Icc lo hi) s
  hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Set.Icc lo hi)
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s ∈ Set.Icc lo hi, ∀ n, |a s n| ≤ envelope n
  derivBound : ℝ
  hderivBound : ∀ s ∈ Set.Icc lo hi, ∀ n, |adot s n| ≤ derivBound

/-- Forget a global two-sided source package to a closed-window one-sided package
on a nonnegative window. -/
def DuhamelSourceTimeC1.toOn {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (lo hi : ℝ) (hlo : 0 ≤ lo) : DuhamelSourceTimeC1On a lo hi where
  adot := src.adot
  hderiv := fun s _ n => (src.hderiv s n).hasDerivWithinAt
  hadotcont := fun n => (src.hadotcont n).continuousOn
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := fun s hs n => src.henv_bound s (le_trans hlo hs.1) n
  derivBound := src.derivBound
  hderivBound := fun s hs n => src.hderivBound s (le_trans hlo hs.1) n

/-- Shift a closed-window source on `[offset, offset + W]` to `[0, W]`. -/
def DuhamelSourceTimeC1On.shift_zero {a : ℝ → ℕ → ℝ} {offset W : ℝ}
    (src : DuhamelSourceTimeC1On a offset (offset + W)) :
    DuhamelSourceTimeC1On (fun s n => a (offset + s) n) 0 W where
  adot := fun s n => src.adot (offset + s) n
  hderiv := by
    intro s hs n
    have hmap : Set.MapsTo (fun r : ℝ => offset + r)
        (Set.Icc (0 : ℝ) W) (Set.Icc offset (offset + W)) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hlin : HasDerivWithinAt (fun r : ℝ => offset + r) 1
        (Set.Icc (0 : ℝ) W) s :=
      ((hasDerivAt_id s).const_add offset).hasDerivWithinAt
    have hsrc := src.hderiv (offset + s) (hmap hs) n
    have hcomp := hsrc.comp s hlin hmap
    simpa [Function.comp] using hcomp
  hadotcont := by
    intro n
    have hmap : Set.MapsTo (fun r : ℝ => offset + r)
        (Set.Icc (0 : ℝ) W) (Set.Icc offset (offset + W)) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact (src.hadotcont n).comp
      ((continuous_const.add continuous_id).continuousOn) hmap
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := by
    intro s hs n
    exact src.henv_bound (offset + s)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ n
  derivBound := src.derivBound
  hderivBound := by
    intro s hs n
    exact src.hderivBound (offset + s)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ n

/-- Restrict a closed-window source package to a smaller upper endpoint. -/
def DuhamelSourceTimeC1On.restrict_hi {a : ℝ → ℕ → ℝ} {lo hi hi' : ℝ}
    (src : DuhamelSourceTimeC1On a lo hi) (hhi' : hi' ≤ hi) :
    DuhamelSourceTimeC1On a lo hi' where
  adot := src.adot
  hderiv := by
    intro s hs n
    exact (src.hderiv s ⟨hs.1, le_trans hs.2 hhi'⟩ n).mono
      (Set.Icc_subset_Icc le_rfl hhi')
  hadotcont := by
    intro n
    exact (src.hadotcont n).mono (Set.Icc_subset_Icc le_rfl hhi')
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := by
    intro s hs n
    exact src.henv_bound s ⟨hs.1, le_trans hs.2 hhi'⟩ n
  derivBound := src.derivBound
  hderivBound := by
    intro s hs n
    exact src.hderivBound s ⟨hs.1, le_trans hs.2 hhi'⟩ n

/-- **Scalar multiplication preserves `DuhamelSourceTimeC1On`.** -/
noncomputable def DuhamelSourceTimeC1On.const_mul {a : ℝ → ℕ → ℝ} {lo hi : ℝ}
    (src : DuhamelSourceTimeC1On a lo hi) (c : ℝ) :
    DuhamelSourceTimeC1On (fun s n => c * a s n) lo hi where
  adot := fun s n => c * src.adot s n
  hderiv := by
    intro s hs n
    exact (src.hderiv s hs n).const_mul c
  hadotcont := by
    intro n
    exact continuousOn_const.mul (src.hadotcont n)
  envelope := fun n => |c| * src.envelope n
  henv_summable := src.henv_summable.mul_left |c|
  henv_bound := by
    intro s hs n
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (src.henv_bound s hs n) (abs_nonneg c)
  derivBound := |c| * src.derivBound
  hderivBound := by
    intro s hs n
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (src.hderivBound s hs n) (abs_nonneg c)

/-- **Addition preserves `DuhamelSourceTimeC1On`.** -/
noncomputable def DuhamelSourceTimeC1On.add {a b : ℝ → ℕ → ℝ} {lo hi : ℝ}
    (ha : DuhamelSourceTimeC1On a lo hi) (hb : DuhamelSourceTimeC1On b lo hi) :
    DuhamelSourceTimeC1On (fun s n => a s n + b s n) lo hi where
  adot := fun s n => ha.adot s n + hb.adot s n
  hderiv := by
    intro s hs n
    exact (ha.hderiv s hs n).add (hb.hderiv s hs n)
  hadotcont := by
    intro n
    exact (ha.hadotcont n).add (hb.hadotcont n)
  envelope := fun n => ha.envelope n + hb.envelope n
  henv_summable := ha.henv_summable.add hb.henv_summable
  henv_bound := by
    intro s hs n
    exact (abs_add_le _ _).trans
      (add_le_add (ha.henv_bound s hs n) (hb.henv_bound s hs n))
  derivBound := ha.derivBound + hb.derivBound
  hderivBound := by
    intro s hs n
    exact (abs_add_le _ _).trans
      (add_le_add (ha.hderivBound s hs n) (hb.hderivBound s hs n))

/-- Per-mode time integration by parts from one-sided closed-window derivative data. -/
theorem duhamelCoeff_eigenvalue_mul_on
    {lo hi t lam : ℝ} {a adot : ℝ → ℝ} (_hlohi : lo ≤ hi)
    (htlo : lo ≤ t) (hthi : t ≤ hi)
    (hda : ∀ s ∈ Set.Icc lo t, HasDerivWithinAt a (adot s) (Set.Icc lo hi) s)
    (hadotcont : ContinuousOn adot (Set.Icc lo hi)) :
    lam * (∫ s in lo..t, Real.exp (-(t - s) * lam) * a s)
      = a t - Real.exp (-(t - lo) * lam) * a lo
        - ∫ s in lo..t, Real.exp (-(t - s) * lam) * adot s := by
  have hlt : lo ≤ t := htlo
  have hIcc_sub : Set.Icc lo t ⊆ Set.Icc lo hi := fun s hs => ⟨hs.1, le_trans hs.2 hthi⟩
  have hacont : ContinuousOn a (Set.Icc lo t) := by
    intro s hs
    exact ((hda s hs).mono hIcc_sub).continuousWithinAt
  have hexp : ∀ s, HasDerivAt (fun s : ℝ => Real.exp (-(t - s) * lam))
      (lam * Real.exp (-(t - s) * lam)) s := by
    intro s
    have harg : HasDerivAt (fun s : ℝ => -(t - s) * lam) lam s := by
      have h1 : HasDerivAt (fun s : ℝ => -(t - s)) 1 s := by
        have : HasDerivAt (fun s : ℝ => s - t) 1 s := by
          simpa using (hasDerivAt_id s).sub_const t
        refine this.congr_of_eventuallyEq ?_
        filter_upwards with y using by ring
      simpa using h1.mul_const lam
    simpa [mul_comm] using harg.exp
  have hw : ∀ s ∈ Set.Ioo lo t,
      HasDerivWithinAt (fun s : ℝ => a s * Real.exp (-(t - s) * lam))
        (adot s * Real.exp (-(t - s) * lam)
          + a s * (lam * Real.exp (-(t - s) * lam))) (Set.Ioi s) s := by
    intro s hs
    have hsI : s ∈ Set.Icc lo t := ⟨hs.1.le, hs.2.le⟩
    have hs_nhds : Set.Icc lo hi ∈ 𝓝 s := by
      have hopen : Set.Ioo lo hi ∈ 𝓝 s :=
        isOpen_Ioo.mem_nhds ⟨hs.1, lt_of_lt_of_le hs.2 hthi⟩
      exact Filter.mem_of_superset hopen Set.Ioo_subset_Icc_self
    exact ((hda s hsI).hasDerivAt hs_nhds).mul (hexp s) |>.hasDerivWithinAt
  have hcont' : ContinuousOn (fun s : ℝ => adot s * Real.exp (-(t - s) * lam)
      + a s * (lam * Real.exp (-(t - s) * lam))) (Set.Icc lo t) := by
    have he : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
    exact ((hadotcont.mono hIcc_sub).mul he.continuousOn).add
      (hacont.mul ((continuous_const.mul he).continuousOn))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hlt
    (f := fun s : ℝ => a s * Real.exp (-(t - s) * lam))
    (f' := fun s : ℝ => adot s * Real.exp (-(t - s) * lam)
      + a s * (lam * Real.exp (-(t - s) * lam)))
    (by
      have he : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
      exact hacont.mul he.continuousOn)
    hw (by
      exact hcont'.intervalIntegrable_of_Icc hlt)
  change (∫ y in lo..t,
      adot y * Real.exp (-(t - y) * lam) + a y * (lam * Real.exp (-(t - y) * lam)))
    = a t * Real.exp (-(t - t) * lam) - a lo * Real.exp (-(t - lo) * lam) at hFTC
  have hwt : a t * Real.exp (-(t - t) * lam) = a t := by simp
  have hwlo : a lo * Real.exp (-(t - lo) * lam)
      = Real.exp (-(t - lo) * lam) * a lo := by ring
  rw [hwt, hwlo] at hFTC
  have hi1 : IntervalIntegrable
      (fun s => adot s * Real.exp (-(t - s) * lam)) volume lo t := by
    have he : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
    exact ((hadotcont.mono hIcc_sub).mul he.continuousOn).intervalIntegrable_of_Icc hlt
  have hi2 : IntervalIntegrable
      (fun s => a s * (lam * Real.exp (-(t - s) * lam))) volume lo t := by
    have he : Continuous (fun s : ℝ => Real.exp (-(t - s) * lam)) := by fun_prop
    exact (hacont.mul ((continuous_const.mul he).continuousOn)).intervalIntegrable_of_Icc hlt
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  have he1 : (∫ s in lo..t, a s * (lam * Real.exp (-(t - s) * lam)))
      = lam * ∫ s in lo..t, Real.exp (-(t - s) * lam) * a s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => by ring)
  have he2 : (∫ s in lo..t, adot s * Real.exp (-(t - s) * lam))
      = ∫ s in lo..t, Real.exp (-(t - s) * lam) * adot s :=
    intervalIntegral.integral_congr (fun s _ => by ring)
  rw [he1, he2] at hFTC
  linarith [hFTC]

/-- Windowed eigenvalue-weighted coefficient summability. -/
theorem duhamelSpectralCoeff_eigenvalue_summable_on
    {lo hi t : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1On a lo hi) (htlo : lo < t) (hthi : t ≤ hi) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |∫ s in lo..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n|) := by
  have hlohi : lo ≤ hi := le_trans htlo.le hthi
  have hnn : ∀ n, 0 ≤ src.envelope n :=
    fun n => le_trans (abs_nonneg _) (src.henv_bound lo ⟨le_rfl, hlohi⟩ n)
  have hdbnn : 0 ≤ src.derivBound :=
    le_trans (abs_nonneg _) (src.hderivBound lo ⟨le_rfl, hlohi⟩ 0)
  have hM : Summable (fun n => 2 * src.envelope n
      + src.derivBound * ∫ s in lo..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) :=
    (src.henv_summable.mul_left 2).add
      (by
        have hshift := duhamelGainIntegral_summable (t := t - lo)
          (Mdot := src.derivBound) (by linarith) hdbnn
        have hgain : (fun n => src.derivBound * ∫ s in lo..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n))
            = (fun n => src.derivBound * ∫ s in (0 : ℝ)..t - lo,
              Real.exp (-((t - lo) - s) * unitIntervalCosineEigenvalue n)) := by
          funext n
          congr 1
          calc
            ∫ s in lo..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
                = ∫ s in (0 : ℝ)..t - lo,
                    Real.exp (-(t - (s + lo)) * unitIntervalCosineEigenvalue n) := by
              symm
              simpa [zero_add, sub_add_cancel] using
                intervalIntegral.integral_comp_add_right
                  (a := (0 : ℝ)) (b := t - lo)
                  (fun s : ℝ =>
                    Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) lo
            _ = ∫ s in (0 : ℝ)..t - lo,
                    Real.exp (-((t - lo) - s) * unitIntervalCosineEigenvalue n) := by
              refine intervalIntegral.integral_congr (fun s _ => ?_)
              congr 1
              ring
        rw [hgain]
        exact hshift)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg ?_ (abs_nonneg _)) (fun n => ?_) hM
  · unfold unitIntervalCosineEigenvalue; positivity
  · have hlamnn : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have hkey := duhamelCoeff_eigenvalue_mul_on (lo := lo) (hi := hi) (t := t)
      (lam := unitIntervalCosineEigenvalue n) (a := fun s => a s n)
      (adot := fun s => src.adot s n) hlohi htlo.le hthi
      (fun s hs => src.hderiv s (⟨hs.1, le_trans hs.2 hthi⟩) n) (src.hadotcont n)
    have hconv : unitIntervalCosineEigenvalue n *
          |∫ s in lo..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n|
        = |a t n - Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * a lo n
            - ∫ s in lo..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| := by
      have key := congrArg abs hkey
      rw [abs_mul, abs_of_nonneg hlamnn] at key
      exact key
    rw [hconv]
    have hb1 : |a t n| ≤ src.envelope n := src.henv_bound t ⟨htlo.le, hthi⟩ n
    have hexp_le : Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ (t - lo) * unitIntervalCosineEigenvalue n := mul_nonneg (by linarith) hlamnn
      linarith
    have hb2 : |Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * a lo n|
        ≤ src.envelope n := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * |a lo n|
          ≤ 1 * |a lo n| := mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)
        _ = |a lo n| := one_mul _
        _ ≤ src.envelope n := src.henv_bound lo ⟨le_rfl, hlohi⟩ n
    have hI_bound : |∫ s in lo..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
        ≤ src.derivBound * ∫ s in lo..t,
            Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
      have hkernel : Continuous
          (fun s : ℝ => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)) := by fun_prop
      have hII1 : IntervalIntegrable
          (fun s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n)
          volume lo t := by
        exact (hkernel.continuousOn.mul ((src.hadotcont n).mono
          (fun s hs => ⟨hs.1, le_trans hs.2 hthi⟩))).intervalIntegrable_of_Icc htlo.le
      calc |∫ s in lo..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
          = ‖∫ s in lo..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in lo..t,
              ‖Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n‖ :=
            intervalIntegral.norm_integral_le_integral_norm htlo.le
        _ ≤ ∫ s in lo..t,
              src.derivBound * Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            apply intervalIntegral.integral_mono_on htlo.le hII1.norm
              (by apply Continuous.intervalIntegrable; fun_prop)
            intro s hs
            have hsI : s ∈ Set.Icc lo t := by
              simpa [Set.uIcc_of_le htlo.le] using hs
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
              mul_comm src.derivBound]
            exact mul_le_mul_of_nonneg_left
              (src.hderivBound s ⟨hsI.1, le_trans hsI.2 hthi⟩ n) (Real.exp_nonneg _)
        _ = src.derivBound * ∫ s in lo..t,
              Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
            rw [intervalIntegral.integral_const_mul]
    calc |a t n - Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * a lo n
            - ∫ s in lo..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n|
        ≤ |a t n - Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * a lo n|
            + |∫ s in lo..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| := by
          have := abs_add_le (a t n -
              Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * a lo n)
            (-(∫ s in lo..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n))
          simpa [sub_eq_add_neg, abs_neg] using this
      _ ≤ (|a t n| + |Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * a lo n|)
            + |∫ s in lo..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n| := by
          gcongr
          have := abs_add_le (a t n)
            (-(Real.exp (-(t - lo) * unitIntervalCosineEigenvalue n) * a lo n))
          simpa [sub_eq_add_neg, abs_neg] using this
      _ ≤ (src.envelope n + src.envelope n)
            + src.derivBound * ∫ s in lo..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
          gcongr
      _ = 2 * src.envelope n
            + src.derivBound * ∫ s in lo..t,
                Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by ring

end ShenWork.IntervalDuhamelSourceTimeC1On
