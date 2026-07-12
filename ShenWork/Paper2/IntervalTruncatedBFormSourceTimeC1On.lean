import ShenWork.Paper2.IntervalBottomLevelProofs
import ShenWork.Paper2.IntervalBFormCron2TruncatedCoefficientWeakTest
import ShenWork.Paper2.IntervalPicardLimitRestartBdd
import ShenWork.PDE.IntervalDuhamelCoeffFTC
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.PDE.AnalyticSemigroupGen

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn abs_duhamelSpectralCoeff_le_of_bound
   eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound)
open ShenWork.IntervalPicardLimitRestartWeak
  (duhamelSpectralCoeff_general_split_on)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDomain (intervalDomainPoint)

local notation "λ_" n => unitIntervalCosineEigenvalue n

private theorem exp_mono_of_le_time {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    Real.exp (-b * (λ_ n)) ≤ Real.exp (-a * (λ_ n)) := by
  apply Real.exp_le_exp.mpr
  have hlam : 0 ≤ λ_ n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  nlinarith

private theorem lambda_exp_bound {c s : ℝ} (hc : 0 < c) (hcs : c ≤ s) (n : ℕ) :
    (λ_ n) * Real.exp (-s * (λ_ n)) ≤ 1 / c := by
  have hlam : 0 ≤ λ_ n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  calc
    (λ_ n) * Real.exp (-s * (λ_ n))
        ≤ (λ_ n) * Real.exp (-c * (λ_ n)) := by
          exact mul_le_mul_of_nonneg_left (exp_mono_of_le_time hcs n) hlam
    _ = (λ_ n) * Real.exp (-((λ_ n) * c)) := by ring_nf
    _ ≤ 1 / c :=
          ShenWork.PDE.AnalyticSemigroupGen.real_mul_exp_neg_mul_le_inv
            (r := (λ_ n)) (t := c) hc

private def restartCoeffEnvelope
    (src : DuhamelSourceBddOn a W) (c T M₀ : ℝ) (n : ℕ) : ℝ :=
  M₀ * Real.exp (-c * (λ_ n))
    + (c / 2 * src.M) * Real.exp (-(c / 2) * (λ_ n))
    + T * src.env (c / 2) n

private theorem restartCoeffEnvelope_summable
    (src : DuhamelSourceBddOn a W) {c T M₀ : ℝ}
    (hc : 0 < c) (hcW : c / 2 ≤ W) :
    Summable (fun n => restartCoeffEnvelope src c T M₀ n) := by
  unfold restartCoeffEnvelope
  have hc2 : 0 < c / 2 := by linarith
  refine (((ShenWork.IntervalSemigroupComposition.expEigSummable hc).mul_left M₀).add
    (((ShenWork.IntervalSemigroupComposition.expEigSummable hc2).mul_left
      (c / 2 * src.M)).add
      ((src.henv_summable (c / 2) hc2 hcW).mul_left T))).congr ?_
  intro n
  ring

private theorem duhamel_abs_le_split_env
    {a : ℝ → ℕ → ℝ} {W c T s : ℝ}
    (src : DuhamelSourceBddOn a W)
    (hc : 0 < c) (hs : s ∈ Icc c T) (hTW : T < W) (n : ℕ) :
    |duhamelSpectralCoeff a s n| ≤
      (c / 2 * src.M) * Real.exp (-(c / 2) * (λ_ n))
        + T * src.env (c / 2) n := by
  have hc2 : 0 < c / 2 := by linarith
  have hc2_nonneg : 0 ≤ c / 2 := le_of_lt hc2
  have hc2s : c / 2 ≤ s := by linarith [hs.1]
  have hsW : s ≤ W := le_of_lt (lt_of_le_of_lt hs.2 hTW)
  have hsplit := duhamelSpectralCoeff_general_split_on
    (a := a) (T := W) src.hcont hc2_nonneg hc2s hsW n
  rw [hsplit]
  have hhead : |duhamelSpectralCoeff a (c / 2) n| ≤ (c / 2) * src.M :=
    abs_duhamelSpectralCoeff_le_of_bound hc2 n
      (fun r hr0 hrc => src.hM r hr0 (le_trans hrc (le_trans hc2s hsW)) n)
  have htail :
      |duhamelSpectralCoeff (fun σ k => a (c / 2 + σ) k) (s - c / 2) n|
        ≤ (s - c / 2) * src.env (c / 2) n :=
    abs_duhamelSpectralCoeff_le_of_bound (by linarith [hc, hs.1]) n
      (fun r hr0 hrs =>
        src.henv_bound (c / 2) hc2 (c / 2 + r) (by linarith) (by linarith) n)
  have henv_nonneg : 0 ≤ src.env (c / 2) n :=
    le_trans (abs_nonneg _)
      (src.henv_bound (c / 2) hc2 (c / 2) le_rfl (le_trans hc2s hsW) n)
  have htailT : (s - c / 2) * src.env (c / 2) n ≤
      T * src.env (c / 2) n := by
    apply mul_le_mul_of_nonneg_right _ henv_nonneg
    linarith [hs.2, hc2_nonneg]
  calc
    |Real.exp (-(s - c / 2) * (λ_ n)) * duhamelSpectralCoeff a (c / 2) n
        + duhamelSpectralCoeff (fun σ k => a (c / 2 + σ) k) (s - c / 2) n|
      ≤ |Real.exp (-(s - c / 2) * (λ_ n)) * duhamelSpectralCoeff a (c / 2) n|
          + |duhamelSpectralCoeff (fun σ k => a (c / 2 + σ) k) (s - c / 2) n| :=
        abs_add_le _ _
    _ ≤ (c / 2 * src.M) * Real.exp (-(c / 2) * (λ_ n))
          + T * src.env (c / 2) n := by
        apply add_le_add _ (le_trans htail htailT)
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have hexp : Real.exp (-(s - c / 2) * (λ_ n))
            ≤ Real.exp (-(c / 2) * (λ_ n)) := by
          apply Real.exp_le_exp.mpr
          have hlam : 0 ≤ λ_ n := by
            unfold unitIntervalCosineEigenvalue
            positivity
          nlinarith [hs.1, hlam]
        calc
          Real.exp (-(s - c / 2) * (λ_ n)) * |duhamelSpectralCoeff a (c / 2) n|
              ≤ Real.exp (-(c / 2) * (λ_ n)) * ((c / 2) * src.M) :=
            mul_le_mul hexp hhead (abs_nonneg _) (Real.exp_nonneg _)
          _ = (c / 2 * src.M) * Real.exp (-(c / 2) * (λ_ n)) := by ring

private theorem restartCoeff_abs_le_envelope
    {a : ℝ → ℕ → ℝ} {W c T M₀ : ℝ} {a₀ : ℕ → ℝ}
    (src : DuhamelSourceBddOn a W) (_hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    (hc : 0 < c) (hTW : T < W) {s : ℝ} (hs : s ∈ Icc c T) (n : ℕ) :
    |localRestartCoeff a₀ a s n| ≤ restartCoeffEnvelope src c T M₀ n := by
  unfold localRestartCoeff restartCoeffEnvelope
  have hhom :
      |Real.exp (-s * (λ_ n)) * a₀ n| ≤ M₀ * Real.exp (-c * (λ_ n)) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp := exp_mono_of_le_time hs.1 n
    calc
      Real.exp (-s * (λ_ n)) * |a₀ n|
          ≤ Real.exp (-c * (λ_ n)) * M₀ :=
        mul_le_mul hexp (ha₀ n) (abs_nonneg _) (Real.exp_nonneg _)
      _ = M₀ * Real.exp (-c * (λ_ n)) := by ring
  have hduh := duhamel_abs_le_split_env src hc hs hTW n
  calc
    |Real.exp (-s * (λ_ n)) * a₀ n + duhamelSpectralCoeff a s n|
        ≤ M₀ * Real.exp (-c * (λ_ n))
            + ((c / 2 * src.M) * Real.exp (-(c / 2) * (λ_ n))
              + T * src.env (c / 2) n) :=
      (abs_add_le _ _).trans (add_le_add hhom hduh)
    _ = restartCoeffEnvelope src c T M₀ n := by
      unfold restartCoeffEnvelope
      ring

private theorem restartCoeff_adot_abs_le
    {a : ℝ → ℕ → ℝ} {W c T M₀ : ℝ} {a₀ : ℕ → ℝ}
    (src : DuhamelSourceBddOn a W) (_hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    (hc : 0 < c) (hTW : T < W) {s : ℝ} (hs : s ∈ Icc c T) (n : ℕ) :
    |a s n - (λ_ n) * localRestartCoeff a₀ a s n|
      ≤ M₀ / c + 2 * src.M := by
  have hsW : s ≤ W := le_of_lt (lt_of_le_of_lt hs.2 hTW)
  have hsrc : |a s n| ≤ src.M := src.hM s (le_trans hc.le hs.1) hsW n
  have hduh_gain :
      (λ_ n) * |duhamelSpectralCoeff a s n| ≤ src.M :=
    eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound
      (by linarith [hc, hs.1]) n
      (fun r hr0 hrs => src.hM r hr0 (le_trans hrs hsW) n)
      ((src.hcont n).mono (Set.Icc_subset_Icc le_rfl hsW))
  have hhom_gain :
      (λ_ n) * |Real.exp (-s * (λ_ n)) * a₀ n| ≤ M₀ / c := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      (λ_ n) * (Real.exp (-s * (λ_ n)) * |a₀ n|)
          = ((λ_ n) * Real.exp (-s * (λ_ n))) * |a₀ n| := by ring
      _ ≤ (1 / c) * M₀ :=
        mul_le_mul (lambda_exp_bound hc hs.1 n) (ha₀ n) (abs_nonneg _)
          (div_nonneg zero_le_one hc.le)
      _ = M₀ / c := by ring
  have hcoeff_gain :
      (λ_ n) * |localRestartCoeff a₀ a s n| ≤ M₀ / c + src.M := by
    unfold localRestartCoeff
    calc
      (λ_ n) * |Real.exp (-s * (λ_ n)) * a₀ n + duhamelSpectralCoeff a s n|
          ≤ (λ_ n) *
              (|Real.exp (-s * (λ_ n)) * a₀ n| + |duhamelSpectralCoeff a s n|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _)
          (by unfold unitIntervalCosineEigenvalue; positivity)
      _ = (λ_ n) * |Real.exp (-s * (λ_ n)) * a₀ n|
            + (λ_ n) * |duhamelSpectralCoeff a s n| := by ring
      _ ≤ M₀ / c + src.M := add_le_add hhom_gain hduh_gain
  calc
    |a s n - (λ_ n) * localRestartCoeff a₀ a s n|
        ≤ |a s n| + |(λ_ n) * localRestartCoeff a₀ a s n| := by
          rw [sub_eq_add_neg]
          exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ = |a s n| + (λ_ n) * |localRestartCoeff a₀ a s n| := by
          have hlam : 0 ≤ (λ_ n) := by
            unfold unitIntervalCosineEigenvalue
            positivity
          rw [abs_mul, abs_of_nonneg hlam]
    _ ≤ src.M + (M₀ / c + src.M) := add_le_add hsrc hcoeff_gain
    _ = M₀ / c + 2 * src.M := by ring

/-- C0/bounded-source FTC package for positive restart windows. -/
def localRestartCoeff_timeC1On_of_bddSource
    {a : ℝ → ℕ → ℝ} {a₀ : ℕ → ℝ} {W c T M₀ : ℝ}
    (src : DuhamelSourceBddOn a W) (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀) (hc : 0 < c) (hcT : c ≤ T) (hTW : T < W) :
    DuhamelSourceTimeC1On (fun s n => localRestartCoeff a₀ a s n) c T where
  adot := fun s n => a s n - (λ_ n) * localRestartCoeff a₀ a s n
  hderiv := by
    intro s hs n
    have hs0 : 0 < s := lt_of_lt_of_le hc hs.1
    have hsW : s < W := lt_of_le_of_lt hs.2 hTW
    exact ((ShenWork.IntervalDuhamelCoeffFTC.localRestartCoeff_hasDerivAt_of_contSource_relative
      (a₀ := a₀) (a := a) (T := W) hs0 hsW n (src.hcont n))).hasDerivWithinAt
  hadotcont := by
    intro n
    have hcoeff_deriv : ∀ s ∈ Icc c T,
        HasDerivAt (fun r => localRestartCoeff a₀ a r n)
          (a s n - (λ_ n) * localRestartCoeff a₀ a s n) s := by
      intro s hs
      exact ShenWork.IntervalDuhamelCoeffFTC.localRestartCoeff_hasDerivAt_of_contSource_relative
        (a₀ := a₀) (a := a) (T := W) (lt_of_lt_of_le hc hs.1)
        (lt_of_le_of_lt hs.2 hTW) n (src.hcont n)
    have hcoeff_cont : ContinuousOn (fun s => localRestartCoeff a₀ a s n) (Icc c T) :=
      fun s hs => (hcoeff_deriv s hs).continuousAt.continuousWithinAt
    exact ((src.hcont n).mono (Set.Icc_subset_Icc (by linarith) hTW.le)).sub
      (continuousOn_const.mul hcoeff_cont)
  envelope := restartCoeffEnvelope src c T M₀
  henv_summable := restartCoeffEnvelope_summable src hc (by linarith [hcT, hTW])
  henv_bound := fun s hs n => restartCoeff_abs_le_envelope src hM₀ ha₀ hc hTW hs n
  derivBound := M₀ / c + 2 * src.M
  hderivBound := fun s hs n => restartCoeff_adot_abs_le src hM₀ ha₀ hc hTW hs n

/-- The truncated Picard coefficient family, with the plural name used by the
positive-window source-time regularity route. -/
abbrev truncatedBFormSourceCoeffs (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  truncatedPicardCoeff p u₀ u

/-- Positive-window `DuhamelSourceTimeC1On` for the truncated B-form restart
coefficients, driven only by C0/bounded data for the truncated B-form RHS source. -/
def truncatedBFormSourceCoeffs_timeC1On_of_bddSource
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {W c T M₀ : ℝ}
    (src : DuhamelSourceBddOn (truncatedBFormSourceCoeff p u) W)
    (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |truncatedPicardInitialCoeff u₀ n| ≤ M₀)
    (hc : 0 < c) (hcT : c ≤ T) (hTW : T < W) :
    DuhamelSourceTimeC1On (truncatedBFormSourceCoeffs p u₀ u) c T :=
  localRestartCoeff_timeC1On_of_bddSource src hM₀ ha₀ hc hcT hTW

end ShenWork.Paper2.BFormPositiveDatumNegPart
