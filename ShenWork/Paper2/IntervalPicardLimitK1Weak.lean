/-
  ShenWork/Paper2/IntervalPicardLimitK1Weak.lean

  **De-circularized K1 producer (`k1_quadruple_weak`).**

  The K1 producer in `IntervalPicardLimitK1.lean` (`k1_quadruple`) is CIRCULAR:
  its restart engine threads through `clampedSource_duhamelSourceTimeC1`, which
  consumes a full `DuhamelSourceTimeC1` package — i.e. the σ-DERIVATIVE fields
  `adott₀/hderivt₀/hadotcontt₀/hMdott₀`, which are IDENTICAL in shape to its own
  K1 conclusion.  So `k1_quadruple` cannot bootstrap the Provider's K1 fields.

  This file replaces the derivative source by the HONEST WEAK SPINE:

  * the restart engine is driven by a `DuhamelSourceBddOn` package (constant
    k-uniform bound on `[0,W]` + per-compact decaying envelopes + time
    continuity — NO derivative fields), producible from the weak ledger data
    (`hsrc0 : DuhamelSourceL1ContOn`) + per-compact K2 alone via the
    `windowEnv` envelope extraction of `IntervalPicardLimitBddProducer`;
  * the per-mode FTC `duhamelSpectralCoeff_hasDerivAt` needs ONLY continuity of
    `s ↦ a s n`, which the `DuhamelSourceBddOn.hcont` field carries;
  * the term-wise series differentiation and joint continuity are re-proved
    against the bounded package with a FIXED split point (`c₀ := τ₀/4` below the
    evaluation window `Ioo (τ₀/2) W`), giving a single summable derivative-series
    majorant `M·λₙ e^{−c₀λₙ}·(1+c₀) + 2·env c₀ n` valid uniformly on the window.

  The final theorem `k1_quadruple_weak` has the SAME conclusion as `k1_quadruple`
  but its hypothesis set is ONLY the ledger-V2 satisfiable data — NO
  `adott₀/hderivt₀/hadotcontt₀/hMdott₀`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitK1
import ShenWork.Paper2.IntervalPicardLimitBddProducer
import ShenWork.Paper2.IntervalPicardLimitTimeNhdSubtype

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalGradientDuhamelMap
  (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff duhamelSpectralCoeff_hasDerivAt)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
    cosineCoeffs_eq_factor_mul_integral
    cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn duhamelSpectralCoeff_general_split_on)
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn abs_duhamelSpectralCoeff_le_of_bound
    eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound
    summable_abs_duhamelSpectralCoeff_bdd)
open ShenWork.IntervalPicardLimitSourceData
  (restartDuhamelCoeff_eq_localRestartCoeff source_family_eq_w)
open ShenWork.IntervalPicardLimitTimeNhd (picardLimitRestart_general)
open ShenWork.Paper2.ClampedSourceRepresentation (clampedFamily_eq_on)
open ShenWork.IntervalTimeSoftClamp (φ)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalDomain (intervalDomainConstExtend)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.Paper2.TimeNhdSubtype (picardLimitRestart_general_of_subtypeCont)

noncomputable section

namespace ShenWork.Paper2.PicardLimitK1Weak

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## A. Per-mode FTC from continuity alone (window version).

`duhamelSpectralCoeff_hasDerivAt` already needs ONLY `Continuous (fun s => a s n)`
(it derives that from `src.hderiv`, but the derivative is never used otherwise).
We package that fact so a `DuhamelSourceBddOn` (continuity-only) drives it. -/

/-- Per-mode FTC for the Duhamel coefficient from a GLOBAL continuity hypothesis
for the single mode `n`.  Mirrors `duhamelSpectralCoeff_hasDerivAt` with the
continuity supplied directly instead of read off a derivative field. -/
theorem duhamelSpectralCoeff_hasDerivAt_of_cont
    {a : ℝ → ℕ → ℝ} (n : ℕ) (hcont_an : Continuous (fun s => a s n)) (t : ℝ) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r n)
      (a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n) t := by
  set lam := unitIntervalCosineEigenvalue n
  set G : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, Real.exp (s * lam) * a s n
  have hfactor : ∀ r, duhamelSpectralCoeff a r n = Real.exp (-r * lam) * G r := by
    intro r; show (∫ s in (0:ℝ)..r, _) = _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by
      rw [show -(r - s) * lam = -r * lam + s * lam from by ring, Real.exp_add, mul_assoc])
  have hd_exp : HasDerivAt (fun r => Real.exp (-r * lam))
      (-lam * Real.exp (-t * lam)) t := by
    have h1 : HasDerivAt (fun r : ℝ => -r * lam) (-1 * lam) t :=
      (hasDerivAt_id t).neg.mul_const lam
    have h2 := h1.exp
    simp only [neg_mul, one_mul] at h2 ⊢
    convert h2 using 1; ring
  have hG_cont : Continuous (fun s => Real.exp (s * lam) * a s n) :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul hcont_an
  have hd_G : HasDerivAt G (Real.exp (t * lam) * a t n) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hG_cont.intervalIntegrable 0 t)
      hG_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hG_cont.continuousAt
  have hexp_cancel : Real.exp (-t * lam) * Real.exp (t * lam) = 1 := by
    rw [← Real.exp_add, show -t * lam + t * lam = 0 from by ring, Real.exp_zero]
  have hderiv_val :
      -lam * Real.exp (-t * lam) * G t + Real.exp (-t * lam) * (Real.exp (t * lam) * a t n) =
      a t n - lam * (Real.exp (-t * lam) * G t) := by
    rw [← mul_assoc (Real.exp _), hexp_cancel, one_mul]; ring
  have hprod : HasDerivAt (fun r => Real.exp (-r * lam) * G r)
      (a t n - lam * (Real.exp (-t * lam) * G t)) t :=
    (hd_exp.mul hd_G).congr_deriv hderiv_val
  rw [show (fun r => duhamelSpectralCoeff a r n) =
      (fun r => Real.exp (-r * lam) * G r) from funext hfactor, hfactor t]
  exact hprod

/-! ## B. Term-wise differentiation of the restart cosine series (bounded source).

We work on the open connected window `Ioo (τ₀/2) W ∋ τ₀` with the FIXED split
point `c₀ := τ₀/4`.  Each derivative term `(aₙ(τ) − λₙ cₙ(τ))·cos` is bounded
uniformly there by a single summable majorant. -/

variable {a : ℝ → ℕ → ℝ} {W : ℝ}

/-- The uniform derivative-series majorant on `Ioo (τ₀/2) W` with split `c₀`.
`M` bounds the restart-base coeffs `a₀`; `src.M` is the source's own bound. -/
private def derivMajorant (src : DuhamelSourceBddOn a W) (c₀ : ℝ) (M : ℝ) (n : ℕ) : ℝ :=
  M * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) +
    (c₀ * src.M) * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) +
    src.env c₀ n + src.env c₀ n

set_option maxHeartbeats 1000000 in
private theorem derivMajorant_summable (src : DuhamelSourceBddOn a W) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hc₀W : c₀ ≤ W) (M : ℝ) :
    Summable (fun n => derivMajorant src c₀ M n) := by
  unfold derivMajorant
  have hexp := ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
    (τ := c₀) hc₀
  have henv : Summable (src.env c₀) := src.henv_summable c₀ hc₀ hc₀W
  have := (((hexp.mul_left M).add (hexp.mul_left (c₀ * src.M))).add henv).add henv
  refine this.congr (fun n => by ring)

/-- **Per-mode HasDerivAt for the restart coefficient times the cosine.**
`HasDerivAt (fun τ => cₙ(τ)·cos) ((aₙ(τ) − λₙ cₙ(τ))·cos) τ`, with `cₙ` the
`localRestartCoeff`; from the homogeneous derivative + the continuity-only
per-mode FTC. -/
theorem hasDerivAt_localRestartCoeff_mul_cos
    {a₀ : ℕ → ℝ} (n : ℕ) (hcont_an : Continuous (fun s => a s n)) (x τ : ℝ) :
    HasDerivAt (fun r => localRestartCoeff a₀ a r n * cosineMode n x)
      ((a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n)
        * cosineMode n x) τ := by
  set lam := unitIntervalCosineEigenvalue n with hlam
  -- homogeneous piece e^{-τλ}·a₀ₙ
  have hd_hom : HasDerivAt (fun r => Real.exp (-r * lam) * a₀ n)
      (-lam * Real.exp (-τ * lam) * a₀ n) τ := by
    have h1 : HasDerivAt (fun r : ℝ => -r * lam) (-1 * lam) τ :=
      (hasDerivAt_id τ).neg.mul_const lam
    have h2 := (h1.exp).mul_const (a₀ n)
    simp only [neg_mul, one_mul] at h2 ⊢
    convert h2 using 1; ring
  -- Duhamel piece
  have hd_duh := duhamelSpectralCoeff_hasDerivAt_of_cont n hcont_an τ
  -- sum = derivative of localRestartCoeff
  have hsum : HasDerivAt (fun r => localRestartCoeff a₀ a r n)
      (a τ n - lam * localRestartCoeff a₀ a τ n) τ := by
    have hadd := hd_hom.add hd_duh
    have hfun : (fun r => localRestartCoeff a₀ a r n)
        = (fun r => Real.exp (-r * lam) * a₀ n + duhamelSpectralCoeff a r n) := by
      funext r; simp only [localRestartCoeff, hlam]
    rw [hfun]
    refine hadd.congr_deriv ?_
    simp only [localRestartCoeff, hlam]; ring
  exact hsum.mul_const _

/-! ### The per-window uniform derivative-term bound. -/

private theorem deriv_term_abs_le
    {a₀ : ℕ → ℝ} {M : ℝ} (src : DuhamelSourceBddOn a W) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (hcont_a : ∀ n, Continuous (fun s => a s n))
    {c₀ a' : ℝ} (hc₀ : 0 < c₀) (ha'2 : a' = 2 * c₀) (haW : a' ≤ W)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo a' W) (x : ℝ) (n : ℕ) :
    ‖(a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n)
        * cosineMode n x‖ ≤ derivMajorant src c₀ M n := by
  have hcos_le : |cosineMode n x| ≤ 1 := by
    simp only [cosineMode]; exact Real.abs_cos_le_one _
  have hlam_nn : (0 : ℝ) ≤ (λ_ n) := by unfold unitIntervalCosineEigenvalue; positivity
  have hc₀W : c₀ ≤ W := by linarith [ha'2 ▸ haW]
  have hτlt : a' < τ := hτ.1
  have hτW : τ ≤ W := hτ.2.le
  have hc₀τ : c₀ < τ := by rw [ha'2] at hτlt; linarith
  have hc₀le_τ : c₀ ≤ τ := hc₀τ.le
  -- piece B: |a τ n| ≤ env c₀ n
  have hB : |a τ n| ≤ src.env c₀ n := src.henv_bound c₀ hc₀ τ hc₀le_τ hτW n
  -- piece A: λ·exp(-τλ)·|a₀ n| ≤ M·(λ·exp(-c₀λ))
  have hA : (λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|) ≤ M * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) := by
    have hexp_mono : Real.exp (-τ * (λ_ n)) ≤ Real.exp (-c₀ * (λ_ n)) :=
      Real.exp_le_exp_of_le (by nlinarith [hc₀τ])
    calc (λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|)
        ≤ (λ_ n) * (Real.exp (-c₀ * (λ_ n)) * M) := by
          apply mul_le_mul_of_nonneg_left _ hlam_nn
          exact mul_le_mul hexp_mono (ha₀ n) (abs_nonneg _) (Real.exp_nonneg _)
      _ = M * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) := by ring
  -- piece C: λ·|duh a τ n| via split at c₀
  have hsplit : duhamelSpectralCoeff a τ n
      = Real.exp (-(τ - c₀) * (λ_ n)) * duhamelSpectralCoeff a c₀ n
        + duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (τ - c₀) n :=
    duhamelSpectralCoeff_general_split_on (a := a) (T := W)
      src.hcont hc₀.le hc₀le_τ hτW n
  have hτc₀ : 0 < τ - c₀ := by linarith
  -- head: |duh a c₀ n| ≤ c₀·src.M
  have hhead : |duhamelSpectralCoeff a c₀ n| ≤ c₀ * src.M :=
    abs_duhamelSpectralCoeff_le_of_bound hc₀ n
      (fun s hs hsc₀ => src.hM s hs (le_trans hsc₀ hc₀W) n)
  -- tail: λ·|duh shifted (τ-c₀) n| ≤ env c₀ n
  have htail : (λ_ n) * |duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (τ - c₀) n|
      ≤ src.env c₀ n := by
    refine eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound hτc₀ n ?_ ?_
    · intro σ hσ hστc₀
      exact src.henv_bound c₀ hc₀ (c₀ + σ) (by linarith) (by linarith) n
    · have hmaps : Set.MapsTo (fun σ : ℝ => c₀ + σ) (Set.Icc 0 (τ - c₀)) (Set.Icc 0 W) :=
        fun σ hσ => ⟨by linarith [hσ.1, hc₀.le], by linarith [hσ.2]⟩
      exact (src.hcont n).comp (continuous_const.add continuous_id).continuousOn hmaps
  -- assemble piece C
  have hC : (λ_ n) * |duhamelSpectralCoeff a τ n|
      ≤ (c₀ * src.M) * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) + src.env c₀ n := by
    rw [hsplit]
    calc (λ_ n) * |Real.exp (-(τ - c₀) * (λ_ n)) * duhamelSpectralCoeff a c₀ n
            + duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (τ - c₀) n|
        ≤ (λ_ n) * (|Real.exp (-(τ - c₀) * (λ_ n)) * duhamelSpectralCoeff a c₀ n|
            + |duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (τ - c₀) n|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hlam_nn
      _ = (λ_ n) * |Real.exp (-(τ - c₀) * (λ_ n)) * duhamelSpectralCoeff a c₀ n|
            + (λ_ n) * |duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (τ - c₀) n| := by ring
      _ ≤ (c₀ * src.M) * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) + src.env c₀ n := by
          apply add_le_add _ htail
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp_mono : Real.exp (-(τ - c₀) * (λ_ n)) ≤ Real.exp (-c₀ * (λ_ n)) :=
            Real.exp_le_exp_of_le (by nlinarith [hc₀τ])
          calc (λ_ n) * (Real.exp (-(τ - c₀) * (λ_ n)) * |duhamelSpectralCoeff a c₀ n|)
              ≤ (λ_ n) * (Real.exp (-c₀ * (λ_ n)) * (c₀ * src.M)) := by
                apply mul_le_mul_of_nonneg_left _ hlam_nn
                exact mul_le_mul hexp_mono hhead (abs_nonneg _) (Real.exp_nonneg _)
            _ = (c₀ * src.M) * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) := by ring
  -- combine
  rw [Real.norm_eq_abs, abs_mul]
  calc |a τ n - (λ_ n) * localRestartCoeff a₀ a τ n| * |cosineMode n x|
      ≤ |a τ n - (λ_ n) * localRestartCoeff a₀ a τ n| * 1 :=
        mul_le_mul_of_nonneg_left hcos_le (abs_nonneg _)
    _ = |a τ n - (λ_ n) * localRestartCoeff a₀ a τ n| := mul_one _
    _ ≤ |a τ n| + (λ_ n) * |localRestartCoeff a₀ a τ n| := by
        calc |a τ n - (λ_ n) * localRestartCoeff a₀ a τ n|
            ≤ |a τ n| + |(λ_ n) * localRestartCoeff a₀ a τ n| := by
              rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
          _ = |a τ n| + (λ_ n) * |localRestartCoeff a₀ a τ n| := by
              rw [abs_mul, abs_of_nonneg hlam_nn]
    _ ≤ src.env c₀ n + ((λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|)
          + (λ_ n) * |duhamelSpectralCoeff a τ n|) := by
        apply add_le_add hB
        calc (λ_ n) * |localRestartCoeff a₀ a τ n|
            ≤ (λ_ n) * (|Real.exp (-τ * (λ_ n)) * a₀ n| + |duhamelSpectralCoeff a τ n|) := by
              apply mul_le_mul_of_nonneg_left _ hlam_nn
              simp only [localRestartCoeff]; exact abs_add_le _ _
          _ = (λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|) + (λ_ n) * |duhamelSpectralCoeff a τ n| := by
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]; ring
    _ ≤ src.env c₀ n + (M * ((λ_ n) * Real.exp (-c₀ * (λ_ n)))
          + ((c₀ * src.M) * ((λ_ n) * Real.exp (-c₀ * (λ_ n))) + src.env c₀ n)) :=
        add_le_add (le_refl _) (add_le_add hA hC)
    _ = derivMajorant src c₀ M n := by unfold derivMajorant; ring

/-- Pointwise summability of the restart value series at any `τ ∈ (0, W]`. -/
private theorem summable_localRestartCoeff_mul_cos
    {a₀ : ℕ → ℝ} {M : ℝ} (src : DuhamelSourceBddOn a W)
    (ha₀ : ∀ n, |a₀ n| ≤ M) {τ : ℝ} (hτ : 0 < τ) (hτW : τ ≤ W) (x : ℝ) :
    Summable (fun n => localRestartCoeff a₀ a τ n * cosineMode n x) := by
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    simp only [cosineMode]; exact Real.abs_cos_le_one _
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  have hhom : Summable (fun n =>
      Real.exp (-τ * (λ_ n)) * a₀ n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n => Real.exp (-τ * (λ_ n)) * M)
      ((ShenWork.IntervalSemigroupComposition.expEigSummable hτ).mul_right M)
      (fun n => ?_)
    rw [Real.norm_eq_abs,
      show Real.exp (-τ * (λ_ n)) * a₀ n * cosineMode n x =
        Real.exp (-τ * (λ_ n)) * (a₀ n * cosineMode n x) from by ring,
      abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (by rw [abs_mul]
          calc |a₀ n| * |cosineMode n x| ≤ M * 1 :=
                mul_le_mul (ha₀ n) (hcos_le n) (abs_nonneg _) hM0
            _ = M := mul_one _)
      (Real.exp_nonneg _)
  have hduh : Summable (fun n => duhamelSpectralCoeff a τ n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n => |duhamelSpectralCoeff a τ n|)
      (summable_abs_duhamelSpectralCoeff_bdd src hτ hτW) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hcos_le n)
  refine (hhom.add hduh).congr (fun n => ?_)
  simp only [localRestartCoeff]; ring

/-! ## C. The weak restart-series time derivative (Lemma 2+3, bounded engine). -/

set_option maxHeartbeats 1600000 in
/-- **Weak restart cosine-series time derivative.**  For the restart coefficient
`cₙ(τ) = e^{−τλₙ} a₀ₙ + bₙ(τ)`, the series `τ ↦ ∑' n, cₙ(τ) cos(nπx)` has time
derivative `∑' n, (aₙ(τ₀) − λₙ cₙ(τ₀)) cos(nπx)` at every `τ₀ ∈ (0, W)`, driven
by the BOUNDED package (no derivative fields).  Mirror of
`restartCosineSeries_hasDerivAt_time` with the fixed-split majorant. -/
theorem restartCosineSeries_hasDerivAt_time_bdd
    {a₀ : ℕ → ℝ} {M : ℝ} (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceBddOn a W) (hcont_a : ∀ n, Continuous (fun s => a s n))
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hτ₀W : τ₀ < W) (x : ℝ) :
    HasDerivAt
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x)
      (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a τ₀ n) * cosineMode n x) τ₀ := by
  set a' : ℝ := τ₀ / 2 with ha'def
  set c₀ : ℝ := τ₀ / 4 with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  have ha'2 : a' = 2 * c₀ := by rw [ha'def, hc₀def]; ring
  have ha'W : a' ≤ W := by rw [ha'def]; linarith
  have hτ₀mem : τ₀ ∈ Set.Ioo a' W := ⟨by rw [ha'def]; linarith, hτ₀W⟩
  -- the uniform majorant
  set u : ℕ → ℝ := fun n => derivMajorant src c₀ M n with hudef
  have hu : Summable u := derivMajorant_summable src hc₀ (by rw [hc₀def, ha'def] at *; linarith) M
  -- per-mode HasDerivAt on the window
  have hg : ∀ n (τ : ℝ), τ ∈ Set.Ioo a' W → HasDerivAt
      (fun τ => localRestartCoeff a₀ a τ n * cosineMode n x)
      ((a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n)
        * cosineMode n x) τ :=
    fun n τ _ => hasDerivAt_localRestartCoeff_mul_cos n (hcont_a n) x τ
  -- per-mode derivative bound
  have hg' : ∀ n (τ : ℝ), τ ∈ Set.Ioo a' W →
      ‖(a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n)
        * cosineMode n x‖ ≤ u n :=
    fun n τ hτ => deriv_term_abs_le src
      (le_trans (abs_nonneg _) (ha₀ 0)) ha₀ hcont_a hc₀ ha'2 ha'W hτ x n
  -- pointwise summability at τ₀
  have hg0 : Summable (fun n => localRestartCoeff a₀ a τ₀ n * cosineMode n x) :=
    summable_localRestartCoeff_mul_cos src ha₀ hτ₀ hτ₀W.le x
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (isPreconnected_Ioo) hg hg' hτ₀mem hg0 hτ₀mem

/-! ## D. Joint continuity of the value and derivative series (bounded engine).

Both are proved by the local `continuousOn_tsum` pattern of
`duhamelSeries_jointContinuousOn`, on the window `Ioo 0 W ×ˢ univ`, with the
fixed-split majorant (the same split that drives the HasDerivAt majorant). -/

/-- Continuity of each Duhamel coefficient in time (bounded engine, from the
continuity-only per-mode FTC). -/
private theorem duhamelSpectralCoeff_continuous
    (n : ℕ) (hcont_an : Continuous (fun s => a s n)) :
    Continuous (fun τ => duhamelSpectralCoeff a τ n) :=
  continuous_iff_continuousAt.2
    (fun τ => (duhamelSpectralCoeff_hasDerivAt_of_cont n hcont_an τ).continuousAt)

/-- Uniform-on-window bound for the value Duhamel coefficient via fixed split:
for `q ∈ (2c₀, W)`, `|duh a q n| ≤ c₀·M·e^{−c₀λₙ} + W·env c₀ n`. -/
private theorem abs_duhamelSpectralCoeff_le_window
    (src : DuhamelSourceBddOn a W)
    {c₀ q : ℝ} (hc₀ : 0 < c₀) (hc₀W : c₀ ≤ W) (hq1 : 2 * c₀ < q) (hqW : q ≤ W)
    (n : ℕ) :
    |duhamelSpectralCoeff a q n|
      ≤ (c₀ * src.M) * Real.exp (-c₀ * (λ_ n)) + W * src.env c₀ n := by
  have hc₀q : c₀ < q := by linarith
  have hsplit : duhamelSpectralCoeff a q n
      = Real.exp (-(q - c₀) * (λ_ n)) * duhamelSpectralCoeff a c₀ n
        + duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (q - c₀) n :=
    duhamelSpectralCoeff_general_split_on (a := a) (T := W)
      src.hcont hc₀.le hc₀q.le hqW n
  have hqc₀ : 0 < q - c₀ := by linarith
  have hhead : |duhamelSpectralCoeff a c₀ n| ≤ c₀ * src.M :=
    abs_duhamelSpectralCoeff_le_of_bound hc₀ n
      (fun s hs hsc₀ => src.hM s hs (le_trans hsc₀ hc₀W) n)
  have henv_nn : 0 ≤ src.env c₀ n := le_trans (abs_nonneg _)
    (src.henv_bound c₀ hc₀ c₀ le_rfl hc₀W n)
  -- tail crude bound by window envelope
  have htail : |duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (q - c₀) n|
      ≤ (q - c₀) * src.env c₀ n := by
    refine abs_duhamelSpectralCoeff_le_of_bound hqc₀ n (fun s hs hstail => ?_)
    exact src.henv_bound c₀ hc₀ (c₀ + s) (by linarith) (by linarith) n
  rw [hsplit]
  have hexp_mono : Real.exp (-(q - c₀) * (λ_ n)) ≤ Real.exp (-c₀ * (λ_ n)) :=
    Real.exp_le_exp_of_le (by nlinarith [hc₀q,
      (by unfold unitIntervalCosineEigenvalue; positivity : (0:ℝ) ≤ (λ_ n))])
  calc |Real.exp (-(q - c₀) * (λ_ n)) * duhamelSpectralCoeff a c₀ n
          + duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (q - c₀) n|
      ≤ |Real.exp (-(q - c₀) * (λ_ n)) * duhamelSpectralCoeff a c₀ n|
          + |duhamelSpectralCoeff (fun σ k => a (c₀ + σ) k) (q - c₀) n| := abs_add_le _ _
    _ ≤ (c₀ * src.M) * Real.exp (-c₀ * (λ_ n)) + W * src.env c₀ n := by
        apply add_le_add
        · rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
          exact mul_le_mul hhead hexp_mono (Real.exp_nonneg _)
            (mul_nonneg hc₀.le src.hM_nonneg)
        · refine le_trans htail ?_
          exact mul_le_mul_of_nonneg_right (by linarith) henv_nn

set_option maxHeartbeats 1600000 in
/-- **Joint continuity of the bounded restart VALUE series** on `Ioo 0 W ×ˢ univ`. -/
theorem valueSeries_jointContinuousOn_bdd
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceBddOn a W) (hcont_a : ∀ n, Continuous (fun s => a s n)) :
    ContinuousOn
      (Function.uncurry (fun (τ : ℝ) (x : ℝ) =>
        ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x))
      (Set.Ioo (0 : ℝ) W ×ˢ Set.univ) := by
  change ContinuousOn
    (fun p : ℝ × ℝ => ∑' n, localRestartCoeff a₀ a p.1 n * cosineMode n p.2)
    (Set.Ioo 0 W ×ˢ Set.univ)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hτ₀mem, _⟩ := Set.mem_prod.mp hp
  have hτ₀ : 0 < p.1 := (Set.mem_Ioo.mp hτ₀mem).1
  have hτ₀W : p.1 < W := (Set.mem_Ioo.mp hτ₀mem).2
  set c₀ : ℝ := p.1 / 4 with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  have hc₀W : c₀ ≤ W := by rw [hc₀def]; linarith
  -- window Ioo (p.1/2) W ∋ p.1
  set lo : ℝ := p.1 / 2 with hlodef
  have hcos_le : ∀ n (y : ℝ), |cosineMode n y| ≤ 1 := fun n y => by
    simp only [cosineMode]; exact Real.abs_cos_le_one _
  -- summable majorant on the window
  set g : ℕ → ℝ := fun n =>
    Real.exp (-lo * (λ_ n)) * M
      + ((c₀ * src.M) * Real.exp (-c₀ * (λ_ n)) + W * src.env c₀ n) with hgdef
  have hg_sum : Summable g := by
    have h1 : Summable (fun n => Real.exp (-lo * (λ_ n)) * M) :=
      (ShenWork.IntervalSemigroupComposition.expEigSummable
        (by rw [hlodef]; linarith)).mul_right M
    have h2 : Summable (fun n => (c₀ * src.M) * Real.exp (-c₀ * (λ_ n))) := by
      have := (ShenWork.IntervalSemigroupComposition.expEigSummable hc₀).mul_left (c₀ * src.M)
      exact this
    have h3 : Summable (fun n => W * src.env c₀ n) :=
      (src.henv_summable c₀ hc₀ hc₀W).mul_left W
    exact h1.add (h2.add h3)
  have hcont_on : ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, localRestartCoeff a₀ a q.1 n * cosineMode n q.2)
      (Set.Ioo lo W ×ˢ Set.univ) := by
    apply continuousOn_tsum
    · intro n
      apply ContinuousOn.mul
      · have : Continuous (fun τ => localRestartCoeff a₀ a τ n) := by
          have he : Continuous (fun τ : ℝ => Real.exp (-τ * (λ_ n)) * a₀ n) :=
            ((Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
              continuous_const)
          have hd := duhamelSpectralCoeff_continuous n (hcont_a n)
          have heq : (fun τ => localRestartCoeff a₀ a τ n)
              = (fun τ => Real.exp (-τ * (λ_ n)) * a₀ n + duhamelSpectralCoeff a τ n) := by
            funext τ; simp only [localRestartCoeff]
          rw [heq]; exact he.add hd
        exact (this.comp continuous_fst).continuousOn
      · exact ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn)
    · exact hg_sum
    · intro n q hq
      obtain ⟨hτ, _⟩ := Set.mem_prod.mp hq
      have hqlo : lo < q.1 := (Set.mem_Ioo.mp hτ).1
      have hqW : q.1 ≤ W := (Set.mem_Ioo.mp hτ).2.le
      have hq2c₀ : 2 * c₀ < q.1 := by rw [hc₀def] at *; rw [hlodef] at hqlo; linarith
      rw [Real.norm_eq_abs, abs_mul]
      have hcbound : |localRestartCoeff a₀ a q.1 n|
          ≤ Real.exp (-lo * (λ_ n)) * M
            + ((c₀ * src.M) * Real.exp (-c₀ * (λ_ n)) + W * src.env c₀ n) := by
        refine (abs_add_le _ _).trans ?_
        apply add_le_add
        · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp_mono : Real.exp (-q.1 * (λ_ n)) ≤ Real.exp (-lo * (λ_ n)) :=
            Real.exp_le_exp_of_le (by nlinarith [hqlo,
              (by unfold unitIntervalCosineEigenvalue; positivity : (0:ℝ) ≤ (λ_ n))])
          exact mul_le_mul hexp_mono (ha₀ n) (abs_nonneg _) (Real.exp_nonneg _)
        · exact abs_duhamelSpectralCoeff_le_window src hc₀ hc₀W hq2c₀ hqW n
      calc |localRestartCoeff a₀ a q.1 n| * |cosineMode n q.2|
          ≤ g n * 1 := mul_le_mul hcbound (hcos_le n q.2) (abs_nonneg _) (by
            refine le_trans (abs_nonneg _) hcbound)
        _ = g n := mul_one _
  have hmem : p ∈ Set.Ioo lo W ×ˢ (Set.univ : Set ℝ) :=
    ⟨Set.mem_Ioo.mpr ⟨by rw [hlodef]; linarith, hτ₀W⟩, Set.mem_univ _⟩
  have hopen : IsOpen (Set.Ioo lo W ×ˢ (Set.univ : Set ℝ)) :=
    IsOpen.prod isOpen_Ioo isOpen_univ
  exact hcont_on.continuousAt (hopen.mem_nhds hmem)

theorem windowEnv_le_const {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    ShenWork.IntervalPicardLimitBddProducer.windowEnv C k ≤ C := by
  unfold ShenWork.IntervalPicardLimitBddProducer.windowEnv
  split
  · exact le_refl _
  · rename_i hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hden : (1 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
      nlinarith [Real.pi_gt_three, hk1, sq_nonneg ((k:ℝ) * Real.pi - 1)]
    rw [div_le_iff₀ (by nlinarith [hden] : (0:ℝ) < ((k : ℝ) * Real.pi) ^ 2)]
    nlinarith [hC, hden]

set_option maxHeartbeats 1600000 in
/-- **Joint continuity of the bounded restart DERIVATIVE series** on
`Ioo 0 W ×ˢ univ`: `(τ, x) ↦ ∑' n, (aₙ(τ) − λₙ cₙ(τ)) cos(nπx)`. -/
theorem derivSeries_jointContinuousOn_bdd
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceBddOn a W) (hcont_a : ∀ n, Continuous (fun s => a s n)) :
    ContinuousOn
      (Function.uncurry (fun (τ : ℝ) (x : ℝ) =>
        ∑' n, (a τ n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a τ n) * cosineMode n x))
      (Set.Ioo (0 : ℝ) W ×ˢ Set.univ) := by
  change ContinuousOn
    (fun p : ℝ × ℝ => ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a p.1 n) * cosineMode n p.2)
    (Set.Ioo 0 W ×ˢ Set.univ)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hτ₀mem, _⟩ := Set.mem_prod.mp hp
  have hτ₀ : 0 < p.1 := (Set.mem_Ioo.mp hτ₀mem).1
  have hτ₀W : p.1 < W := (Set.mem_Ioo.mp hτ₀mem).2
  set c₀ : ℝ := p.1 / 4 with hc₀def
  set lo : ℝ := p.1 / 2 with hlodef
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  have hloc₀ : lo = 2 * c₀ := by rw [hlodef, hc₀def]; ring
  have hloW : lo ≤ W := by rw [hlodef]; linarith
  -- uniform majorant
  have hg_sum : Summable (fun n => derivMajorant src c₀ M n) :=
    derivMajorant_summable src hc₀ (by rw [hc₀def]; linarith) M
  have hcont_on : ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, (a q.1 n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a q.1 n) * cosineMode n q.2)
      (Set.Ioo lo W ×ˢ Set.univ) := by
    apply continuousOn_tsum
    · intro n
      apply ContinuousOn.mul
      · have hc : Continuous (fun τ => a τ n - unitIntervalCosineEigenvalue n *
            localRestartCoeff a₀ a τ n) := by
          have he : Continuous (fun τ : ℝ => Real.exp (-τ * (λ_ n)) * a₀ n) :=
            ((Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
              continuous_const)
          have hd := duhamelSpectralCoeff_continuous n (hcont_a n)
          have hlc : Continuous (fun τ => localRestartCoeff a₀ a τ n) := by
            have heq : (fun τ => localRestartCoeff a₀ a τ n)
                = (fun τ => Real.exp (-τ * (λ_ n)) * a₀ n + duhamelSpectralCoeff a τ n) := by
              funext τ; simp only [localRestartCoeff]
            rw [heq]; exact he.add hd
          exact (hcont_a n).sub (continuous_const.mul hlc)
        exact (hc.comp continuous_fst).continuousOn
      · exact ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn)
    · exact hg_sum
    · intro n q hq
      obtain ⟨hτ, _⟩ := Set.mem_prod.mp hq
      have hqmem : q.1 ∈ Set.Ioo lo W := hτ
      exact deriv_term_abs_le src hM ha₀ hcont_a hc₀ hloc₀ hloW hqmem q.2 n
  have hmem : p ∈ Set.Ioo lo W ×ˢ (Set.univ : Set ℝ) :=
    ⟨Set.mem_Ioo.mpr ⟨by rw [hlodef]; linarith, hτ₀W⟩, Set.mem_univ _⟩
  have hopen : IsOpen (Set.Ioo lo W ×ˢ (Set.univ : Set ℝ)) :=
    IsOpen.prod isOpen_Ioo isOpen_univ
  exact hcont_on.continuousAt (hopen.mem_nhds hmem)

/-! ## E. The de-circularized local restart engine and the K1 producer. -/

/-- **Weak local restart bundle.**  Mirrors `LocalRestart` of
`IntervalPicardLimitK1.lean`, but the clamped source carries the BOUNDED package
`srcC : DuhamelSourceBddOn aC W` (constant bound + per-compact envelopes +
continuity — NO derivative fields) together with global time-continuity
`hcontC`.  `W` is the offset horizon, `d - τ ≤ W`. -/
structure LocalRestartWeak
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T σ : ℝ) where
  τ : ℝ
  d : ℝ
  W : ℝ
  hτpos : 0 < τ
  hστ : τ < σ
  hσd : σ < d
  hdT : d < T
  hdτW : d - τ ≤ W
  a₀ : ℕ → ℝ
  M : ℝ
  hM_nonneg : 0 ≤ M
  ha₀ : ∀ n, |a₀ n| ≤ M
  aC : ℝ → ℕ → ℝ
  srcC : DuhamelSourceBddOn aC W
  hcontC : ∀ n, Continuous (fun s => aC s n)
  hrep : ∀ r, r ∈ Set.Ioo τ d → ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
    intervalDomainLift (u r) x
      = ∑' n, localRestartCoeff a₀ aC (r - τ) n * cosineMode n x
  hpos : ∀ r, r ∈ Set.Ioo τ d → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift (u r) x
  hα : 1 ≤ p.α

open ShenWork.IntervalPicardLimitBddProducer (patchedSource patchedSource_eq_of_pos
  windowEnv windowEnv_summable)
open ShenWork.IntervalLogisticSourceQuantBound
  (B_log B_log_nonneg logisticSourceFun_cosineCoeff_quadratic_decay_explicit)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_zero_abs_le_of_bound logisticSourceFun_abs_le_of_bound)
open ShenWork.IntervalTimeSoftClamp (φ_mem_range φ_continuous φ_eq_id_on)

/-- **Single-slice window envelope bound for the logistic source coefficient**,
from WINDOWED ledger data only (the slice `s` is fixed inside `[a',b'] ⊂ (0,T)`).
Inlined single-slice core of `patchedSource_windowEnv_bound`. -/
theorem logisticSource_slice_windowEnv_bound
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {Msup : ℝ} {bc : ℝ → ℕ → ℝ} {s G1 G2 : ℝ}
    (hbsum_s : Summable (fun n => unitIntervalCosineEigenvalue n * |bc s n|))
    (hagree_s : Set.EqOn (intervalDomainLift (u s))
        (fun x => ∑' n, bc s n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u s) x)
    (hub_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u s) x ≤ Msup)
    (hG1_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u s)) x| ≤ G1)
    (hG2_s : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u s))) x| ≤ G2)
    (k : ℕ) :
    |cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s))) k|
      ≤ windowEnv (max (2 * B_log p.a p.b p.α Msup G1 G2)
          (Msup * (p.a + p.b * Msup ^ p.α))) k := by
  set cs : ℝ → ℝ := fun x => ∑' n, bc s n * cosineMode n x with hcs
  have hcsC2 : ContDiff ℝ 2 cs :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hbsum_s
  have hcs_d_cont : Continuous (deriv cs) := hcsC2.continuous_deriv (by norm_num)
  have hcs_dd_cont : Continuous (deriv (deriv cs)) := by
    have h2 : ContDiff ℝ (1 + 1) cs := by simpa using hcsC2
    exact ((contDiff_succ_iff_deriv.mp h2).2.2).continuous_deriv le_rfl
  have hpos_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < cs x := by
    intro x hx; rw [← hagree_s hx]; exact hpos_s x hx
  have hub_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, cs x ≤ Msup := by
    intro x hx; rw [← hagree_s hx]; exact hub_s x hx
  have hG1_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv cs x| ≤ G1 := by
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      hcs_d_cont.abs (fun x hx => ?_)
    have hloc : intervalDomainLift (u s) =ᶠ[nhds x] cs := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree_s (Set.Ioo_subset_Icc_self hy)
    rw [← hloc.deriv_eq]; exact hG1_s x (Set.Ioo_subset_Icc_self hx)
  have hG2_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv cs) x| ≤ G2 := by
    refine ShenWork.IntervalDomainLimitSourceRepresentation.le_on_Icc_of_le_on_Ioo
      hcs_dd_cont.abs (fun x hx => ?_)
    have hloc : intervalDomainLift (u s) =ᶠ[nhds x] cs := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree_s (Set.Ioo_subset_Icc_self hy)
    have hloc' : deriv (intervalDomainLift (u s)) =ᶠ[nhds x] deriv cs := hloc.deriv
    rw [← hloc'.deriv_eq]; exact hG2_s x (Set.Ioo_subset_Icc_self hx)
  have hN0_cs : deriv cs 0 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero hbsum_s
  have hN1_cs : deriv cs 1 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one hbsum_s
  have hG1nn : 0 ≤ G1 := le_trans (abs_nonneg _) (hG1_s 0 (by constructor <;> norm_num))
  have hG2nn : 0 ≤ G2 := le_trans (abs_nonneg _) (hG2_s 0 (by constructor <;> norm_num))
  have hMnn : 0 ≤ Msup := by
    have h1 := hub_s 0 (by constructor <;> norm_num)
    have h2 := hpos_s 0 (by constructor <;> norm_num); linarith
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  set C : ℝ := max (2 * B_log p.a p.b p.α Msup G1 G2) (Msup * (p.a + p.b * Msup ^ p.α))
    with hCdef
  have hBnn : 0 ≤ B_log p.a p.b p.α Msup G1 G2 := B_log_nonneg hα ha hb hMnn hG1nn hG2nn
  have hsrc_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)) x
        = logisticSourceFun p.a p.b p.α cs x := by
    intro x hx; simp only [logisticSourceFun]; rw [hagree_s hx]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [windowEnv]
    rw [cosineCoeffs_congr_on_Icc hsrc_eq 0]
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticSourceFun p.a p.b p.α cs x| ≤ Msup * (p.a + p.b * Msup ^ p.α) :=
      logisticSourceFun_abs_le_of_bound (B := Msup) hMnn hαpos ha hb
        (fun x hx => by rw [abs_of_pos (hpos_cs x hx)]; exact hub_cs x hx) hpos_cs
    have hgc : Continuous cs := hcsC2.continuous
    have hcont : ContinuousOn (logisticSourceFun p.a p.b p.α cs) (Set.Icc (0 : ℝ) 1) := by
      have hpos' : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → cs x ≠ 0 :=
        fun x hx => ne_of_gt (hpos_cs x hx)
      unfold logisticSourceFun
      apply ContinuousOn.mul hgc.continuousOn
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const hgc.continuousOn (fun x hx => Or.inl (hpos' x hx))
    have hMa_nn : 0 ≤ Msup * (p.a + p.b * Msup ^ p.α) := by positivity
    exact le_trans (cosineCoeffs_zero_abs_le_of_bound hMa_nn hcont hsup) (le_max_right _ _)
  · have hk1 : 1 ≤ k := hkpos
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    simp only [windowEnv, if_neg hkne]
    rw [cosineCoeffs_congr_on_Icc hsrc_eq k]
    refine le_trans
      (logisticSourceFun_cosineCoeff_quadratic_decay_explicit hcsC2 hα ha hb
        hpos_cs hub_cs hG1_cs hG2_cs hN0_cs hN1_cs k hk1) ?_
    gcongr
    exact le_max_left _ _

set_option maxHeartbeats 3200000 in
/-- **Construction of the weak local restart data** from the ledger-V2
satisfiable hypotheses ONLY (NO `adott₀/hderivt₀/hadotcontt₀/hMdott₀`).  The
clamped source's BOUNDED package and global continuity are produced from
`hsrc0`'s continuity (composed with the clamp) + the per-compact `windowEnv`
envelope extraction; the restart representation is built exactly as in
`localRestart_of_ledger`. -/
def localRestartWeak_of_ledger
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s)))
    {σ : ℝ} (hσ0 : 0 < σ) (hσT : σ < T) :
    LocalRestartWeak p u T σ := by
  set τ : ℝ := σ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτσ : τ < σ := by rw [hτdef]; linarith
  have hτT : τ < T := lt_trans hτσ hσT
  set c' : ℝ := σ / 4 with hc'def
  set d : ℝ := (σ + T) / 2 with hddef
  set d' : ℝ := (σ + 3 * T) / 4 with hd'def
  have hc' : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ d := by rw [hddef, hτdef]; linarith
  have hd' : d < d' := by rw [hddef, hd'def]; linarith
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hd'T : d' < T := by rw [hd'def]; linarith
  have hσd : σ < d := by rw [hddef]; linarith
  have hdT : d < T := lt_trans hd' hd'T
  have hwin : ∀ s ∈ Set.Icc c' d', 0 < s ∧ s < T := fun s hs =>
    ⟨lt_of_lt_of_le hc'pos hs.1, lt_of_le_of_lt hs.2 hd'T⟩
  set G1 := (hG1t c' d' hc'pos hd'T).choose with hG1def
  have hG1 := (hG1t c' d' hc'pos hd'T).choose_spec
  set G2 := (hG2t c' d' hc'pos hd'T).choose with hG2def
  have hG2 := (hG2t c' d' hc'pos hd'T).choose_spec
  -- restart-base bound (same as K1)
  have hMnn : 0 ≤ Msup := by
    have h1 := hubt τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    have h2 := hpost τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    linarith
  have ha₀ : ∀ k, |cosineCoeffs (intervalDomainLift (u τ)) k| ≤ 2 * Msup := by
    intro k
    refine ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) (by linarith) ?_ k
    intro x hx
    rw [abs_of_pos (hpost τ hτpos hτT x hx)]
    exact hubt τ hτpos hτT x hx
  -- The clamped family.
  set aC : ℝ → ℕ → ℝ := fun ρ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
    (intervalDomainLift (u (φ c' τ d d' (τ + ρ))))) k with haCdef
  -- window envelope constant.
  set Cval : ℝ := max (2 * B_log p.a p.b p.α Msup G1 G2)
    (Msup * (p.a + p.b * Msup ^ p.α)) with hCvaldef
  have hCval_nn : 0 ≤ Cval := by
    rw [hCvaldef]
    refine le_trans ?_ (le_max_right _ _)
    have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
    positivity
  -- envelope/bound on the clamp window via patchedSource_windowEnv_bound.
  have hΦmem : ∀ ρ : ℝ, φ c' τ d d' (τ + ρ) ∈ Set.Icc c' d' :=
    fun ρ => φ_mem_range hc' hcd hd' (τ + ρ)
  -- |aC ρ k| ≤ windowEnv Cval k for ALL ρ.
  have haC_env : ∀ ρ : ℝ, ∀ k, |aC ρ k| ≤ windowEnv Cval k := by
    intro ρ k
    set s := φ c' τ d d' (τ + ρ) with hsdef
    have hsmem := hΦmem ρ
    have hspos : 0 < s := (hwin s hsmem).1
    have hsT : s < T := (hwin s hsmem).2
    have hbound := logisticSource_slice_windowEnv_bound p u hα ha hb
      (bc := bc) (s := s) (G1 := G1) (G2 := G2)
      (hbsum s hspos hsT) (hagree s hspos hsT) (hpost s hspos hsT) (hubt s hspos hsT)
      (fun x hx => hG1 s hsmem x hx) (fun x hx => hG2 s hsmem x hx) k
    simpa only [haCdef, hsdef, hCvaldef] using hbound
  -- global continuity of the clamped family (from hsrc0.hcont ∘ clamp).
  have hΦcont : Continuous (fun s : ℝ => φ c' τ d d' (τ + s)) :=
    φ_continuous.comp (continuous_const.add continuous_id)
  have hcontC : ∀ n, Continuous (fun s => aC s n) := by
    intro n
    have hcanon : (fun s => aC s n)
        = (fun s => cosineCoeffs (logisticLifted p (u (φ c' τ d d' (τ + s)))) n) := by
      funext s
      exact (cosineCoeffs_congr_on_Icc
        (logisticLifted_eq_logisticSourceFun_on_Icc p (u (φ c' τ d d' (τ + s)))) n).symm
    rw [hcanon]
    have hmaps : Set.MapsTo (fun s : ℝ => φ c' τ d d' (τ + s)) Set.univ (Set.Icc 0 T) :=
      fun s _ => ⟨le_trans hc'pos.le (hΦmem s).1, le_of_lt (hwin _ (hΦmem s)).2⟩
    have := (hsrc0.hcont n).comp_continuous hΦcont (fun s => (hmaps (Set.mem_univ s)))
    exact this
  -- the bounded source package.
  have hWnn : (0:ℝ) ≤ d - τ := by linarith
  have hsrcC : DuhamelSourceBddOn aC (d - τ) :=
    { M := Cval
      hM_nonneg := hCval_nn
      hM := fun s _ _ k => le_trans (haC_env s k) (windowEnv_le_const hCval_nn k)
      hcont := fun k => (hcontC k).continuousOn
      env := fun _ => windowEnv Cval
      henv_summable := fun _ _ _ => windowEnv_summable
      henv_bound := fun _ _ s _ _ k => haC_env s k }
  refine
    { τ := τ, d := d, W := d - τ
      hτpos := hτpos, hστ := hτσ, hσd := hσd, hdT := hdT, hdτW := le_rfl
      a₀ := cosineCoeffs (intervalDomainLift (u τ)), M := 2 * Msup
      hM_nonneg := by linarith, ha₀ := ha₀
      aC := aC
      srcC := hsrcC
      hcontC := hcontC
      hpos := fun r hr x hx =>
        hpost r (lt_trans hτpos hr.1) (lt_trans hr.2 hdT) x hx
      hα := hα, hrep := ?_ }
  -- restart representation on Ioo τ d (identical to localRestart_of_ledger).
  intro r hr x hx
  have hτr : τ < r := hr.1
  have hrd : r < d := hr.2
  have hrT : r < T := lt_trans hrd hdT
  have hrpos : 0 < r := lt_trans hτpos hτr
  have heqon := picardLimitRestart_general p hχ0 u₀ u
    (fun s hs hsr => hfix s hs (lt_of_le_of_lt hsr hrT))
    hu₀_cont hu₀_bound hsrc0 hτpos hτr hrT.le
    (fun s hs hsr => hLc r hrpos hrT s hs hsr)
  rw [heqon hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  rw [restartDuhamelCoeff_eq_localRestartCoeff]
  unfold localRestartCoeff
  congr 1
  unfold duhamelSpectralCoeff
  apply intervalIntegral.integral_congr
  intro ρ hρ
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ r - τ)] at hρ
  have hmem_cd : τ + ρ ∈ Set.Icc τ d :=
    ⟨by linarith [hρ.1], by linarith [hρ.2, hrd.le]⟩
  simp only [haCdef]
  congr 1
  rw [clampedFamily_eq_on p u hc' hd' hmem_cd k]
  exact congrFun (congrFun (source_family_eq_w p u) (τ + ρ)) k

set_option maxHeartbeats 3200000 in
/-- **Subtype-continuity variant of `localRestartWeak_of_ledger`.**

Identical to `localRestartWeak_of_ledger` except the lift-continuity hypothesis
`hu₀_cont : Continuous (intervalDomainLift u₀)` (FALSE for positive boundary
data — the zero-extension lift jumps to 0 outside `[0,1]`) is replaced by the
subtype form `Continuous u₀`, and the slice-continuity hypothesis `hLc`
(`Continuous (logisticLifted p (u s))`, likewise false) is replaced by the
`constExtend` form `hLc_ce`.  The only consumer of those two hypotheses is the
restart representation `picardLimitRestart_general`, which we swap for
`picardLimitRestart_general_of_subtypeCont`.  Everything else (the BddOn package,
the window envelope, the integral congr) is independent of lift continuity. -/
def localRestartWeak_of_ledger_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    {σ : ℝ} (hσ0 : 0 < σ) (hσT : σ < T) :
    LocalRestartWeak p u T σ := by
  set τ : ℝ := σ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτσ : τ < σ := by rw [hτdef]; linarith
  have hτT : τ < T := lt_trans hτσ hσT
  set c' : ℝ := σ / 4 with hc'def
  set d : ℝ := (σ + T) / 2 with hddef
  set d' : ℝ := (σ + 3 * T) / 4 with hd'def
  have hc' : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ d := by rw [hddef, hτdef]; linarith
  have hd' : d < d' := by rw [hddef, hd'def]; linarith
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hd'T : d' < T := by rw [hd'def]; linarith
  have hσd : σ < d := by rw [hddef]; linarith
  have hdT : d < T := lt_trans hd' hd'T
  have hwin : ∀ s ∈ Set.Icc c' d', 0 < s ∧ s < T := fun s hs =>
    ⟨lt_of_lt_of_le hc'pos hs.1, lt_of_le_of_lt hs.2 hd'T⟩
  set G1 := (hG1t c' d' hc'pos hd'T).choose with hG1def
  have hG1 := (hG1t c' d' hc'pos hd'T).choose_spec
  set G2 := (hG2t c' d' hc'pos hd'T).choose with hG2def
  have hG2 := (hG2t c' d' hc'pos hd'T).choose_spec
  -- restart-base bound (same as K1)
  have hMnn : 0 ≤ Msup := by
    have h1 := hubt τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    have h2 := hpost τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
    linarith
  have ha₀ : ∀ k, |cosineCoeffs (intervalDomainLift (u τ)) k| ≤ 2 * Msup := by
    intro k
    refine ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) (by linarith) ?_ k
    intro x hx
    rw [abs_of_pos (hpost τ hτpos hτT x hx)]
    exact hubt τ hτpos hτT x hx
  -- The clamped family.
  set aC : ℝ → ℕ → ℝ := fun ρ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
    (intervalDomainLift (u (φ c' τ d d' (τ + ρ))))) k with haCdef
  -- window envelope constant.
  set Cval : ℝ := max (2 * B_log p.a p.b p.α Msup G1 G2)
    (Msup * (p.a + p.b * Msup ^ p.α)) with hCvaldef
  have hCval_nn : 0 ≤ Cval := by
    rw [hCvaldef]
    refine le_trans ?_ (le_max_right _ _)
    have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
    positivity
  -- envelope/bound on the clamp window via patchedSource_windowEnv_bound.
  have hΦmem : ∀ ρ : ℝ, φ c' τ d d' (τ + ρ) ∈ Set.Icc c' d' :=
    fun ρ => φ_mem_range hc' hcd hd' (τ + ρ)
  -- |aC ρ k| ≤ windowEnv Cval k for ALL ρ.
  have haC_env : ∀ ρ : ℝ, ∀ k, |aC ρ k| ≤ windowEnv Cval k := by
    intro ρ k
    set s := φ c' τ d d' (τ + ρ) with hsdef
    have hsmem := hΦmem ρ
    have hspos : 0 < s := (hwin s hsmem).1
    have hsT : s < T := (hwin s hsmem).2
    have hbound := logisticSource_slice_windowEnv_bound p u hα ha hb
      (bc := bc) (s := s) (G1 := G1) (G2 := G2)
      (hbsum s hspos hsT) (hagree s hspos hsT) (hpost s hspos hsT) (hubt s hspos hsT)
      (fun x hx => hG1 s hsmem x hx) (fun x hx => hG2 s hsmem x hx) k
    simpa only [haCdef, hsdef, hCvaldef] using hbound
  -- global continuity of the clamped family (from hsrc0.hcont ∘ clamp).
  have hΦcont : Continuous (fun s : ℝ => φ c' τ d d' (τ + s)) :=
    φ_continuous.comp (continuous_const.add continuous_id)
  have hcontC : ∀ n, Continuous (fun s => aC s n) := by
    intro n
    have hcanon : (fun s => aC s n)
        = (fun s => cosineCoeffs (logisticLifted p (u (φ c' τ d d' (τ + s)))) n) := by
      funext s
      exact (cosineCoeffs_congr_on_Icc
        (logisticLifted_eq_logisticSourceFun_on_Icc p (u (φ c' τ d d' (τ + s)))) n).symm
    rw [hcanon]
    -- bridge patched → canonical: the clamp lands in [c',d'] ⊂ (0,T), where
    -- patchedSource = canonical, so the canonical mode equals the patched one.
    have hpatch : (fun s => cosineCoeffs (logisticLifted p (u (φ c' τ d d' (τ + s)))) n)
        = (fun s => patchedSource p u₀ u (φ c' τ d d' (τ + s)) n) := by
      funext s
      exact (patchedSource_eq_of_pos p u₀ u (hwin _ (hΦmem s)).1 n).symm
    rw [hpatch]
    have hmaps : Set.MapsTo (fun s : ℝ => φ c' τ d d' (τ + s)) Set.univ (Set.Icc 0 T) :=
      fun s _ => ⟨le_trans hc'pos.le (hΦmem s).1, le_of_lt (hwin _ (hΦmem s)).2⟩
    have := (hsrc0.hcont n).comp_continuous hΦcont (fun s => (hmaps (Set.mem_univ s)))
    exact this
  -- the bounded source package.
  have hWnn : (0:ℝ) ≤ d - τ := by linarith
  have hsrcC : DuhamelSourceBddOn aC (d - τ) :=
    { M := Cval
      hM_nonneg := hCval_nn
      hM := fun s _ _ k => le_trans (haC_env s k) (windowEnv_le_const hCval_nn k)
      hcont := fun k => (hcontC k).continuousOn
      env := fun _ => windowEnv Cval
      henv_summable := fun _ _ _ => windowEnv_summable
      henv_bound := fun _ _ s _ _ k => haC_env s k }
  refine
    { τ := τ, d := d, W := d - τ
      hτpos := hτpos, hστ := hτσ, hσd := hσd, hdT := hdT, hdτW := le_rfl
      a₀ := cosineCoeffs (intervalDomainLift (u τ)), M := 2 * Msup
      hM_nonneg := by linarith, ha₀ := ha₀
      aC := aC
      srcC := hsrcC
      hcontC := hcontC
      hpos := fun r hr x hx =>
        hpost r (lt_trans hτpos hr.1) (lt_trans hr.2 hdT) x hx
      hα := hα, hrep := ?_ }
  -- restart representation on Ioo τ d (subtype-continuity variant).
  intro r hr x hx
  have hτr : τ < r := hr.1
  have hrd : r < d := hr.2
  have hrT : r < T := lt_trans hrd hdT
  have hrpos : 0 < r := lt_trans hτpos hτr
  have heqon := picardLimitRestart_general_of_subtypeCont p hχ0 u₀ u
    (fun s hs hsr => hfix s hs (lt_of_le_of_lt hsr hrT))
    hu₀_cont hu₀_bound hsrc0 hτpos hτr hrT.le
    (fun s hs hsr => hLc_ce r hrpos hrT s hs hsr)
  rw [heqon hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  rw [restartDuhamelCoeff_eq_localRestartCoeff]
  unfold localRestartCoeff
  congr 1
  unfold duhamelSpectralCoeff
  apply intervalIntegral.integral_congr
  intro ρ hρ
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ r - τ)] at hρ
  have hmem_cd : τ + ρ ∈ Set.Icc τ d :=
    ⟨by linarith [hρ.1], by linarith [hρ.2, hrd.le]⟩
  simp only [haCdef]
  congr 1
  rw [clampedFamily_eq_on p u hc' hd' hmem_cd k]
  exact congrFun (congrFun (source_family_eq_w p u) (τ + ρ)) k

namespace LocalRestartWeak

open ShenWork.Paper2.PicardLimitK1 (slopeSlice sourceDerivSlice adottOf)

variable {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
  (L : LocalRestartWeak p u T σ)

/-- The restart time-derivative series at offset `ρ`. -/
def vSeries (ρ x : ℝ) : ℝ :=
  ∑' n, (L.aC ρ n - unitIntervalCosineEigenvalue n *
    localRestartCoeff L.a₀ L.aC ρ n) * cosineMode n x

/-- The restart value series at offset `ρ`. -/
def valueSeries (ρ x : ℝ) : ℝ :=
  ∑' n, localRestartCoeff L.a₀ L.aC ρ n * cosineMode n x

theorem hσ_mem : σ ∈ Set.Ioo L.τ L.d := ⟨L.hστ, L.hσd⟩

/-- σ − τ < W, so the HasDerivAt evaluation point sits inside the window. -/
theorem hστ_lt_W : σ - L.τ < L.W := by
  have := L.hσd; have := L.hdτW; linarith

/-- **Lemma 2+3 (weak): time derivative of the solution slice.** -/
theorem hasDerivAt_slice {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => intervalDomainLift (u s) x) (L.vSeries (r - L.τ) x) r := by
  have hrτ : 0 < r - L.τ := by have := hr.1; linarith
  have hrW : r - L.τ < L.W := by have := hr.2; have := L.hdτW; linarith
  have hspec := restartCosineSeries_hasDerivAt_time_bdd L.ha₀ L.srcC L.hcontC hrτ hrW x
  have hshift : HasDerivAt (fun s : ℝ => s - L.τ) 1 r :=
    (hasDerivAt_id r).sub_const L.τ
  have hcomp := hspec.comp r hshift
  simp only [mul_one] at hcomp
  have hev : (fun s => intervalDomainLift (u s) x) =ᶠ[𝓝 r]
      (fun s => ∑' n, localRestartCoeff L.a₀ L.aC (s - L.τ) n * cosineMode n x) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => ?_)
    exact L.hrep s hs x hx
  exact (hcomp.congr_of_eventuallyEq hev).congr_deriv rfl

theorem slopeSlice_eq {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    slopeSlice u r x = L.vSeries (r - L.τ) x :=
  (L.hasDerivAt_slice hr hx).deriv

theorem lift_eq_valueSeries {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (u r) x = L.valueSeries (r - L.τ) x :=
  L.hrep r hr x hx

/-- Maps the time-slab (shifted) into `Ioo 0 W ×ˢ univ`. -/
theorem vSeries_jointContinuousOn :
    ContinuousOn (Function.uncurry (fun ρ x => L.vSeries ρ x))
      (Set.Ioo (0 : ℝ) L.W ×ˢ Set.univ) :=
  derivSeries_jointContinuousOn_bdd L.hM_nonneg L.ha₀ L.srcC L.hcontC

theorem valueSeries_jointContinuousOn :
    ContinuousOn (Function.uncurry (fun ρ x => L.valueSeries ρ x))
      (Set.Ioo (0 : ℝ) L.W ×ˢ Set.univ) :=
  valueSeries_jointContinuousOn_bdd L.hM_nonneg L.ha₀ L.srcC L.hcontC

/-- The shift map sends the time-slab `Icc a' b' ⊆ Ioo τ d` into `Ioo 0 W` (offsets). -/
theorem shift_mapsTo {a' b' : ℝ} (hsub : Set.Icc a' b' ⊆ Set.Ioo L.τ L.d) :
    Set.MapsTo (fun q : ℝ × ℝ => ((q.1 - L.τ, q.2) : ℝ × ℝ))
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) (Set.Ioo (0:ℝ) L.W ×ˢ Set.univ) := by
  intro q hq
  obtain ⟨hq1, _⟩ := Set.mem_prod.mp hq
  have hr : q.1 ∈ Set.Ioo L.τ L.d := hsub hq1
  refine Set.mem_prod.mpr ⟨Set.mem_Ioo.mpr ⟨?_, ?_⟩, Set.mem_univ _⟩
  · have := hr.1; linarith
  · have := hr.2; have := L.hdτW; linarith

theorem sourceDerivSlice_eq_series {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    sourceDerivSlice p u r x
      = L.vSeries (r - L.τ) x *
        (p.a - p.b * (1 + p.α) * (L.valueSeries (r - L.τ) x) ^ p.α) := by
  unfold sourceDerivSlice
  rw [L.slopeSlice_eq hr hx, L.lift_eq_valueSeries hr hx]

theorem sourceDerivSlice_continuousOn_slab {a' b' : ℝ}
    (hsub : Set.Icc a' b' ⊆ Set.Ioo L.τ L.d) :
    ContinuousOn (Function.uncurry (fun s x => sourceDerivSlice p u s x))
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) := by
  set Φ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 - L.τ, q.2) with hΦ
  have hΦcont : Continuous Φ := (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hmaps := L.shift_mapsTo hsub
  have hvS : ContinuousOn (fun q : ℝ × ℝ => L.vSeries (q.1 - L.τ) q.2)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    (L.vSeries_jointContinuousOn.comp hΦcont.continuousOn hmaps)
  have hwS : ContinuousOn (fun q : ℝ × ℝ => L.valueSeries (q.1 - L.τ) q.2)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    (L.valueSeries_jointContinuousOn.comp hΦcont.continuousOn hmaps)
  have hposS : ∀ q ∈ Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1,
      0 < L.valueSeries (q.1 - L.τ) q.2 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    rw [← L.lift_eq_valueSeries (hsub hq1) hq2]
    exact L.hpos q.1 (hsub hq1) q.2 hq2
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => (L.valueSeries (q.1 - L.τ) q.2) ^ p.α)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.rpow_const hwS
    intro q hq; exact Or.inl (ne_of_gt (hposS q hq))
  have hprod : ContinuousOn
      (fun q : ℝ × ℝ => L.vSeries (q.1 - L.τ) q.2 *
        (p.a - p.b * (1 + p.α) * (L.valueSeries (q.1 - L.τ) q.2) ^ p.α))
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    hvS.mul ((continuousOn_const).sub ((continuousOn_const).mul hpow))
  apply hprod.congr
  intro q hq
  obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
  simp only [Function.uncurry]
  exact L.sourceDerivSlice_eq_series (hsub hq1) hq2

theorem logisticSlice_continuousOn {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d) :
    ContinuousOn (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r)))
      (Set.Icc (0:ℝ) 1) := by
  have hrτ : 0 < r - L.τ := by have := hr.1; linarith
  have hrW : r - L.τ < L.W := by have := hr.2; have := L.hdτW; linarith
  have hsec : ContinuousOn (fun x => L.valueSeries (r - L.τ) x) (Set.Icc (0:ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((r - L.τ, x) : ℝ × ℝ))
        (Set.Icc (0:ℝ) 1) (Set.Ioo (0:ℝ) L.W ×ˢ Set.univ) :=
      fun x _ => Set.mem_prod.mpr ⟨Set.mem_Ioo.mpr ⟨hrτ, hrW⟩, Set.mem_univ _⟩
    exact L.valueSeries_jointContinuousOn.comp
      (continuousOn_const.prodMk continuousOn_id) hmaps
  have hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < L.valueSeries (r - L.τ) x := by
    intro x hx; rw [← L.lift_eq_valueSeries hr hx]; exact L.hpos r hr x hx
  have hpow : ContinuousOn (fun x => (L.valueSeries (r - L.τ) x) ^ p.α)
      (Set.Icc (0:ℝ) 1) :=
    hsec.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hbody : ContinuousOn (fun x => L.valueSeries (r - L.τ) x *
      (p.a - p.b * (L.valueSeries (r - L.τ) x) ^ p.α)) (Set.Icc (0:ℝ) 1) :=
    hsec.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
  apply hbody.congr
  intro x hx
  unfold logisticSourceFun
  rw [L.lift_eq_valueSeries hr hx]

theorem hasDerivAt_logisticSlice {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)) x)
      (sourceDerivSlice p u r x) r := by
  have hslice := L.hasDerivAt_slice hr hx
  have hpos := L.hpos r hr x hx
  have hα0 : 0 < p.α := lt_of_lt_of_le zero_lt_one L.hα
  have hchain := ShenWork.IntervalMildPicardRegularity.logisticSourceFun_hasDerivAt_time
    (a := p.a) (b := p.b) (α := p.α)
    (f := fun s => intervalDomainLift (u s) x) (σ := r) hα0 hpos hslice
  unfold logisticSourceFun sourceDerivSlice slopeSlice
  rw [(L.hasDerivAt_slice hr hx).deriv]
  exact hchain

include L in
/-- **Lemma 4 (weak) = K1(i).** -/
theorem hasDerivAt_sourceCoeff (k : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adottOf p u σ k) σ := by
  set δ : ℝ := min (σ - L.τ) (L.d - σ) / 2 with hδdef
  have hδ1 : 0 < σ - L.τ := by have := L.hστ; linarith
  have hδ2 : 0 < L.d - σ := by have := L.hσd; linarith
  have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
  have hδle1 : δ ≤ (σ - L.τ) / 2 := by
    rw [hδdef]; have := min_le_left (σ - L.τ) (L.d - σ); linarith
  have hδle2 : δ ≤ (L.d - σ) / 2 := by
    rw [hδdef]; have := min_le_right (σ - L.τ) (L.d - σ); linarith
  have hball : Metric.ball σ δ ⊆ Set.Ioo L.τ L.d := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
  have hslab : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioo L.τ L.d := by
    intro s hs
    exact ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
  have hf_cont : ∀ᶠ s in 𝓝 σ,
      ContinuousOn (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)))
        (Set.Icc (0:ℝ) 1) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds L.hσ_mem) (fun s hs => ?_)
    exact L.logisticSlice_continuousOn hs
  have hf_int : ∀ᶠ s in 𝓝 σ, IntervalIntegrable
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (u s)))
      MeasureTheory.volume (0:ℝ) 1 := by
    filter_upwards [hf_cont] with s hs
    rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hs.intervalIntegrable
  have h_diff : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => logisticSourceFun p.a p.b p.α (intervalDomainLift (u r)) x)
        (sourceDerivSlice p u s x) s := by
    intro x hx s hs
    exact L.hasDerivAt_logisticSlice (hball hs) (Set.Ioo_subset_Icc_self hx)
  have h_cont_deriv : ContinuousOn (Function.uncurry (sourceDerivSlice p u))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0:ℝ) 1) :=
    L.sourceDerivSlice_continuousOn_slab hslab
  have hmain := ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
    (f := fun r => logisticSourceFun p.a p.b p.α (intervalDomainLift (u r)))
    (f' := sourceDerivSlice p u) (τ := σ) (n := k)
    hδ hf_int h_diff h_cont_deriv
  exact hmain

end LocalRestartWeak

/-! ## F. The de-circularized K1 producer. -/

open ShenWork.Paper2.PicardLimitK1 (sourceDerivSlice adottOf)
open LocalRestartWeak

set_option maxHeartbeats 1600000 in
set_option linter.style.maxHeartbeats false in
/-- **The K1 producer (de-circularized).**  Same conclusion as
`IntervalPicardLimitK1.k1_quadruple`, but the hypothesis set is ONLY the
ledger-V2 satisfiable data — NO `adott₀/hderivt₀/hadotcontt₀/hMdott₀`.  The
restart engine is driven by the BOUNDED package built from `hsrc0` + per-compact
K2 alone. -/
theorem k1_quadruple_weak
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))) :
    (∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
        (fun r => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
        (adottOf p u σ k) σ)
      ∧ (∀ k, ContinuousOn (fun σ => adottOf p u σ k) (Set.Ioo 0 T))
      ∧ (∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
          ∀ k, |adottOf p u σ k| ≤ Mdot) := by
  have mkL : ∀ σ, 0 < σ → σ < T → LocalRestartWeak p u T σ := fun σ hσ0 hσT =>
    localRestartWeak_of_ledger hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc
      hbsum hagree hpost hubt hG1t hG2t hLc hσ0 hσT
  have hderiv : ∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adottOf p u σ k) σ :=
    fun σ hσ0 hσT k => (mkL σ hσ0 hσT).hasDerivAt_sourceCoeff k
  -- Global joint continuity of the chain-rule slice on Ioo 0 T ×ˢ Icc 0 1.
  have hslice_cont : ContinuousOn (Function.uncurry (sourceDerivSlice p u))
      (Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    set σ₀ := q.1 with hσ₀
    have hσ₀0 : 0 < σ₀ := hq1.1
    have hσ₀T : σ₀ < T := hq1.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    have hslab_sub : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hslabcont := L.sourceDerivSlice_continuousOn_slab hslab_sub
    have hmem : q ∈ Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, hq2⟩
    have hnhds : Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1
        ∈ 𝓝[Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1] q := by
      have hopen : Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 q := by
        apply (isOpen_Ioo.prod isOpen_univ).mem_nhds
        exact Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
      have hinter := Filter.inter_mem (Filter.mem_inf_of_left hopen)
        (self_mem_nhdsWithin (a := q) (s := Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1))
      refine Filter.mem_of_superset hinter ?_
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      exact Set.mem_prod.mpr ⟨⟨(Set.mem_prod.mp hy1).1.1.le,
        (Set.mem_prod.mp hy1).1.2.le⟩, (Set.mem_prod.mp hy2).2⟩
    exact (hslabcont.continuousWithinAt hmem).mono_of_mem_nhdsWithin hnhds
  have hcont : ∀ k, ContinuousOn (fun σ => adottOf p u σ k) (Set.Ioo 0 T) := by
    intro k σ₀ hσ₀
    have hσ₀0 : 0 < σ₀ := hσ₀.1
    have hσ₀T : σ₀ < T := hσ₀.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    set I : Set ℝ := Set.Icc (σ₀ - δ) (σ₀ + δ) with hIdef
    have hIsub : I ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hσ₀mem : σ₀ ∈ I := ⟨by linarith, by linarith⟩
    have hslabcont := L.sourceDerivSlice_continuousOn_slab hIsub
    set F : ℝ → ℝ → ℝ := fun σ x =>
      Real.cos ((k : ℝ) * Real.pi * x) * sourceDerivSlice p u σ x with hFdef
    have hcos_cont : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id')
    have hFcont : ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0:ℝ) 1) :=
      (hcos_cont.comp continuous_snd).continuousOn.mul hslabcont
    have hKcompact : IsCompact (I ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image hFcont.norm)
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hFbd : ∀ σ ∈ I, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖F σ x‖ ≤ B' := by
      intro σ hσ x hx
      have : ‖Function.uncurry F (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hσ, hx⟩))
      exact le_trans this (le_max_left _ _)
    have hsec_cont : ∀ σ ∈ I, ContinuousOn (F σ) (Set.Icc (0:ℝ) 1) := by
      intro σ hσ
      have hsslice : ContinuousOn (sourceDerivSlice p u σ) (Set.Icc (0:ℝ) 1) :=
        hslabcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
      exact (hcos_cont.continuousOn).mul hsslice
    have hInhds : I ∈ 𝓝 σ₀ := by
      have : Set.Ioo (σ₀ - δ) (σ₀ + δ) ⊆ I := fun y hy => ⟨hy.1.le, hy.2.le⟩
      exact Filter.mem_of_superset
        (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) this
    have hint_cont : ContinuousAt (fun σ => ∫ x in (0:ℝ)..1, F σ x) σ₀ := by
      refine intervalIntegral.continuousAt_of_dominated_interval
        (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
      · filter_upwards [hInhds] with σ hσ
        have : ContinuousOn (F σ) (Set.uIcc (0:ℝ) 1) := by
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hsec_cont σ hσ
        exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
      · filter_upwards [hInhds] with σ hσ
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        exact hFbd σ hσ x ⟨hx.1.le, hx.2⟩
      · refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
        have hpt : (σ₀, x) ∈ I ×ˢ Set.Icc (0:ℝ) 1 :=
          Set.mem_prod.mpr ⟨hσ₀mem, hxIcc⟩
        have hcwa : ContinuousWithinAt (fun σ => F σ x) I σ₀ := by
          have := (hFcont.comp (continuousOn_id.prodMk continuousOn_const)
            (fun σ hσ => Set.mem_prod.mpr ⟨hσ, hxIcc⟩)).continuousWithinAt hσ₀mem
          simpa [Function.uncurry] using this
        exact hcwa.continuousAt hInhds
    have hadeq : ∀ σ, adottOf p u σ k =
        (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x := by
      intro σ; unfold adottOf; rw [cosineCoeffs_eq_factor_mul_integral]
    have hcont_at : ContinuousAt (fun σ => adottOf p u σ k) σ₀ := by
      have hfun : (fun σ => adottOf p u σ k)
          = (fun σ => (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x) :=
        funext hadeq
      rw [hfun]
      exact hint_cont.const_mul _
    exact hcont_at.continuousWithinAt
  have hbound : ∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adottOf p u σ k| ≤ Mdot := by
    intro a' b' ha' hb'
    set K := Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1 with hKdef
    have hKsub : K ⊆ Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
      exact Set.mem_prod.mpr ⟨⟨lt_of_lt_of_le ha' hq1.1, lt_of_le_of_lt hq1.2 hb'⟩, hq2⟩
    have hKcompact : IsCompact K := (isCompact_Icc).prod (isCompact_Icc)
    have hcontK : ContinuousOn (Function.uncurry (sourceDerivSlice p u)) K :=
      hslice_cont.mono hKsub
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image (hcontK.norm)).imp (fun B hB => hB)
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hbd : ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
        |sourceDerivSlice p u σ x| ≤ B' := by
      intro σ hσ x hx
      have hmem : (σ, x) ∈ K := Set.mem_prod.mpr ⟨hσ, hx⟩
      have : ‖Function.uncurry (sourceDerivSlice p u) (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ hmem)
      simp only [Function.uncurry, Real.norm_eq_abs] at this
      exact le_trans this (le_max_left _ _)
    refine ⟨2 * B', fun σ hσ k => ?_⟩
    have hsec : ContinuousOn (sourceDerivSlice p u σ) (Set.Icc (0:ℝ) 1) := by
      have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
          (Set.Icc (0:ℝ) 1) K :=
        fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩
      exact hcontK.comp (continuousOn_const.prodMk continuousOn_id) hmaps
    exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
      (fun x hx => hbd σ hσ x hx) k
  exact ⟨hderiv, hcont, hbound⟩

set_option maxHeartbeats 1600000 in
set_option linter.style.maxHeartbeats false in
/-- **Subtype-continuity variant of `k1_quadruple_weak`.**  Same conclusion, but
the lift-continuity hypothesis `hu₀_cont : Continuous (intervalDomainLift u₀)`
(FALSE for positive boundary data) is replaced by the subtype form
`Continuous u₀`, and the slice-continuity hypothesis `hLc`
(`Continuous (logisticLifted p (u s))`) by the `constExtend` form `hLc_ce`.  The
only change in the proof is driving the restart engine via
`localRestartWeak_of_ledger_of_subtypeCont`. -/
theorem k1_quadruple_weak_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))) :
    (∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
        (fun r => cosineCoeffs
          (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
        (adottOf p u σ k) σ)
      ∧ (∀ k, ContinuousOn (fun σ => adottOf p u σ k) (Set.Ioo 0 T))
      ∧ (∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
          ∀ k, |adottOf p u σ k| ≤ Mdot) := by
  have mkL : ∀ σ, 0 < σ → σ < T → LocalRestartWeak p u T σ := fun σ hσ0 hσT =>
    localRestartWeak_of_ledger_of_subtypeCont hχ0 u hα ha hb hu₀_cont hu₀_bound hfix
      hsrc0 bc hbsum hagree hpost hubt hG1t hG2t hLc_ce hσ0 hσT
  have hderiv : ∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adottOf p u σ k) σ :=
    fun σ hσ0 hσT k => (mkL σ hσ0 hσT).hasDerivAt_sourceCoeff k
  have hslice_cont : ContinuousOn (Function.uncurry (sourceDerivSlice p u))
      (Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    set σ₀ := q.1 with hσ₀
    have hσ₀0 : 0 < σ₀ := hq1.1
    have hσ₀T : σ₀ < T := hq1.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    have hslab_sub : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hslabcont := L.sourceDerivSlice_continuousOn_slab hslab_sub
    have hmem : q ∈ Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, hq2⟩
    have hnhds : Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1
        ∈ 𝓝[Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1] q := by
      have hopen : Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 q := by
        apply (isOpen_Ioo.prod isOpen_univ).mem_nhds
        exact Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
      have hinter := Filter.inter_mem (Filter.mem_inf_of_left hopen)
        (self_mem_nhdsWithin (a := q) (s := Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1))
      refine Filter.mem_of_superset hinter ?_
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      exact Set.mem_prod.mpr ⟨⟨(Set.mem_prod.mp hy1).1.1.le,
        (Set.mem_prod.mp hy1).1.2.le⟩, (Set.mem_prod.mp hy2).2⟩
    exact (hslabcont.continuousWithinAt hmem).mono_of_mem_nhdsWithin hnhds
  have hcont : ∀ k, ContinuousOn (fun σ => adottOf p u σ k) (Set.Ioo 0 T) := by
    intro k σ₀ hσ₀
    have hσ₀0 : 0 < σ₀ := hσ₀.1
    have hσ₀T : σ₀ < T := hσ₀.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    set I : Set ℝ := Set.Icc (σ₀ - δ) (σ₀ + δ) with hIdef
    have hIsub : I ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hσ₀mem : σ₀ ∈ I := ⟨by linarith, by linarith⟩
    have hslabcont := L.sourceDerivSlice_continuousOn_slab hIsub
    set F : ℝ → ℝ → ℝ := fun σ x =>
      Real.cos ((k : ℝ) * Real.pi * x) * sourceDerivSlice p u σ x with hFdef
    have hcos_cont : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id')
    have hFcont : ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0:ℝ) 1) :=
      (hcos_cont.comp continuous_snd).continuousOn.mul hslabcont
    have hKcompact : IsCompact (I ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image hFcont.norm)
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hFbd : ∀ σ ∈ I, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖F σ x‖ ≤ B' := by
      intro σ hσ x hx
      have : ‖Function.uncurry F (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hσ, hx⟩))
      exact le_trans this (le_max_left _ _)
    have hsec_cont : ∀ σ ∈ I, ContinuousOn (F σ) (Set.Icc (0:ℝ) 1) := by
      intro σ hσ
      have hsslice : ContinuousOn (sourceDerivSlice p u σ) (Set.Icc (0:ℝ) 1) :=
        hslabcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
      exact (hcos_cont.continuousOn).mul hsslice
    have hInhds : I ∈ 𝓝 σ₀ := by
      have : Set.Ioo (σ₀ - δ) (σ₀ + δ) ⊆ I := fun y hy => ⟨hy.1.le, hy.2.le⟩
      exact Filter.mem_of_superset
        (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) this
    have hint_cont : ContinuousAt (fun σ => ∫ x in (0:ℝ)..1, F σ x) σ₀ := by
      refine intervalIntegral.continuousAt_of_dominated_interval
        (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
      · filter_upwards [hInhds] with σ hσ
        have : ContinuousOn (F σ) (Set.uIcc (0:ℝ) 1) := by
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hsec_cont σ hσ
        exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
      · filter_upwards [hInhds] with σ hσ
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        exact hFbd σ hσ x ⟨hx.1.le, hx.2⟩
      · refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
        have hpt : (σ₀, x) ∈ I ×ˢ Set.Icc (0:ℝ) 1 :=
          Set.mem_prod.mpr ⟨hσ₀mem, hxIcc⟩
        have hcwa : ContinuousWithinAt (fun σ => F σ x) I σ₀ := by
          have := (hFcont.comp (continuousOn_id.prodMk continuousOn_const)
            (fun σ hσ => Set.mem_prod.mpr ⟨hσ, hxIcc⟩)).continuousWithinAt hσ₀mem
          simpa [Function.uncurry] using this
        exact hcwa.continuousAt hInhds
    have hadeq : ∀ σ, adottOf p u σ k =
        (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x := by
      intro σ; unfold adottOf; rw [cosineCoeffs_eq_factor_mul_integral]
    have hcont_at : ContinuousAt (fun σ => adottOf p u σ k) σ₀ := by
      have hfun : (fun σ => adottOf p u σ k)
          = (fun σ => (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x) :=
        funext hadeq
      rw [hfun]
      exact hint_cont.const_mul _
    exact hcont_at.continuousWithinAt
  have hbound : ∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adottOf p u σ k| ≤ Mdot := by
    intro a' b' ha' hb'
    set K := Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1 with hKdef
    have hKsub : K ⊆ Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
      exact Set.mem_prod.mpr ⟨⟨lt_of_lt_of_le ha' hq1.1, lt_of_le_of_lt hq1.2 hb'⟩, hq2⟩
    have hKcompact : IsCompact K := (isCompact_Icc).prod (isCompact_Icc)
    have hcontK : ContinuousOn (Function.uncurry (sourceDerivSlice p u)) K :=
      hslice_cont.mono hKsub
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image (hcontK.norm)).imp (fun B hB => hB)
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hbd : ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
        |sourceDerivSlice p u σ x| ≤ B' := by
      intro σ hσ x hx
      have hmem : (σ, x) ∈ K := Set.mem_prod.mpr ⟨hσ, hx⟩
      have : ‖Function.uncurry (sourceDerivSlice p u) (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ hmem)
      simp only [Function.uncurry, Real.norm_eq_abs] at this
      exact le_trans this (le_max_left _ _)
    refine ⟨2 * B', fun σ hσ k => ?_⟩
    have hsec : ContinuousOn (sourceDerivSlice p u σ) (Set.Icc (0:ℝ) 1) := by
      have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
          (Set.Icc (0:ℝ) 1) K :=
        fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩
      exact hcontK.comp (continuousOn_const.prodMk continuousOn_id) hmaps
    exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
      (fun x hx => hbd σ hσ x hx) k
  exact ⟨hderiv, hcont, hbound⟩

end ShenWork.Paper2.PicardLimitK1Weak
