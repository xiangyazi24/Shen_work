/-
  ShenWork/Paper2/IntervalPicardLimitRestartBdd.lean

  **Bounded-source weak chain: the satisfiable envelope shape.**

  ## Why (the finding)

  `DuhamelSourceL1ContOn a T` demands a SUMMABLE envelope dominating
  `|a s k|` for ALL `s ∈ [0, T]`.  For the canonical limit-source family with
  merely-continuous `u₀` (all a `PositiveInitialDatum` provides), as `s → 0⁺`
  the family tends to `cosineCoeffs (logistic (lift u₀))` — and a merely
  continuous function's cosine coefficients need not be `ℓ¹`.  So NO summable
  envelope exists near `s = 0`: the L1ContOn package is unfillable for the
  Provider one layer deeper than the (already fixed) global quantifiers.

  ## The fix (consumer audit)

  Almost every consumer of the envelope only needs a K-UNIFORM bound `M` plus
  the parabolic gain `λₖ ∫₀ᵗ e^{−(t−s)λₖ} ds ≤ 1`:

  * the `∑∫ = ∫∑` swap (`duhamelValue_adot_eq_tsum_on`) takes a constant
    bound `Mdot` already;
  * plain `ℓ¹` summability of the Duhamel coefficients follows from
    `λₖ·|duh| ≤ M` (FTC estimate with the constant bound) ⟹ `|duh| ≤ M/λₖ`,
    summable by `∑ 1/k²`.

  The ONLY consumer genuinely needing a decaying envelope is the
  eigenvalue-WEIGHTED summability (`hbsum` producer), and there the time split
  `∫₀ᵗ = ∫₀^{t/2} + ∫_{t/2}^t` (already proven:
  `duhamelSpectralCoeff_general_split_on`) reduces it to
  * the head: `λₖ e^{−(t/2)λₖ}·(t/2)M` — parabolic series, summable;
  * the tail: the shifted family reads `s ∈ [t/2, t] ⋐ (0, T)` where a
    PER-COMPACT decaying envelope exists (quadratic decay from the per-compact
    K2 bounds of ledger V2).

  Hence the satisfiable package `DuhamelSourceBddOn`: constant `M` on `[0, τ]`
  + continuity on `[0, τ]` + per-compact summable envelopes on `[a', τ]`,
  `a' > 0`.  This file proves the weak-chain entry points against it.

  Design: HANDOFF/hsrc0-splitenv-design.md (+ ChatGPT cron consult 2026-06-09).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestartWeak

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupComposition
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff duhamelValue_adot_eq_tsum_on)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalPicardIterateRestart
  (heatValue_eq_cosineSeries cosineCoeffs_of_l1_cosineSeries
    intervalGradientDuhamelMap_eq_of_chi0_zero)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn duhamelSpectralCoeff_general_split_on)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalDomain (intervalDomainConstExtend constExtend_eq_lift_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardLimitRestartBdd

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. The bounded-source package. -/

/-- **Bounded weak source package (constant bound + per-compact envelopes).**
The satisfiable replacement for `DuhamelSourceL1ContOn`'s global summable
envelope: a k-uniform bound `M` on the full horizon `[0, τ]` (fillable from the
solution's sup bound, including `s = 0` via a patched family), plus per-compact
DECAYING envelopes valid on `[a', τ]` for every `a' > 0` (fillable from the
per-compact K2 slice regularity — quadratic decay away from `s = 0`). -/
structure DuhamelSourceBddOn (a : ℝ → ℕ → ℝ) (τ : ℝ) where
  /-- k-uniform bound on the full horizon. -/
  M : ℝ
  hM_nonneg : 0 ≤ M
  hM : ∀ s, 0 ≤ s → s ≤ τ → ∀ k, |a s k| ≤ M
  /-- Each coefficient is continuous in time on the closed horizon. -/
  hcont : ∀ k, ContinuousOn (fun s : ℝ => a s k) (Set.Icc 0 τ)
  /-- Per-compact decaying envelope: `env a'` is valid on `[a', τ]`. -/
  env : ℝ → ℕ → ℝ
  henv_summable : ∀ a', 0 < a' → a' ≤ τ → Summable (env a')
  henv_bound : ∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ τ → ∀ k, |a s k| ≤ env a' k

/-- Forgetful map: a global-envelope package is in particular a bounded one
(`M := ∑ envelope`, every window envelope := the global one). -/
def _root_.ShenWork.IntervalPicardLimitRestartWeak.DuhamelSourceL1ContOn.toBddOn
    {a : ℝ → ℕ → ℝ} {τ : ℝ} (hτ0 : 0 ≤ τ) (src : DuhamelSourceL1ContOn a τ) :
    DuhamelSourceBddOn a τ where
  M := ∑' j, src.envelope j
  hM_nonneg := tsum_nonneg (fun j =>
    le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl hτ0 j))
  hM := by
    intro s hs hsτ k
    have hnn : ∀ j, 0 ≤ src.envelope j := fun j =>
      le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl hτ0 j)
    refine le_trans (src.henv_bound s hs hsτ k) ?_
    have := src.henv_summable.sum_le_tsum {k} (fun j _ => hnn j)
    simpa using this
  hcont := src.hcont
  env := fun _ => src.envelope
  henv_summable := fun _ _ _ => src.henv_summable
  henv_bound := fun a' ha' s hs hsτ k =>
    src.henv_bound s (le_trans ha'.le hs) hsτ k

/-! ## 2. Raw-bound Duhamel coefficient estimates.

Both estimates depend only on a POINTWISE bound for the single mode `k` on
`[0, t]` and continuity of that mode — no package, no summability.  They serve
the constant-`M` and the window-envelope instantiations alike. -/

/-- **Raw crude bound.**  `|duhamelSpectralCoeff a t k| ≤ t · C` from a
pointwise bound `C` for mode `k` on `[0, t]`. -/
theorem abs_duhamelSpectralCoeff_le_of_bound
    {a : ℝ → ℕ → ℝ} {t C : ℝ} (ht : 0 < t) (k : ℕ)
    (hC : ∀ s, 0 ≤ s → s ≤ t → |a s k| ≤ C) :
    |duhamelSpectralCoeff a t k| ≤ t * C := by
  unfold duhamelSpectralCoeff
  have hb : ∀ s ∈ Set.uIcc (0:ℝ) t,
      |Real.exp (-(t - s) * (λ_ k)) * a s k| ≤ C := by
    intro s hs
    rw [Set.uIcc_of_le ht.le] at hs
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (-(t - s) * (λ_ k)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hts : 0 ≤ t - s := by linarith [hs.2]
      have hlam : 0 ≤ (λ_ k) := by
        unfold unitIntervalCosineEigenvalue; positivity
      nlinarith [mul_nonneg hts hlam]
    calc Real.exp (-(t - s) * (λ_ k)) * |a s k|
        ≤ 1 * |a s k| := by
          apply mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)
      _ = |a s k| := one_mul _
      _ ≤ C := hC s hs.1 hs.2
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (0:ℝ)..t, Real.exp (-(t - s) * (λ_ k)) * a s k‖
      ≤ C * |t - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le ht.le] at hs
        rw [Real.norm_eq_abs]
        exact hb s (by rw [Set.uIcc_of_le ht.le]; exact ⟨le_of_lt hs.1, hs.2⟩)
    _ = t * C := by rw [sub_zero, abs_of_pos ht]; ring

/-- **Raw eigenvalue-weighted bound (parabolic gain).**
`λₖ · |duhamelSpectralCoeff a t k| ≤ C` from a pointwise bound `C` for mode `k`
on `[0, t]` and continuity of that mode on `[0, t]`.  FTC:
`∫₀ᵗ λ e^{−(t−s)λ} ds = 1 − e^{−tλ} ≤ 1`. -/
theorem eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound
    {a : ℝ → ℕ → ℝ} {t C : ℝ} (ht : 0 < t) (k : ℕ)
    (hC : ∀ s, 0 ≤ s → s ≤ t → |a s k| ≤ C)
    (hcont : ContinuousOn (fun s : ℝ => a s k) (Set.Icc 0 t)) :
    unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k| ≤ C := by
  have hC_nn : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 le_rfl ht.le)
  by_cases hk : k = 0
  · -- k = 0: λ₀ = 0
    simp [hk, unitIntervalCosineEigenvalue]
    exact hC_nn
  · -- k ≥ 1
    set eigk := (λ_ k) with heigk_def
    have heigk_pos : 0 < eigk := by
      show 0 < unitIntervalCosineEigenvalue k
      unfold unitIntervalCosineEigenvalue
      have : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      positivity
    have hF_deriv : ∀ s : ℝ, HasDerivAt (fun u => Real.exp (-(t - u) * eigk))
        (eigk * Real.exp (-(t - s) * eigk)) s := by
      intro s
      have hinner : HasDerivAt (fun u => -(t - u) * eigk) eigk s := by
        have h1 : HasDerivAt (fun u => -t * eigk + u * eigk) (0 + 1 * eigk) s :=
          (hasDerivAt_const s (-t * eigk)).add ((hasDerivAt_id s).mul_const eigk)
        convert h1 using 1
        · funext u; ring
        · ring
      have := (Real.hasDerivAt_exp (-(t - s) * eigk)).comp s hinner
      rwa [mul_comm] at this
    have hexp_cont : Continuous (fun s : ℝ => Real.exp (-(t - s) * eigk)) := by
      apply Continuous.comp Real.continuous_exp
      exact (continuous_const.sub continuous_id).neg.mul continuous_const
    have hint : ∫ s in (0:ℝ)..t, eigk * Real.exp (-(t - s) * eigk)
        = 1 - Real.exp (-t * eigk) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF_deriv s)
        ((continuous_const.mul hexp_cont).continuousOn.intervalIntegrable)]
      simp only [sub_self, sub_zero, neg_zero, zero_mul, Real.exp_zero]
    unfold duhamelSpectralCoeff
    have h_fa_int : IntervalIntegrable (fun s => Real.exp (-(t - s) * eigk) * a s k)
        volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.le]
      exact hexp_cont.continuousOn.mul hcont
    have h_fe_int : IntervalIntegrable (fun s => Real.exp (-(t - s) * eigk) * C)
        volume 0 t :=
      (hexp_cont.mul continuous_const).continuousOn.intervalIntegrable
    have h_abs_bound : |∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * a s k|
        ≤ ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * C := by
      rw [abs_le]; constructor
      · have h1 : ∫ s in (0:ℝ)..t, -(Real.exp (-(t - s) * eigk) * C)
            ≤ ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * a s k :=
          intervalIntegral.integral_mono_on ht.le h_fe_int.neg h_fa_int (fun s hs => by
            have hexp := (Real.exp_pos (-(t - s) * eigk)).le
            have henv := (abs_le.mp (hC s hs.1 hs.2)).1
            nlinarith)
        rwa [intervalIntegral.integral_neg] at h1
      · exact intervalIntegral.integral_mono_on ht.le h_fa_int h_fe_int (fun s hs =>
          mul_le_mul_of_nonneg_left
            (le_trans (le_abs_self _) (hC s hs.1 hs.2))
            (Real.exp_pos _).le)
    have hne : eigk ≠ 0 := ne_of_gt heigk_pos
    have h_factor : ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * C
        = C * ((1 - Real.exp (-t * eigk)) / eigk) := by
      rw [show (fun s => Real.exp (-(t - s) * eigk) * C) =
          (fun s => C * Real.exp (-(t - s) * eigk)) from by ext s; ring,
        intervalIntegral.integral_const_mul]
      congr 1
      rw [eq_div_iff hne, mul_comm, ← intervalIntegral.integral_const_mul]
      exact hint
    calc eigk * |∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * a s k|
        ≤ eigk * (C * ((1 - Real.exp (-t * eigk)) / eigk)) := by
          apply mul_le_mul_of_nonneg_left (h_abs_bound.trans h_factor.le) heigk_pos.le
      _ = C * (1 - Real.exp (-t * eigk)) := by field_simp
      _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ hC_nn
          linarith [Real.exp_nonneg (-t * eigk)]
      _ = C := mul_one _

/-! ## 3. `ℓ¹` summability of the Duhamel coefficients from the constant bound.

`|duh t k| ≤ M/λₖ` for `k ≥ 1` (parabolic gain) and `≤ t·M` at `k = 0`;
`∑ 1/λₖ < ∞`. -/

theorem summable_abs_duhamelSpectralCoeff_bdd
    {a : ℝ → ℕ → ℝ} {τ : ℝ} (src : DuhamelSourceBddOn a τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ) :
    Summable (fun k => |duhamelSpectralCoeff a t k|) := by
  have hCk : ∀ k, ∀ s, 0 ≤ s → s ≤ t → |a s k| ≤ src.M :=
    fun k s hs hst => src.hM s hs (le_trans hst htτ) k
  have hcontk : ∀ k, ContinuousOn (fun s : ℝ => a s k) (Set.Icc 0 t) :=
    fun k => (src.hcont k).mono (Set.Icc_subset_Icc le_rfl htτ)
  -- tail comparison: |duh (k+1)| ≤ M / λ_{k+1} = (M/π²)·1/(k+1)²
  have hgsum : Summable
      (fun n : ℕ => src.M * (1 / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left (src.M * (1 / Real.pi ^ 2))
  have htail : Summable (fun k => |duhamelSpectralCoeff a t (k + 1)|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hgsum
    have hlam_pos : 0 < (λ_ (k + 1)) := by
      unfold unitIntervalCosineEigenvalue
      have : (0:ℝ) < ((k : ℝ) + 1) := by positivity
      push_cast
      positivity
    have hgain := eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound ht (k + 1)
      (hCk (k + 1)) (hcontk (k + 1))
    have hlam_eq : (λ_ (k + 1)) = ((k : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue; push_cast; ring
    have hdiv : |duhamelSpectralCoeff a t (k + 1)| ≤ src.M / (λ_ (k + 1)) := by
      rw [le_div_iff₀ hlam_pos]
      calc |duhamelSpectralCoeff a t (k + 1)| * (λ_ (k + 1))
          = (λ_ (k + 1)) * |duhamelSpectralCoeff a t (k + 1)| := by ring
        _ ≤ src.M := hgain
    refine le_trans hdiv (le_of_eq ?_)
    rw [hlam_eq]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  exact (summable_nat_add_iff
    (f := fun k => |duhamelSpectralCoeff a t k|) 1).mp htail

/-! ## 4. The `∑∫ = ∫∑` swap from the constant bound. -/

/-- **Bounded spectral Duhamel series.**  Same conclusion as
`duhamelSpectral_eq_cosineSeries_weak`, from the constant bound alone (the
underlying swap `duhamelValue_adot_eq_tsum_on` takes a constant `Mdot`). -/
theorem duhamelSpectral_eq_cosineSeries_bdd {t x τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceBddOn a τ) (ht : 0 < t) (htτ : t ≤ τ) :
    (∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x)
      = ∑' n, duhamelSpectralCoeff a t n * cosineMode n x := by
  rw [duhamelValue_adot_eq_tsum_on (adot := a) (Mdot := src.M)
      ht htτ (fun s hs hsτ n => src.hM s hs hsτ n) src.hcont (b := t) ht.le (le_refl t)]
  refine tsum_congr (fun n => ?_)
  calc (∫ s in (0:ℝ)..t, unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
      = ∫ s in (0:ℝ)..t,
          (Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n) * cosineMode n x :=
        intervalIntegral.integral_congr (fun s _ => by
          simp only [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode, cosineMode]; ring)
    _ = (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n)
          * cosineMode n x := intervalIntegral.integral_mul_const _ _
    _ = duhamelSpectralCoeff a t n * cosineMode n x := rfl

/-! ## 5. `ℓ¹` summability of `limitCoeff` from the constant bound. -/

theorem summable_abs_limitCoeff_bdd
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ) :
    Summable (fun k =>
      |ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k|) := by
  have hhom : Summable (fun k =>
      |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hduh := summable_abs_duhamelSpectralCoeff_bdd src ht htτ
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  exact abs_add_le _ _

/-! ## 6. Eigenvalue-weighted summability via the time split (the key lemma).

`∑ λₖ |limitCoeff t k| < ∞` from constant `M` + per-compact envelopes:
split the Duhamel coefficient at `t/2`; the head gains `e^{−(t/2)λₖ}` against
the crude `(t/2)·M` bound, the tail reads the family on `[t/2, t]` where the
window envelope `env (t/2)` decays. -/

theorem summable_eigenvalue_mul_abs_limitCoeff_bdd
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (_hM0 : 0 ≤ M₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ) :
    Summable (fun k => (λ_ k) *
      |ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k|) := by
  set a' : ℝ → ℕ → ℝ := fun s k => cosineCoeffs (logisticLifted p (u s)) k with ha'
  set t₂ : ℝ := t / 2 with ht₂def
  have ht₂ : 0 < t₂ := by rw [ht₂def]; linarith
  have ht₂t : t₂ ≤ t := by rw [ht₂def]; linarith
  have ht₂τ : t₂ ≤ τ := le_trans ht₂t htτ
  have htt₂ : 0 < t - t₂ := by rw [ht₂def]; linarith
  -- the split (per mode)
  have hsplit : ∀ k, duhamelSpectralCoeff a' t k
      = Real.exp (-(t - t₂) * (λ_ k)) * duhamelSpectralCoeff a' t₂ k
        + duhamelSpectralCoeff (fun σ k => a' (t₂ + σ) k) (t - t₂) k :=
    fun k => duhamelSpectralCoeff_general_split_on (a := a') (T := τ)
      src.hcont ht₂.le ht₂t htτ k
  -- head: |duh a' t₂ k| ≤ t₂·M (crude)
  have hhead : ∀ k, |duhamelSpectralCoeff a' t₂ k| ≤ t₂ * src.M :=
    fun k => abs_duhamelSpectralCoeff_le_of_bound ht₂ k
      (fun s hs hst₂ => src.hM s hs (le_trans hst₂ ht₂τ) k)
  -- tail: λₖ·|duh (shifted) (t−t₂) k| ≤ env t₂ k (window envelope + gain)
  have htail : ∀ k, (λ_ k) *
      |duhamelSpectralCoeff (fun σ k => a' (t₂ + σ) k) (t - t₂) k|
        ≤ src.env t₂ k := by
    intro k
    refine eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound htt₂ k ?_ ?_
    · intro σ hσ hσtt₂
      exact src.henv_bound t₂ ht₂ (t₂ + σ) (by linarith) (by linarith) k
    · have hmaps : Set.MapsTo (fun σ : ℝ => t₂ + σ) (Set.Icc 0 (t - t₂))
          (Set.Icc 0 τ) := by
        intro σ hσ
        exact ⟨by linarith [hσ.1, ht₂.le], by linarith [hσ.2]⟩
      exact (src.hcont k).comp
        (continuous_const.add continuous_id).continuousOn hmaps
  -- eigenvalue nonnegativity
  have heig_nn : ∀ k, 0 ≤ (λ_ k) := fun k => by
    unfold unitIntervalCosineEigenvalue; positivity
  -- comparison series
  refine Summable.of_nonneg_of_le
    (f := fun k => M₀ * ((λ_ k) * Real.exp (-t * (λ_ k)))
      + ((t₂ * src.M) * ((λ_ k) * Real.exp (-(t - t₂) * (λ_ k)))
        + src.env t₂ k))
    (fun k => mul_nonneg (heig_nn k) (abs_nonneg _))
    (fun k => ?_) ?_
  · -- per-mode bound
    unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
    calc (λ_ k) * |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
            + duhamelSpectralCoeff a' t k|
        ≤ (λ_ k) * (|Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
            + |duhamelSpectralCoeff a' t k|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (heig_nn k)
      _ = (λ_ k) * |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
            + (λ_ k) * |duhamelSpectralCoeff a' t k| := by ring
      _ ≤ M₀ * ((λ_ k) * Real.exp (-t * (λ_ k)))
            + ((t₂ * src.M) * ((λ_ k) * Real.exp (-(t - t₂) * (λ_ k)))
              + src.env t₂ k) := by
          apply add_le_add
          · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            calc (λ_ k) * (Real.exp (-t * (λ_ k)) *
                    |cosineCoeffs (intervalDomainLift u₀) k|)
                ≤ (λ_ k) * (Real.exp (-t * (λ_ k)) * M₀) := by
                  apply mul_le_mul_of_nonneg_left _ (heig_nn k)
                  exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
              _ = M₀ * ((λ_ k) * Real.exp (-t * (λ_ k))) := by ring
          · -- split the Duhamel part
            rw [hsplit k]
            calc (λ_ k) * |Real.exp (-(t - t₂) * (λ_ k)) * duhamelSpectralCoeff a' t₂ k
                    + duhamelSpectralCoeff (fun σ k => a' (t₂ + σ) k) (t - t₂) k|
                ≤ (λ_ k) * (|Real.exp (-(t - t₂) * (λ_ k)) * duhamelSpectralCoeff a' t₂ k|
                    + |duhamelSpectralCoeff (fun σ k => a' (t₂ + σ) k) (t - t₂) k|) :=
                  mul_le_mul_of_nonneg_left (abs_add_le _ _) (heig_nn k)
              _ = (λ_ k) * |Real.exp (-(t - t₂) * (λ_ k)) * duhamelSpectralCoeff a' t₂ k|
                    + (λ_ k) * |duhamelSpectralCoeff (fun σ k => a' (t₂ + σ) k) (t - t₂) k| := by
                  ring
              _ ≤ (t₂ * src.M) * ((λ_ k) * Real.exp (-(t - t₂) * (λ_ k)))
                    + src.env t₂ k := by
                  apply add_le_add
                  · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
                    calc (λ_ k) * (Real.exp (-(t - t₂) * (λ_ k))
                            * |duhamelSpectralCoeff a' t₂ k|)
                        ≤ (λ_ k) * (Real.exp (-(t - t₂) * (λ_ k)) * (t₂ * src.M)) := by
                          apply mul_le_mul_of_nonneg_left _ (heig_nn k)
                          exact mul_le_mul_of_nonneg_left (hhead k) (Real.exp_pos _).le
                      _ = (t₂ * src.M) * ((λ_ k) * Real.exp (-(t - t₂) * (λ_ k))) := by
                          ring
                  · exact htail k
  · -- summability of the comparison series
    have h1 : Summable (fun k => M₀ * ((λ_ k) * Real.exp (-t * (λ_ k)))) :=
      (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        ht).mul_left M₀
    have h2 : Summable (fun k =>
        (t₂ * src.M) * ((λ_ k) * Real.exp (-(t - t₂) * (λ_ k)))) :=
      (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        htt₂).mul_left (t₂ * src.M)
    have h3 : Summable (src.env t₂) := src.henv_summable t₂ ht₂ ht₂τ
    exact h1.add (h2.add h3)

/-! ## 7. Cosine representation of the limit (subtype-continuity, bounded source).

The Provider's `hagree` entry point against the bounded package. -/

/-- **Cosine representation of the Picard limit (representation-fed, bounded
source).**  Copy of `limit_lift_eq_cosineSeries_of_subtypeCont` with the
summable-envelope package replaced by the bounded one: the heat-value adapter
and the swap take the constant bound; the final summability is the parabolic
`ℓ¹` estimate. -/
theorem limit_lift_eq_cosineSeries_of_subtypeCont_bdd
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ)
    (hfix_t : ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (u t) x
      = ∑' k, ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k * cosineMode k x := by
  -- Subtype continuity of the logistic source from constExtend continuity.
  have hL_subtype : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (u s)) := by
    intro s hs hsT
    have heq : intervalLogisticSource p (u s) =
        (intervalDomainConstExtend (intervalLogisticSource p (u s))) ∘ Subtype.val := by
      funext ⟨y, hy⟩
      simp only [Function.comp]
      rw [constExtend_eq_lift_on_Icc hy]
      simp only [intervalDomainLift]
      split_ifs with h
      · exact congr_arg _ (Subtype.ext rfl)
      · exact absurd hy h
    rw [heq]; exact (hL_cont s hs hsT).comp continuous_subtype_val
  rw [hfix_t x hx,
    intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * unitIntervalCosineEigenvalue k)
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
          ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  set a : ℝ → ℕ → ℝ := fun s k =>
    cosineCoeffs (logisticLifted p (u s)) k with ha
  -- k-uniform bound on the family, in the shape the adapter wants
  have hMa : ∀ s, 0 ≤ s → s ≤ τ → ∀ k, |a s k| ≤ src.M := src.hM
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (a s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hsub : Continuous (intervalLogisticSource p (u s)) :=
      hL_subtype s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs (logisticLifted p (u s)) k| ≤ src.M :=
      fun k => hMa s (le_of_lt hs.1) (le_trans (le_of_lt hs.2) htτ) k
    show intervalFullSemigroupOperator (t - s)
        (intervalDomainLift (intervalLogisticSource p (u s))) x
        = unitIntervalCosineHeatValue (t - s) (a s) x
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        hts hsub hMs hx
  have hduh_eq : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      = ∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0:ℝ) t → s ∈ Set.Ioo (0:ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hsmem
      refine ⟨hsmem.1, lt_of_le_of_ne hsmem.2 ?_⟩
      intro hst; exact hs (by simp [hst])
    filter_upwards [hmem] with s hs hsIoc
    exact hduh_integrand s (hs hsIoc)
  rw [hhom, hduh_eq, duhamelSpectral_eq_cosineSeries_bdd src ht htτ]
  have hcosbd : ∀ (c : ℕ → ℝ) (k : ℕ), ‖c k * cosineMode k x‖ ≤ |c k| := by
    intro c k
    rw [Real.norm_eq_abs, abs_mul]
    calc |c k| * |cosineMode k x| ≤ |c k| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa [cosineMode] using Real.abs_cos_le_one ((k : ℝ) * Real.pi * x)
      _ = |c k| := mul_one _
  have hM0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  have hsum_hom : Summable (fun k =>
      (Real.exp (-t * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k)
        * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hsum_duh : Summable (fun k =>
      duhamelSpectralCoeff a t k * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    exact summable_abs_duhamelSpectralCoeff_bdd src ht htτ
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun k => ?_)
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  rw [ha]
  ring

end ShenWork.IntervalPicardLimitRestartBdd
