/-
  ShenWork/Paper2/IntervalPicardIterateRestart.lean

  Phase-0 / M1 — the χ₀ = 0 half-step **restart cosine identity** for Picard
  iterates.

  For `p : CM2Params` with `p.χ₀ = 0`, the Picard iterate

      picardIter p u₀ (n+1) t = Φ(u₀, picardIter p u₀ n)(t)

  (where `Φ = intervalGradientDuhamelMap`) admits, for every `0 < t`, the
  *half-step restart* cosine representation on `[0,1]`:

      lift(uₙ₊₁(t))(x)
        = ∑'ₖ restartDuhamelCoeff
              (cosineCoeffs (lift uₙ₊₁(t/2)))
              (fun σ k => cosineCoeffs (logisticLifted p (uₙ(t/2+σ))) k)
              (t/2) k · cosineMode k x.

  χ₀ = 0 kills the chemotaxis flux term (`(-p.χ₀)·(…) = 0`), so the map reduces
  to `S(t)u₀ + ∫₀ᵗ S(t−s) Lₙ(s) ds` — `intervalGradientDuhamelMap_eq_of_chi0_zero`.
  The two pieces have spectral forms (S1b for the propagator, the Duhamel
  spectral series for the integral), giving termwise coefficients

      c_k(t) = e^{−tλ_k}·û₀_k + duhamelSpectralCoeff L̂ₙ t k.

  With `τ := t/2`, `t = τ + τ`, the heat factor splits `e^{−tλ} = e^{−τλ}e^{−τλ}`
  and the Duhamel integral splits `∫₀ᵗ = ∫₀^τ + ∫_τ^t`, the second piece
  σ-shifting (change of variables `s = τ+σ`) into the shifted-source Duhamel
  coefficient.  Combined with coefficient extraction at `t/2`, this is exactly
  `restartDuhamelCoeff`.

  ## Hypotheses (discharged later in the induction; satisfiable by design)

  * `hu₀_cont`, `hu₀_bound` (H1) — the datum `lift u₀` is continuous with
    uniformly bounded cosine coefficients.  *Dischargeable*: this is the input
    datum; `CM2Params` data are C²/Neumann so their cosine coefficients are even
    ℓ¹-summable, a fortiori bounded.
  * `hsrc0` (H2) — the `DuhamelSourceTimeC1` for the source family
    `s ↦ cosineCoeffs (logisticLifted p (picardIter p u₀ n s))` on `[0,t]`,
    used for the spectral form of the full Duhamel term and of the half-step
    term.  *Dischargeable*: M3-module output (the logistic source of a continuous
    iterate slice is C¹ in time with an ℓ¹ envelope).  NOTE: the σ-shift required
    by the conclusion (`σ ↦ t/2+σ`) is handled *internally* by
    `duhamelSpectralCoeff_halfstep_split` from the same `hsrc0` (the split's
    second piece is literally `duhamelSpectralCoeff (fun σ k => a (τ+σ) k) τ k`),
    so no separate "shifted" hypothesis is needed — the shifted source family in
    the conclusion is the change-of-variables image of `hsrc0`.
  * `hL_cont` (H3) — per-slice continuity
    `∀ s ∈ (0,t], Continuous (logisticLifted p (picardIter p u₀ n s))`.
    *Dischargeable*: iterate-continuity lemmas (`picardIter_ball` continuity);
    the lifted logistic of a continuous slice is continuous.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.Paper2.IntervalMildRegularityBootstrap

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupComposition
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff DuhamelSourceTimeC1 duhamelSpectral_eq_cosineSeries)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardIterateRestart

/-- The eigenvalue used throughout (matches `unitIntervalCosineEigenvalue` and
`restartDuhamelCoeff`). -/
local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## Step 0 — χ₀ = 0 reduces the gradient-Duhamel map to `S(t)u₀ + ∫S L`. -/

/-- With `p.χ₀ = 0` the chemotaxis flux term vanishes and the gradient-Duhamel
map is the homogeneous propagator plus the logistic-source Duhamel integral. -/
theorem intervalGradientDuhamelMap_eq_of_chi0_zero
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) :
    intervalGradientDuhamelMap p u₀ u t x
      = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        + ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1 := by
  unfold intervalGradientDuhamelMap
  rw [hχ0]
  ring

/-! ## Step 1 — generic ℓ¹ cosine-series coefficient extraction.

If `g(x) = ∑'ₖ c k · cosineMode k x` with `∑ₖ |c k| < ∞`, then
`cosineCoeffs g n = c n`.  This is the restart-series analogue of
`cosineCoeffs_unitIntervalCosineHeatValue`; it does not assume the series is a
heat value, only ℓ¹ majorisation of the raw coefficients. -/
theorem cosineCoeffs_of_l1_cosineSeries
    {c : ℕ → ℝ} (hc : Summable (fun k => |c k|)) (n : ℕ) :
    cosineCoeffs (fun x => ∑' k, c k * cosineMode k x) n = c n := by
  rw [cosineCoeffs_eq_factor_mul_integral]
  -- The summand family.
  set F : ℕ → ℝ → ℝ := fun k x =>
    Real.cos ((n : ℝ) * Real.pi * x) * (c k * cosineMode k x) with hF
  have hpt : ∀ x : ℝ,
      Real.cos ((n : ℝ) * Real.pi * x) * (∑' k, c k * cosineMode k x)
        = ∑' k, F k x := by
    intro x
    rw [← tsum_mul_left]
  have hF_cont : ∀ k, Continuous (F k) := by
    intro k
    simp only [hF, cosineMode]
    fun_prop
  have hF_int : ∀ k,
      Integrable (F k) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    exact ((hF_cont k).integrableOn_Icc (μ := volume)).mono_set
      Set.Ioc_subset_Icc_self
  have hF_bound : ∀ k x, ‖F k x‖ ≤ |c k| := by
    intro k x
    simp only [hF, cosineMode, Real.norm_eq_abs]
    rw [abs_mul, abs_mul]
    have hc1 : |Real.cos ((n : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hc2 : |Real.cos ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    calc |Real.cos ((n : ℝ) * Real.pi * x)| * (|c k| * |Real.cos ((k : ℝ) * Real.pi * x)|)
        ≤ 1 * (|c k| * 1) := by
          apply mul_le_mul hc1 _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hc2 (abs_nonneg _)
      _ = |c k| := by ring
  have hF_sum : Summable (fun k =>
      ∫ x, ‖F k x‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun x => norm_nonneg _) ?_ hc
    intro k
    calc (∫ x, ‖F k x‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        ≤ ∫ _x, |c k| ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          apply integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (integrable_const _)
          exact Filter.Eventually.of_forall fun x => hF_bound k x
      _ = |c k| * (volume.restrict (Set.Ioc (0 : ℝ) 1) Set.univ).toReal := by
          rw [integral_const, smul_eq_mul, MeasureTheory.measureReal_def]
          ring
      _ = |c k| := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioc]
          norm_num
  have hswap :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  have hIoc : (∫ x in (0 : ℝ)..1,
        Real.cos ((n : ℝ) * Real.pi * x) * (∑' k, c k * cosineMode k x))
      = ∑' k, ∫ x, F k x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have h1 : (∫ x in Set.Ioc (0:ℝ) 1,
          Real.cos ((n : ℝ) * Real.pi * x) *
            (∑' k, c k * cosineMode k x) ∂volume)
        = ∫ x, (∑' k, F k x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
    rw [h1, ← hswap]
  rw [hIoc]
  have hterm : ∀ k, (∫ x, F k x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      = c k *
        ∫ x in (0 : ℝ)..1,
          ShenWork.CosineSpectrum.cosineMode n x *
            ShenWork.CosineSpectrum.cosineMode k x := by
    intro k
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [hF, ShenWork.CosineSpectrum.cosineMode]
    ring
  have hsingle : (∑' k, ∫ x, F k x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      = ∫ x, F n x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply tsum_eq_single
    intro k hk
    rw [hterm k, ShenWork.CosineSpectrum.cosineMode_orthogonal (Ne.symm hk),
      mul_zero]
  rw [hsingle, hterm n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ShenWork.CosineSpectrum.cosineMode_self_integral_zero]
    norm_num
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    rw [ShenWork.CosineSpectrum.cosineMode_self_integral_of_ne_zero hne,
      if_neg hne]
    ring

/-! ## Step 2 — spectral form of the propagator piece as a `cosineMode` series. -/

/-- `unitIntervalCosineHeatValue t a x = ∑'ₖ (e^{−tλₖ} aₖ)·cosineMode k x`:
the heat value is literally the cosine series with damped coefficients. -/
theorem heatValue_eq_cosineSeries (t : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    unitIntervalCosineHeatValue t a x
      = ∑' k, (Real.exp (-t * (λ_ k)) * a k) * cosineMode k x := by
  unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight
    unitIntervalCosineMode
  apply tsum_congr
  intro k
  simp only [cosineMode]
  ring

/-! ## Step 3 — spectral coefficient of the whole iterate slice.

`c k(t) := e^{−tλₖ}·û₀ₖ + duhamelSpectralCoeff L̂ t k`, the `k`-th coefficient of
`lift(uₙ₊₁(t))`. -/

/-- The full spectral coefficient of the `(n+1)`-st iterate slice. -/
def iterateCoeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
    + duhamelSpectralCoeff
        (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) t k

/-! ## Step 4 — summability of `|c k(t)|`.

`|e^{−tλ}û₀| ≤ M₀·e^{−tλ}` (summable) and
`|duhamelSpectralCoeff L̂ t| ≤ t·envₖ` (envelope ℓ¹). -/

/-- `|duhamelSpectralCoeff a t k| ≤ |t| · envelope k` when the source is bounded
by an envelope on `[0,t]` (here via `DuhamelSourceTimeC1`). -/
theorem abs_duhamelSpectralCoeff_le
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    |duhamelSpectralCoeff a t k| ≤ t * src.envelope k := by
  unfold duhamelSpectralCoeff
  have hb : ∀ s ∈ Set.uIcc (0:ℝ) t,
      |Real.exp (-(t - s) * (λ_ k)) * a s k| ≤ src.envelope k := by
    intro s hs
    rw [Set.uIcc_of_le ht.le] at hs
    have hs0 : 0 ≤ s := hs.1
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
      _ ≤ src.envelope k := src.henv_bound s hs0 k
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (0:ℝ)..t, Real.exp (-(t - s) * (λ_ k)) * a s k‖
      ≤ src.envelope k * |t - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le ht.le] at hs
        rw [Real.norm_eq_abs]
        exact hb s (by rw [Set.uIcc_of_le ht.le]; exact ⟨le_of_lt hs.1, hs.2⟩)
    _ = t * src.envelope k := by rw [sub_zero, abs_of_pos ht]; ring

/-- `Summable (fun k => |c k(t)|)` for the iterate-slice coefficients, from H1
(bounded `û₀`) and H2′ (`DuhamelSourceTimeC1` for the source family). -/
theorem summable_abs_iterateCoeff
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => |iterateCoeff p u₀ n t k|) := by
  have hM0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  -- homogeneous part summable
  have hhom : Summable (fun k =>
      |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  -- duhamel part summable
  have hduh : Summable (fun k =>
      |duhamelSpectralCoeff
          (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
          t k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (hsrc0.henv_summable.mul_left t)
    exact abs_duhamelSpectralCoeff_le hsrc0 ht k
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  unfold iterateCoeff
  exact abs_add_le _ _

/-! ## Step 5 — the spectral representation of the iterate slice on `[0,1]`. -/

/-- The `(n+1)`-st iterate slice equals its cosine series with coefficients
`iterateCoeff` on `[0,1]`, for `0 < t`.  Combines the χ₀ = 0 reduction, S1b for
the propagator, the Duhamel spectral series, and `tsum_add`. -/
theorem iterate_lift_eq_cosineSeries
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (logisticLifted p (picardIter p u₀ n s)))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (picardIter p u₀ (n+1) t) x
      = ∑' k, iterateCoeff p u₀ n t k * cosineMode k x := by
  -- Reduce the lift to the map value.
  have hlift : intervalDomainLift (picardIter p u₀ (n+1) t) x
      = intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t ⟨x, hx⟩ := by
    show (if hx' : x ∈ Set.Icc (0:ℝ) 1 then
          picardIter p u₀ (n+1) t ⟨x, hx'⟩ else 0) = _
    rw [dif_pos hx]
    rfl
  rw [hlift, intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  -- S1b for the homogeneous propagator term.
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * (λ_ k))
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  -- Spectral form of the Duhamel integral.
  -- First rewrite the integrand via S1b (Icc) pointwise.
  set a : ℝ → ℕ → ℝ := fun s k =>
    cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k with ha
  have hMa : ∀ s, 0 ≤ s → ∀ k, |a s k| ≤ ∑' j, hsrc0.envelope j := by
    intro s hs k
    have hnn : ∀ j, 0 ≤ hsrc0.envelope j := fun j =>
      le_trans (abs_nonneg _) (hsrc0.henv_bound 0 le_rfl j)
    refine le_trans (hsrc0.henv_bound s hs k) ?_
    have := hsrc0.henv_summable.sum_le_tsum {k} (fun j _ => hnn j)
    simpa using this
  -- Pointwise spectral form of the integrand on the open interval `Ioo 0 t`
  -- (where `0 < s < t`, so `t - s > 0` for S1b and `0 < s` for `hL_cont`).
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x
        = unitIntervalCosineHeatValue (t - s) (a s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hcont : Continuous (logisticLifted p (picardIter p u₀ n s)) :=
      hL_cont s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k|
        ≤ ∑' j, hsrc0.envelope j := fun k => hMa s (le_of_lt hs.1) k
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc hts hcont hMs hx
  -- a.e. on `Ι 0 t = Ioc 0 t` the integrands agree (they differ only at `s = t`).
  have hduh_eq : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x)
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
  rw [hhom, hduh_eq, duhamelSpectral_eq_cosineSeries hsrc0 ht]
  -- Now both terms are cosine series; combine via `tsum_add`.
  have hcosbd : ∀ (c : ℕ → ℝ) (k : ℕ), ‖c k * cosineMode k x‖ ≤ |c k| := by
    intro c k
    rw [Real.norm_eq_abs, abs_mul]
    calc |c k| * |cosineMode k x| ≤ |c k| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa [cosineMode] using Real.abs_cos_le_one ((k : ℝ) * Real.pi * x)
      _ = |c k| := mul_one _
  have hM0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  have hsum_hom : Summable (fun k =>
      (Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k)
        * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hsum_duh : Summable (fun k =>
      duhamelSpectralCoeff a t k * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (hsrc0.henv_summable.mul_left t)
    exact abs_duhamelSpectralCoeff_le hsrc0 ht k
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun k => ?_)
  unfold iterateCoeff
  rw [ha]
  ring

/-! ## Step 6 — the Duhamel half-step split.

`duhamelSpectralCoeff a (τ+τ) k = e^{−τλₖ}·duhamelSpectralCoeff a τ k
  + duhamelSpectralCoeff (fun σ => a (τ+σ)) τ k`.

`∫₀^{2τ} = ∫₀^τ + ∫_τ^{2τ}`; the first factors `e^{−(2τ−s)λ} = e^{−τλ}e^{−(τ−s)λ}`,
the second σ-shifts by `s = τ+σ`. -/
theorem duhamelSpectralCoeff_halfstep_split
    {a : ℝ → ℕ → ℝ} (ha_cont : ∀ k, Continuous (fun s => a s k))
    (τ : ℝ) (k : ℕ) :
    duhamelSpectralCoeff a (τ + τ) k
      = Real.exp (-τ * (λ_ k)) * duhamelSpectralCoeff a τ k
        + duhamelSpectralCoeff (fun σ k => a (τ + σ) k) τ k := by
  unfold duhamelSpectralCoeff
  -- integrability of the integrand on any interval
  have hint : ∀ b c : ℝ, IntervalIntegrable
      (fun s => Real.exp (-(τ + τ - s) * (λ_ k)) * a s k) volume b c := by
    intro b c
    apply Continuous.intervalIntegrable
    have : Continuous (fun s => Real.exp (-(τ + τ - s) * (λ_ k))) := by
      fun_prop
    exact this.mul (ha_cont k)
  -- split the integral at τ
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint 0 τ) (hint τ (τ + τ))]
  congr 1
  · -- first piece: factor e^{−τλ}
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _hs
    show Real.exp (-(τ + τ - s) * (λ_ k)) * a s k
      = Real.exp (-τ * (λ_ k)) * (Real.exp (-(τ - s) * (λ_ k)) * a s k)
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · -- second piece: change of variables s = τ + σ
    have hcv := intervalIntegral.integral_comp_add_left
      (a := (0:ℝ)) (b := τ)
      (fun s => Real.exp (-(τ + τ - s) * (λ_ k)) * a s k) τ
    simp only [add_zero] at hcv
    rw [← hcv]
    apply intervalIntegral.integral_congr
    intro σ _hσ
    show Real.exp (-(τ + τ - (τ + σ)) * (λ_ k)) * a (τ + σ) k
      = Real.exp (-(τ - σ) * (λ_ k)) * a (τ + σ) k
    congr 2
    ring

/-! ## Step 7 — coefficient extraction at the half step.

`cosineCoeffs (lift uₙ₊₁(τ)) k = iterateCoeff p u₀ n τ k`. -/
theorem cosineCoeffs_halfstep_eq_iterateCoeff
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {τ : ℝ} (hτ : 0 < τ)
    (hL_cont : ∀ s, 0 < s → s ≤ τ →
      Continuous (logisticLifted p (picardIter p u₀ n s)))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) τ)) k
      = iterateCoeff p u₀ n τ k := by
  have hrepr : ∀ x ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n+1) τ) x
        = ∑' j, iterateCoeff p u₀ n τ j * cosineMode j x := fun x hx =>
    iterate_lift_eq_cosineSeries p hχ0 u₀ n hu₀_cont hu₀_bound hsrc0 hτ hL_cont hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_iterateCoeff p u₀ n hu₀_bound hsrc0 hτ) k

/-! ## Main theorem — the half-step restart cosine identity (χ₀ = 0). -/

/-- **M1 — half-step restart cosine identity.**  For `p.χ₀ = 0` and `0 < t`,
the lift of the `(n+1)`-st Picard iterate slice at time `t` is the cosine series
whose `k`-th coefficient is `restartDuhamelCoeff` applied to the half-step
coefficients (extracted from the slice at `t/2`) and the time-shifted logistic
source family.  Holds on `[0,1]`.

The hypotheses are the discharged-later induction inputs:
`hu₀_cont`/`hu₀_bound` (datum data, H1), `hsrc0` (source time-`C¹`, H2 — the
`σ ↦ t/2+σ` shift required by the conclusion is handled internally by
`duhamelSpectralCoeff_halfstep_split`, so no separate shifted hypothesis is
needed), and `hL_cont` (per-slice continuity, H3). -/
theorem picardIterateRestart_cosineIdentity
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (logisticLifted p (picardIter p u₀ n s))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n+1) t))
      (fun x => ∑' k : ℕ,
        restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) (t/2))))
          (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t/2 + σ))) k)
          (t/2) k * cosineMode k x)
      (Set.Icc (0:ℝ) 1) := by
  intro x hx
  set τ : ℝ := t / 2 with hτdef
  have hτ : 0 < τ := by rw [hτdef]; linarith
  have htτ : t = τ + τ := by rw [hτdef]; ring
  -- the source family for the τ-slice (continuity from hsrc0)
  have ha_cont : ∀ k, Continuous
      (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) := fun k =>
    continuous_iff_continuousAt.2 (fun s => (hsrc0.hderiv s k).continuousAt)
  -- spectral form of the t-slice
  rw [iterate_lift_eq_cosineSeries p hχ0 u₀ n hu₀_cont hu₀_bound hsrc0 ht hL_cont hx]
  refine tsum_congr (fun k => ?_)
  -- per-mode: iterateCoeff p u₀ n t k = restartDuhamelCoeff (…) (…) τ k
  congr 1
  -- expand iterateCoeff at t = τ+τ and restartDuhamelCoeff at τ
  unfold iterateCoeff restartDuhamelCoeff
  -- coefficient extraction at the half step
  have hext : cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) τ)) k
      = iterateCoeff p u₀ n τ k :=
    cosineCoeffs_halfstep_eq_iterateCoeff p hχ0 u₀ n hu₀_cont hu₀_bound hsrc0 hτ
      (fun s hs hsτ => hL_cont s hs (by rw [htτ]; linarith)) k
  rw [hext]
  unfold iterateCoeff
  -- Duhamel split at the half step
  have hsplit := duhamelSpectralCoeff_halfstep_split (a :=
      fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      ha_cont τ k
  -- heat factor splits: e^{−tλ} = e^{−τλ}·e^{−τλ}
  have hexp : Real.exp (-t * (λ_ k))
      = Real.exp (-τ * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; rw [htτ]; ring
  rw [hexp, htτ, hsplit]
  ring

end ShenWork.IntervalPicardIterateRestart
