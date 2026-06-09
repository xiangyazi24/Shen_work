/-
  ShenWork/Paper2/IntervalPicardLimitRestartWeak.lean

  Phase-0 / M4b — BREAK THE CIRCLE: weak-hypothesis ★ + limit envelope package.

  ## The circle (why this module exists)

  M4's ★ (`IntervalPicardLimitRestart.picardLimitRestart_cosineIdentity`)
  consumes `hsrc0 : DuhamelSourceTimeC1` of the LIMIT's source family.  But
  producing a `DuhamelSourceTimeC1` for the limit needs the σ-DERIVATIVE fields,
  which require K1(u) (M3b), which requires rep(u) = ★ itself.  Circular.

  ## The break

  `DuhamelSourceTimeC1`'s σ-DERIVATIVE fields (`adot`, `hderiv`, `hadotcont`,
  `derivBound`, `hderivBound`) are NOT needed for ★'s pipeline:

  * `duhamelSpectral_eq_cosineSeries` uses only `henv_summable`, `henv_bound`,
    and continuity of `s ↦ a s n` (derived there FROM `hderiv`, but continuity
    alone suffices).
  * `abs_duhamelSpectralCoeff_le` uses only `henv_bound`.
  * `duhamelSpectralCoeff_halfstep_split` uses only continuity.

  So we introduce the WEAK source package `DuhamelSourceL1Cont` carrying only
  envelope + summability + bound + continuity (NO derivative fields), re-prove
  the three pipeline lemmas against it, and re-derive ★ verbatim with `hsrc0`
  weakened to `DuhamelSourceL1Cont`.  This breaks the circularity that blocks
  `hMildLocal(χ₀ = 0)`: the weak package is producible from the limit's
  continuous slices alone, with no derivative data.

  ## Deliverables

  1. `DuhamelSourceL1Cont` + forgetful map `DuhamelSourceTimeC1 → DuhamelSourceL1Cont`.
  2. Weak pipeline lemmas:
     - `duhamelSpectral_eq_cosineSeries_weak`
     - `abs_duhamelSpectralCoeff_le_weak`
     - (`duhamelSpectralCoeff_halfstep_split` already needs only continuity — we
       re-export it via the package's `hcont`.)
  3. `picardLimitRestart_cosineIdentity_weak` — M4's ★ with `hsrc0` weakened.
  4. `limitSource_l1cont` — the limit's weak package from n-uniform iterate
     envelope data + pointwise coefficient convergence + slice continuity (the
     envelope-passing via `le_of_tendsto` is PROVED; the per-mode convergence and
     slice-continuity are taken as named satisfiable hypotheses — see header
     justification at the theorem).

  ## Honest-partial status of deliverable 4

  `limitSource_l1cont` takes two named hypotheses:
    (b) `hconv` — pointwise convergence
        `cosineCoeffs (L(uₙ σ)) k → cosineCoeffs (L(u σ)) k`, satisfiable from
        uniform slice convergence (`IntervalMildPicard.picardIter_uniform_convergence`)
        + logistic Lipschitz (`IntervalLogisticLipschitz`) + interval-integral
        dominated convergence on the cosine functional;
    (c) `hcont` — `∀ k, Continuous (σ ↦ cosineCoeffs (L(u σ)) k)`, satisfiable
        from `HasContinuousSlices` of the limit + logistic continuity + integral
        continuity.
  The genuinely new content of deliverable 4 — that the LIMIT's coefficients are
  dominated by the n → ∞ image of the per-iterate envelope — is PROVED here via
  `le_of_tendsto` from `hconv` and the n-uniform per-mode bounds.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestart
import ShenWork.PDE.IntervalSpectralSubtypeAdapter

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupComposition
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalMildPicard (picardIter picardLimit GradientMildSolutionData)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff DuhamelSourceTimeC1 duhamelSpectral_eq_cosineSeries
    duhamelValue_adot_eq_tsum)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff GradientMildHalfStepRestartData gradientMildHalfStepInitialCoeff)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalPicardIterateRestart
  (iterateCoeff heatValue_eq_cosineSeries cosineCoeffs_of_l1_cosineSeries
    duhamelSpectralCoeff_halfstep_split
    intervalGradientDuhamelMap_eq_of_chi0_zero)

noncomputable section

namespace ShenWork.IntervalPicardLimitRestartWeak

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. The weak source package. -/

/-- **Weak Duhamel source package (`L¹` envelope + time continuity, NO
derivative fields).**  Carries exactly the data the ★ pipeline consumes:

* an `ℓ¹`-summable `envelope` dominating `|a s n|` for `0 ≤ s`,
* and continuity of each coefficient `s ↦ a s n`.

This is the same payload as `DuhamelSourceTimeC1` minus the σ-derivative fields
(`adot`, `hderiv`, `hadotcont`, `derivBound`, `hderivBound`).  Producing it for
the Picard limit requires NO derivative data — only the limit's continuous
slices — which is exactly what breaks the M4 circularity. -/
structure DuhamelSourceL1Cont (a : ℝ → ℕ → ℝ) where
  /-- `ℓ¹` envelope dominating the coefficients uniformly in non-negative time. -/
  envelope : ℕ → ℝ
  /-- The envelope is summable. -/
  henv_summable : Summable envelope
  /-- The coefficients are dominated by the envelope for non-negative time. -/
  henv_bound : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n
  /-- Each coefficient is continuous in time. -/
  hcont : ∀ n, Continuous (fun s : ℝ => a s n)

/-- **Forgetful map** `DuhamelSourceTimeC1 → DuhamelSourceL1Cont`: drop the
derivative fields, derive continuity from `hderiv`. -/
def DuhamelSourceL1Cont.ofTimeC1 {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :
    DuhamelSourceL1Cont a where
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := src.henv_bound
  hcont := fun n =>
    continuous_iff_continuousAt.2 (fun s => (src.hderiv s n).continuousAt)

/-! ## 2. Weak variants of the pipeline lemmas.

These are thin re-proofs of M1's `abs_duhamelSpectralCoeff_le` and
`IntervalDuhamelClosedC2.duhamelSpectral_eq_cosineSeries` against the weak
package.  We verified (by reading the originals) that each uses only
`envelope`/`henv_summable`/`henv_bound`/continuity — never a derivative field. -/

/-- **Weak coefficient bound.**  `|duhamelSpectralCoeff a t k| ≤ t · envelope k`.
Copy of M1's `abs_duhamelSpectralCoeff_le` proof; uses only `henv_bound`. -/
theorem abs_duhamelSpectralCoeff_le_weak
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceL1Cont a) {t : ℝ} (ht : 0 < t) (k : ℕ) :
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

/-- **Weak spectral Duhamel series.**  `∫₀ᵗ S(t−s)g(s)(x) ds = ∑'ₙ bₙ(t) cos(nπx)`.
Copy of `IntervalDuhamelClosedC2.duhamelSpectral_eq_cosineSeries` proof; the
continuity it derives there from `hderiv` is taken directly from `src.hcont`. -/
theorem duhamelSpectral_eq_cosineSeries_weak {t x : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceL1Cont a) (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x)
      = ∑' n, duhamelSpectralCoeff a t n * cosineMode n x := by
  have hnn : ∀ n, 0 ≤ src.envelope n :=
    fun n => le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)
  have hunif : ∀ s, 0 ≤ s → ∀ i, |a s i| ≤ ∑' k, src.envelope k := by
    intro s hs i
    refine le_trans (src.henv_bound s hs i) ?_
    have := src.henv_summable.sum_le_tsum {i} (fun j _ => hnn j)
    simpa using this
  rw [duhamelValue_adot_eq_tsum (adot := a) (Mdot := ∑' k, src.envelope k)
      ht hunif src.hcont (b := t) ht.le (le_refl t)]
  refine tsum_congr (fun n => ?_)
  calc (∫ s in (0:ℝ)..t, unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
      = ∫ s in (0:ℝ)..t,
          (Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n) * cosineMode n x :=
        intervalIntegral.integral_congr (fun s _ => by
          simp only [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode, cosineMode]; ring)
    _ = (∫ s in (0:ℝ)..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n)
          * cosineMode n x := intervalIntegral.integral_mul_const _ _
    _ = duhamelSpectralCoeff a t n * cosineMode n x := rfl

/-! ## Weak versions of M4's intermediate lemmas (verbatim re-proofs against the
weak package). -/

/-- Weak `summable_abs_limitCoeff`. -/
theorem summable_abs_limitCoeff_weak
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k =>
      |ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k|) := by
  have hhom : Summable (fun k =>
      |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hduh : Summable (fun k =>
      |duhamelSpectralCoeff
          (fun s k => cosineCoeffs (logisticLifted p (u s)) k) t k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (hsrc0.henv_summable.mul_left t)
    exact abs_duhamelSpectralCoeff_le_weak hsrc0 ht k
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  exact abs_add_le _ _

/-- Weak `limit_lift_eq_cosineSeries`. -/
theorem limit_lift_eq_cosineSeries_weak
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s)))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (u t) x
      = ∑' k, ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k * cosineMode k x := by
  rw [hfix t ht x hx,
    intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * (λ_ k))
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  set a : ℝ → ℕ → ℝ := fun s k =>
    cosineCoeffs (logisticLifted p (u s)) k with ha
  have hMa : ∀ s, 0 ≤ s → ∀ k, |a s k| ≤ ∑' j, hsrc0.envelope j := by
    intro s hs k
    have hnn : ∀ j, 0 ≤ hsrc0.envelope j := fun j =>
      le_trans (abs_nonneg _) (hsrc0.henv_bound 0 le_rfl j)
    refine le_trans (hsrc0.henv_bound s hs k) ?_
    have := hsrc0.henv_summable.sum_le_tsum {k} (fun j _ => hnn j)
    simpa using this
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (a s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hcont : Continuous (logisticLifted p (u s)) :=
      hL_cont s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs (logisticLifted p (u s)) k|
        ≤ ∑' j, hsrc0.envelope j := fun k => hMa s (le_of_lt hs.1) k
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc hts hcont hMs hx
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
  rw [hhom, hduh_eq, duhamelSpectral_eq_cosineSeries_weak hsrc0 ht]
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
    exact abs_duhamelSpectralCoeff_le_weak hsrc0 ht k
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun k => ?_)
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  rw [ha]
  ring

/-- Weak `cosineCoeffs_halfstep_eq_limitCoeff`. -/
theorem cosineCoeffs_halfstep_eq_limitCoeff_weak
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {τ : ℝ} (hτ : 0 < τ)
    (hL_cont : ∀ s, 0 < s → s ≤ τ → Continuous (logisticLifted p (u s)))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (u τ)) k
      = ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ k := by
  have hrepr : ∀ x ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u τ) x
        = ∑' j, ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ j
            * cosineMode j x := fun x hx =>
    limit_lift_eq_cosineSeries_weak p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 hτ hL_cont hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_limitCoeff_weak p u₀ u hu₀_bound hsrc0 hτ) k

/-! ## 3. ★-weak — the half-step restart cosine identity for the LIMIT, with the
weak source package. -/

/-- **M4b — ★-weak.**  Identical statement to M4's
`IntervalPicardLimitRestart.picardLimitRestart_cosineIdentity`, but `hsrc0` is the
WEAK package `DuhamelSourceL1Cont` (no derivative fields).  This is the
circle-breaker: the limit's weak package is producible from continuous slices
alone (no K1(u)/M3b needed), so this ★ no longer depends on rep(u). -/
theorem picardLimitRestart_cosineIdentity_weak
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))) :
    Set.EqOn (intervalDomainLift (u t))
      (fun x => ∑' k : ℕ,
        restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (u (t/2))))
          (fun σ k => cosineCoeffs (logisticLifted p (u (t/2 + σ))) k)
          (t/2) k * cosineMode k x)
      (Set.Icc (0:ℝ) 1) := by
  intro x hx
  set τ : ℝ := t / 2 with hτdef
  have hτ : 0 < τ := by rw [hτdef]; linarith
  have htτ : t = τ + τ := by rw [hτdef]; ring
  -- continuity of the limit source family (now directly from hsrc0.hcont)
  have ha_cont : ∀ k, Continuous
      (fun s => cosineCoeffs (logisticLifted p (u s)) k) := hsrc0.hcont
  rw [limit_lift_eq_cosineSeries_weak p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 ht hL_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff restartDuhamelCoeff
  have hext : cosineCoeffs (intervalDomainLift (u τ)) k
      = ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ k :=
    cosineCoeffs_halfstep_eq_limitCoeff_weak p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 hτ
      (fun s hs hsτ => hL_cont s hs (by rw [htτ]; linarith)) k
  rw [hext]
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  have hsplit := duhamelSpectralCoeff_halfstep_split (a :=
      fun s k => cosineCoeffs (logisticLifted p (u s)) k) ha_cont τ k
  have hexp : Real.exp (-t * (λ_ k))
      = Real.exp (-τ * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; rw [htτ]; ring
  rw [hexp, htτ, hsplit]
  ring

/-! ## 4. The limit's weak package from n-uniform iterate data.

`limitSource_l1cont` assembles `DuhamelSourceL1Cont` for the LIMIT source family
`σ ↦ cosineCoeffs (logisticLifted p (u σ))` out of:

* (a) per-n envelopes: an `ℓ¹` envelope `envFn` dominating every iterate's
  coefficients uniformly in n and σ ≥ 0 (the n → ∞ image of M3's per-iterate
  envelope; from M-final's `PicardIterateUniformData`).
* (b) `hconv` — pointwise convergence of the iterate coefficients to the limit
  coefficients (NAMED satisfiable; satisfiable from
  `IntervalMildPicard.picardIter_uniform_convergence` + logistic Lipschitz +
  interval-integral dominated convergence on the cosine functional).
* (c) `hcont` — continuity of each limit coefficient in time (NAMED satisfiable;
  from the limit's continuous slices + logistic/integral continuity).

The genuinely new content — that the limit coefficients inherit the envelope —
is PROVED via `le_of_tendsto` (Step (a)→envelope_bound below). -/
def limitSource_l1cont
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (envFn : ℕ → ℝ)
    (henv_summable : Summable envFn)
    -- (a) n-uniform per-iterate envelope (M3 envelope, uniform in n):
    (henv_iter : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ∀ k,
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k| ≤ envFn k)
    -- (b) pointwise coefficient convergence (NAMED satisfiable):
    (hconv : ∀ (s : ℝ) (k : ℕ),
      Tendsto (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        atTop (nhds (cosineCoeffs (logisticLifted p (u s)) k)))
    -- (c) continuity of the limit coefficients in time (NAMED satisfiable):
    (hcont : ∀ k, Continuous (fun s => cosineCoeffs (logisticLifted p (u s)) k)) :
    DuhamelSourceL1Cont
      (fun σ k => cosineCoeffs (logisticLifted p (u σ)) k) where
  envelope := envFn
  henv_summable := henv_summable
  henv_bound := by
    intro s hs k
    -- pass the n-uniform bound to the limit via `le_of_tendsto`.
    have hb : ∀ n, |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k| ≤ envFn k :=
      fun n => henv_iter n s hs k
    have htend : Tendsto
        (fun n => |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k|)
        atTop (nhds (|cosineCoeffs (logisticLifted p (u s)) k|)) :=
      (hconv s k).abs
    exact le_of_tendsto htend (Filter.Eventually.of_forall hb)
  hcont := hcont

/-! ## 5. Corollary — ★ for the limit with NO source-derivative hypothesis.

Chaining `limitSource_l1cont` into `picardLimitRestart_cosineIdentity_weak`: the
LIMIT's half-step restart cosine identity holds with the source data supplied
purely by the n-uniform iterate envelope + pointwise convergence + slice
continuity — NO `DuhamelSourceTimeC1` derivative fields anywhere.  The circle is
broken. -/
theorem picardLimitRestart_cosineIdentity_of_iterateData
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (envFn : ℕ → ℝ) (henv_summable : Summable envFn)
    (henv_iter : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ∀ k,
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k| ≤ envFn k)
    (hconv : ∀ (s : ℝ) (k : ℕ),
      Tendsto (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        atTop (nhds (cosineCoeffs (logisticLifted p (u s)) k)))
    (hcoeff_cont : ∀ k, Continuous (fun s => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))) :
    Set.EqOn (intervalDomainLift (u t))
      (fun x => ∑' k : ℕ,
        restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (u (t/2))))
          (fun σ k => cosineCoeffs (logisticLifted p (u (t/2 + σ))) k)
          (t/2) k * cosineMode k x)
      (Set.Icc (0:ℝ) 1) :=
  picardLimitRestart_cosineIdentity_weak p hχ0 u₀ u hfix hu₀_cont hu₀_bound
    (limitSource_l1cont p u₀ u envFn henv_summable henv_iter hconv hcoeff_cont) ht hL_cont

end ShenWork.IntervalPicardLimitRestartWeak

open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1Cont abs_duhamelSpectralCoeff_le_weak
   duhamelSpectral_eq_cosineSeries_weak)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalDomain (intervalDomainConstExtend constExtend_eq_lift_on_Icc)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)

/-- **Cosine representation of the Picard limit (representation-fed).**
Same conclusion as `limit_lift_eq_cosineSeries_weak` but replaces the
`Continuous (intervalDomainLift u₀)` and `Continuous (logisticLifted ...)`
hypotheses by cosine-representation data, routing through the globally-C²
cosine series proxy via `intervalFullSemigroupOperator_congr_Icc`.

This is the paper-faithful variant: u₀ ∈ C(Ω̄) (subtype), NOT
`Continuous (intervalDomainLift u₀)` (false for positive data).
Routes through `intervalDomainConstExtend` (globally continuous). -/
theorem limit_lift_eq_cosineSeries_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t)
    (hfix_t : ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (u t) x
      = ∑' k, ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k * cosineMode k x := by
  -- Derive subtype continuity for logistic source from constExtend continuity.
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
  -- Rewrite via Duhamel formula (same first step as _weak).
  rw [hfix_t x hx,
    intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  -- Homogeneous term: adapter replaces the false `Continuous (lift u₀)` with
  -- the paper-faithful `Continuous u₀` (subtype).
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * unitIntervalCosineEigenvalue k)
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
          ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  -- Source coefficient family (same as _weak).
  set a : ℝ → ℕ → ℝ := fun s k =>
    cosineCoeffs (logisticLifted p (u s)) k with ha
  have hMa : ∀ s, 0 ≤ s → ∀ k, |a s k| ≤ ∑' j, hsrc0.envelope j := by
    intro s hs k
    have hnn : ∀ j, 0 ≤ hsrc0.envelope j := fun j =>
      le_trans (abs_nonneg _) (hsrc0.henv_bound 0 le_rfl j)
    refine le_trans (hsrc0.henv_bound s hs k) ?_
    have := hsrc0.henv_summable.sum_le_tsum {k} (fun j _ => hnn j)
    simpa using this
  -- Duhamel integrand: adapter with subtype continuity of logistic source.
  -- `logisticLifted p (u s) = intervalDomainLift (intervalLogisticSource p (u s))`
  -- by definition, so the adapter applies directly.
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (a s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hsub : Continuous (intervalLogisticSource p (u s)) :=
      hL_subtype s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs (logisticLifted p (u s)) k|
        ≤ ∑' j, hsrc0.envelope j := fun k => hMa s (le_of_lt hs.1) k
    show intervalFullSemigroupOperator (t - s)
        (intervalDomainLift (intervalLogisticSource p (u s))) x
        = unitIntervalCosineHeatValue (t - s) (a s) x
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        hts hsub hMs hx
  -- Integral equality via ae congr (identical to _weak).
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
  rw [hhom, hduh_eq, duhamelSpectral_eq_cosineSeries_weak hsrc0 ht]
  -- Summability + tsum algebra (identical to _weak).
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
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (hsrc0.henv_summable.mul_left t)
    exact abs_duhamelSpectralCoeff_le_weak hsrc0 ht k
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun k => ?_)
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  rw [ha]
  ring


/-! ## Eigenvalue-weighted summability of `limitCoeff`.

The key estimate for `hbsum` in the reduced ledger: `limitCoeff` is not just ℓ¹
summable (which follows from `summable_abs_limitCoeff_weak`), but eigenvalue-weighted
summable: `∑ λ_k |limitCoeff k| < ∞`.

**Homogeneous part:** `λ_k exp(-tλ_k) |ĉ₀_k| ≤ M₀ λ_k exp(-tλ_k)`, summable by
parabolic smoothing (`expEigSummable`-type estimate).

**Duhamel part:** The tight estimate is `λ_k |duhamelSpectralCoeff a t k| ≤ envelope_k`
(not `t λ_k envelope_k`!). This uses the integral identity
`∫₀ᵗ exp(-uλ) du = (1 - exp(-tλ))/λ` for λ > 0, so
`λ · envelope · (1-exp(-tλ))/λ = envelope · (1-exp(-tλ)) ≤ envelope`. -/

section EigenvalueWeighted

open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1Cont
  abs_duhamelSpectralCoeff_le_weak)

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **Eigenvalue-weighted Duhamel coefficient estimate.**
`λ_k * |duhamelSpectralCoeff a t k| ≤ envelope_k` for all k.
Uses: `∫₀ᵗ exp(-(t-s)λ) ds = (1-exp(-tλ))/λ` for λ > 0, giving
`λ * envelope * (1-exp(-tλ))/λ = envelope * (1-exp(-tλ)) ≤ envelope`.
For k = 0 (λ₀ = 0): trivially `0 ≤ envelope₀`. -/
theorem eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceL1Cont a) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k| ≤ src.envelope k := by
  by_cases hk : k = 0
  · -- k = 0: λ₀ = 0, so 0 * |...| = 0 ≤ envelope 0
    simp [hk, unitIntervalCosineEigenvalue]
    exact le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl 0)
  · -- k ≥ 1: use ∫₀ᵗ λ exp(-(t-s)λ) ds = 1 - exp(-tλ) ≤ 1
    set eigk := (λ_ k) with heigk_def
    have heigk_pos : 0 < eigk := by
      show 0 < unitIntervalCosineEigenvalue k
      unfold unitIntervalCosineEigenvalue
      have : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      positivity
    have henv_nn : 0 ≤ src.envelope k :=
      le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl k)
    -- Move eigk inside the integral and bound |a(s,k)| by envelope
    -- eigk * |∫₀ᵗ exp(-(t-s)eigk) a(s,k) ds|
    -- ≤ ∫₀ᵗ eigk * exp(-(t-s)eigk) * envelope_k ds  (by abs under integral + envelope)
    -- = envelope_k * ∫₀ᵗ eigk * exp(-(t-s)eigk) ds
    -- = envelope_k * (1 - exp(-teigk))  (by antiderivative)
    -- ≤ envelope_k
    -- Step 1: HasDerivAt for the antiderivative exp(-(t-u)*eigk)
    -- Write -(t-u)*eigk = -t*eigk + u*eigk to avoid chain rule complexity
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
    -- Continuity of the exponential kernel
    have hexp_cont : Continuous (fun s : ℝ => Real.exp (-(t - s) * eigk)) := by
      apply Continuous.comp Real.continuous_exp
      exact (continuous_const.sub continuous_id).neg.mul continuous_const
    -- Step 2: ∫₀ᵗ eigk exp(-(t-s)eigk) ds = 1 - exp(-teigk)   [FTC with antiderivative exp(-(t-u)*eigk)]
    have hint : ∫ s in (0:ℝ)..t, eigk * Real.exp (-(t - s) * eigk) = 1 - Real.exp (-t * eigk) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF_deriv s)
        ((continuous_const.mul hexp_cont).continuousOn.intervalIntegrable)]
      simp only [sub_self, sub_zero, neg_zero, zero_mul, Real.exp_zero]
    -- Step 3: Bound |duhamelSpectralCoeff| via signed integral comparison + FTC.
    unfold duhamelSpectralCoeff
    have h_fa_int : IntervalIntegrable (fun s => Real.exp (-(t - s) * eigk) * a s k)
        volume 0 t :=
      (hexp_cont.mul (src.hcont k)).continuousOn.intervalIntegrable
    have h_fe_int : IntervalIntegrable (fun s => Real.exp (-(t - s) * eigk) * src.envelope k)
        volume 0 t :=
      (hexp_cont.mul continuous_const).continuousOn.intervalIntegrable
    -- |∫ exp·a| ≤ ∫ exp·envelope   (signed bounds + abs_le)
    have h_abs_bound : |∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * a s k|
        ≤ ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * src.envelope k := by
      rw [abs_le]; constructor
      · -- lower: -(∫ exp·env) ≤ ∫ exp·a
        have h1 : ∫ s in (0:ℝ)..t, -(Real.exp (-(t - s) * eigk) * src.envelope k)
            ≤ ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * a s k :=
          intervalIntegral.integral_mono_on ht.le h_fe_int.neg h_fa_int (fun s hs => by
            have hexp := (Real.exp_pos (-(t - s) * eigk)).le
            have henv := (abs_le.mp (src.henv_bound s hs.1 k)).1
            nlinarith)
        rwa [intervalIntegral.integral_neg] at h1
      · -- upper: ∫ exp·a ≤ ∫ exp·env
        exact intervalIntegral.integral_mono_on ht.le h_fa_int h_fe_int (fun s hs =>
          mul_le_mul_of_nonneg_left
            (le_trans (le_abs_self _) (src.henv_bound s hs.1 k))
            (Real.exp_pos _).le)
    -- ∫ exp·env = env · (1 - exp(-tλ))/λ   [factor constant + FTC]
    have hne : eigk ≠ 0 := ne_of_gt heigk_pos
    have h_factor : ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * src.envelope k
        = src.envelope k * ((1 - Real.exp (-t * eigk)) / eigk) := by
      rw [show (fun s => Real.exp (-(t - s) * eigk) * src.envelope k) =
          (fun s => src.envelope k * Real.exp (-(t - s) * eigk)) from by ext s; ring,
        intervalIntegral.integral_const_mul]
      congr 1
      rw [eq_div_iff hne, mul_comm, ← intervalIntegral.integral_const_mul]
      exact hint
    -- Final assembly: eigk * |duh| ≤ env · (1-exp(-tλ)) ≤ env
    calc eigk * |∫ s in (0:ℝ)..t, Real.exp (-(t - s) * eigk) * a s k|
        ≤ eigk * (src.envelope k * ((1 - Real.exp (-t * eigk)) / eigk)) := by
          gcongr; exact h_abs_bound.trans h_factor.le
      _ = src.envelope k * (1 - Real.exp (-t * eigk)) := by field_simp
      _ ≤ src.envelope k * 1 := by gcongr; linarith [Real.exp_nonneg (-t * eigk)]
      _ = src.envelope k := mul_one _

/-- **Eigenvalue-weighted summability of `limitCoeff` from weak source.**
`∑ λ_k |limitCoeff k| < ∞`, proved from `DuhamelSourceL1Cont` alone (no derivative
fields needed). -/
theorem summable_eigenvalue_mul_abs_limitCoeff_weak
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM0 : 0 ≤ M₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1Cont (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => (λ_ k) *
      |ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k|) := by
  set a' : ℝ → ℕ → ℝ := fun s k => cosineCoeffs (logisticLifted p (u s)) k
  refine Summable.of_nonneg_of_le
    (f := fun k => M₀ * ((λ_ k) * Real.exp (-t * (λ_ k))) + hsrc0.envelope k)
    (fun k => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
    (fun k => ?_) ?_
  · -- bound: λ_k |limitCoeff k| ≤ M₀ λ_k exp(-tλ_k) + envelope_k
    unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
    calc (λ_ k) * |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
            + duhamelSpectralCoeff a' t k|
        ≤ (λ_ k) * (|Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
            + |duhamelSpectralCoeff a' t k|) := by
          apply mul_le_mul_of_nonneg_left (abs_add_le _ _)
          unfold unitIntervalCosineEigenvalue; positivity
      _ = (λ_ k) * |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
            + (λ_ k) * |duhamelSpectralCoeff a' t k| := by ring
      _ ≤ M₀ * ((λ_ k) * Real.exp (-t * (λ_ k))) + hsrc0.envelope k := by
          apply add_le_add
          · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            calc (λ_ k) * (Real.exp (-t * (λ_ k)) *
                    |cosineCoeffs (intervalDomainLift u₀) k|)
                ≤ (λ_ k) * (Real.exp (-t * (λ_ k)) * M₀) := by
                  apply mul_le_mul_of_nonneg_left _ (by unfold unitIntervalCosineEigenvalue; positivity)
                  exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
              _ = M₀ * ((λ_ k) * Real.exp (-t * (λ_ k))) := by ring
          · exact eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope hsrc0 ht k
  · exact (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
      ht).mul_left M₀ |>.add hsrc0.henv_summable

end EigenvalueWeighted
