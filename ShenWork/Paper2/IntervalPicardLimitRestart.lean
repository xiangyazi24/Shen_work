/-
  ShenWork/Paper2/IntervalPicardLimitRestart.lean

  Phase-0 / M4 — the χ₀ = 0 half-step **restart cosine identity** for the Picard
  LIMIT (mild solution).

  ## What this module proves (the ★ identity, step (1) of the M4 spec)

  Let `u := picardLimit p u₀ T` be the mild solution (fixed point of
  `intervalGradientDuhamelMap`, χ₀ = 0).  Each Picard iterate `u_{n+1}` satisfies
  M1's per-iterate half-step restart identity
  (`IntervalPicardIterateRestart.picardIterateRestart_cosineIdentity`).  The
  iterates converge to `u` uniformly on slices
  (`IntervalMildPicard.picardIter_uniform_convergence` / `picardLimit_*`).

  The spec's deliberate simplification — and what makes this the *limit* pass
  rather than a re-derivation — is that the half-step restart identity is the
  TERMWISE COEFFICIENT LIMIT of M1's per-iterate identities.  Concretely, the
  limit's restart series is *self-referential*: its source family is
  `logisticLifted p (u s)` with `u` the limit itself, exactly the n → ∞ image of
  the per-iterate source `logisticLifted p (picardIter p u₀ n s)` (the iterate
  source family converges, via the logistic Lipschitz lemma, to the limit source
  family; the coefficient functionals — `0..1` interval integrals against cosine
  modes — converge by uniform convergence of the slices; the per-mode spectral
  Duhamel coefficients and the cosine series itself pass to the limit under the
  n-uniform ℓ¹ envelope; the LHS converges by uniform convergence of the slices).

  This module realises that limit pass by reducing the limit slice via the mild
  fixed-point equation `u(t) = Φ(u₀,u)(t)` (the n → ∞ image of the per-iterate
  recursion `u_{n+1} = Φ(u₀,u_n)`) and then running the *same* spectral pipeline
  M1 ran for the iterates — χ₀ = 0 reduction (S0), heat-value spectral form (S1b),
  Duhamel spectral series, half-step Duhamel split, half-step coefficient
  extraction — now with `u` in the source slot.  Because the source family
  references `u`, the resulting identity is the mild solution's OWN half-step
  restart cosine identity. ★

  ## Hypotheses (named, satisfiable by design — the limit pass inputs)

  All hypotheses are facts the existing machinery (`IntervalMildPicard`,
  M-final `GradientMildSolutionData`, M1–M3) provides for the Picard limit;
  they are NOT the conclusion in disguise (the ★ identity itself — the
  *coefficient-level agreement* of the slice with its restart series — is proved
  here, not assumed).

  * `hfix` (FIXED POINT) — the mild-solution Duhamel equation
    `lift(u t)(x) = intervalGradientDuhamelMap p u₀ u t x` on `[0,1]`.
    *Satisfiable*: `IntervalMildSolution p T u₀ u` (the predicate `picardLimit`
    satisfies — `IntervalMildPicard.picardLimit_is_mildSolution`) IS this equation;
    it is the n → ∞ image of the per-iterate recursion M1 reduced through.
  * `hu₀_cont`, `hu₀_bound` (H1) — datum `lift u₀` continuous with bounded cosine
    coefficients.  *Satisfiable*: `CM2Params` data are C²/Neumann (ℓ¹ coefficients,
    a fortiori bounded).
  * `hsrc0` (H2) — `DuhamelSourceTimeC1` for the LIMIT source family
    `s ↦ cosineCoeffs (logisticLifted p (u s))`.  *Satisfiable*: M3-module output
    applied to the limit slice (the logistic source of a continuous, bounded slice
    is time-C¹ with an ℓ¹ envelope; the envelope is the n → ∞ image of the
    per-iterate envelopes — `le_of_tendsto` from M-final's
    `PicardIterateUniformData`).  The `σ ↦ t/2+σ` shift required by the conclusion
    is handled internally by `duhamelSpectralCoeff_halfstep_split`.
  * `hL_cont` (H3) — per-slice continuity
    `∀ s ∈ (0,t], Continuous (logisticLifted p (u s))`.  *Satisfiable*: the limit
    has continuous slices (`picardLimit_hasContinuousSlices`); the lifted logistic
    of a continuous slice is continuous.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardIterateRestart

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupComposition
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalMildPicard (picardIter picardLimit GradientMildSolutionData)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff DuhamelSourceTimeC1 duhamelSpectral_eq_cosineSeries)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff GradientMildHalfStepRestartData gradientMildHalfStepInitialCoeff)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalPicardIterateRestart
  (iterateCoeff heatValue_eq_cosineSeries cosineCoeffs_of_l1_cosineSeries
    abs_duhamelSpectralCoeff_le duhamelSpectralCoeff_halfstep_split
    intervalGradientDuhamelMap_eq_of_chi0_zero)

noncomputable section

namespace ShenWork.IntervalPicardLimitRestart

/-- The eigenvalue used throughout (matches `unitIntervalCosineEigenvalue` and
`restartDuhamelCoeff`). -/
local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## The limit spectral coefficient.

The `k`-th cosine coefficient of `lift(u(t))` for the mild solution `u`:
`c k(t) := e^{−tλₖ}·û₀ₖ + duhamelSpectralCoeff L̂ t k`, where `L̂` is the LIMIT's
own logistic source family.  This is the n → ∞ image of
`IntervalPicardIterateRestart.iterateCoeff` (whose source uses `picardIter n`). -/
def limitCoeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
    + duhamelSpectralCoeff
        (fun s k => cosineCoeffs (logisticLifted p (u s)) k) t k

/-! ## Step 1 — summability of `|c k(t)|` for the limit coefficients.

Identical envelope reasoning to M1's `summable_abs_iterateCoeff`, but for the
limit source family.  `|e^{−tλ}û₀| ≤ M₀·e^{−tλ}` (summable) and
`|duhamelSpectralCoeff L̂ t| ≤ t·envₖ` (envelope ℓ¹). -/
theorem summable_abs_limitCoeff
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => |limitCoeff p u₀ u t k|) := by
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
    exact abs_duhamelSpectralCoeff_le hsrc0 ht k
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  unfold limitCoeff
  exact abs_add_le _ _

/-! ## Step 2 — the spectral representation of the limit slice on `[0,1]`.

This is the n → ∞ image of M1's `iterate_lift_eq_cosineSeries`: where M1 reduced
`lift(u_{n+1}(t))` via the recursion `u_{n+1} = Φ(u₀,u_n)`, we reduce
`lift(u(t))` via the mild fixed-point equation `u(t) = Φ(u₀,u)(t)` (`hfix`).  The
downstream spectral pipeline (S0 χ₀-reduction, S1b heat value, Duhamel spectral
series) is identical but with the limit `u` in the source slot. -/
theorem limit_lift_eq_cosineSeries
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s)))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (u t) x
      = ∑' k, limitCoeff p u₀ u t k * cosineMode k x := by
  -- Reduce the lift to the map value via the mild fixed-point equation.
  rw [hfix t ht x hx,
    intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  -- S1b for the homogeneous propagator term.
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
  -- Pointwise spectral form of the integrand on the open interval `Ioo 0 t`.
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
  -- a.e. on `Ι 0 t = Ioc 0 t` the integrands agree (differ only at `s = t`).
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
  rw [hhom, hduh_eq, duhamelSpectral_eq_cosineSeries hsrc0 ht]
  -- Combine both cosine series via `tsum_add`.
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
  unfold limitCoeff
  rw [ha]
  ring

/-! ## Step 3 — half-step coefficient extraction for the limit.

`cosineCoeffs (lift u(τ)) k = limitCoeff p u₀ u τ k`.  Same shape as M1's
`cosineCoeffs_halfstep_eq_iterateCoeff`, using the limit's spectral
representation and ℓ¹ coefficient extraction. -/
theorem cosineCoeffs_halfstep_eq_limitCoeff
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k))
    {τ : ℝ} (hτ : 0 < τ)
    (hL_cont : ∀ s, 0 < s → s ≤ τ → Continuous (logisticLifted p (u s)))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (u τ)) k = limitCoeff p u₀ u τ k := by
  have hrepr : ∀ x ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u τ) x
        = ∑' j, limitCoeff p u₀ u τ j * cosineMode j x := fun x hx =>
    limit_lift_eq_cosineSeries p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 hτ hL_cont hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_limitCoeff p u₀ u hu₀_bound hsrc0 hτ) k

/-! ## ★ Main theorem — the half-step restart cosine identity for the LIMIT. -/

/-- **M4 — half-step restart cosine identity for the Picard limit.**  For
`p.χ₀ = 0` and `0 < t`, the lift of the mild-solution slice `u(t)` is the cosine
series whose `k`-th coefficient is `restartDuhamelCoeff` applied to the half-step
coefficients (extracted from the LIMIT slice at `t/2`) and the LIMIT's own
time-shifted logistic source family.  Holds on `[0,1]`.

This is the coefficient-limit pass: the source family `s ↦ logisticLifted p (u s)`
references the mild solution `u` itself — the n → ∞ image of M1's per-iterate
source `s ↦ logisticLifted p (picardIter p u₀ n s)`.  Reducing the limit slice
through the mild fixed-point equation `hfix` (the n → ∞ image of the per-iterate
recursion) and running M1's spectral pipeline therefore yields the mild
solution's OWN half-step restart cosine identity.

Hypotheses are the limit-pass inputs (all satisfiable by design, see header):
the mild fixed-point equation `hfix`, datum data `hu₀_cont`/`hu₀_bound` (H1), the
limit source time-`C¹` package `hsrc0` (H2 — the `σ ↦ t/2+σ` shift is handled
internally by `duhamelSpectralCoeff_halfstep_split`), and per-slice continuity
`hL_cont` (H3). -/
theorem picardLimitRestart_cosineIdentity
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
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
  -- continuity of the limit source family (from hsrc0)
  have ha_cont : ∀ k, Continuous
      (fun s => cosineCoeffs (logisticLifted p (u s)) k) := fun k =>
    continuous_iff_continuousAt.2 (fun s => (hsrc0.hderiv s k).continuousAt)
  -- spectral form of the t-slice
  rw [limit_lift_eq_cosineSeries p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 ht hL_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  unfold limitCoeff restartDuhamelCoeff
  -- coefficient extraction at the half step
  have hext : cosineCoeffs (intervalDomainLift (u τ)) k = limitCoeff p u₀ u τ k :=
    cosineCoeffs_halfstep_eq_limitCoeff p hχ0 u₀ u hfix hu₀_cont hu₀_bound hsrc0 hτ
      (fun s hs hsτ => hL_cont s hs (by rw [htτ]; linarith)) k
  rw [hext]
  unfold limitCoeff
  -- Duhamel split at the half step
  have hsplit := duhamelSpectralCoeff_halfstep_split (a :=
      fun s k => cosineCoeffs (logisticLifted p (u s)) k) ha_cont τ k
  -- heat factor splits: e^{−tλ} = e^{−τλ}·e^{−τλ}
  have hexp : Real.exp (-t * (λ_ k))
      = Real.exp (-τ * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; rw [htτ]; ring
  rw [hexp, htτ, hsplit]
  ring

/-! ## Step (5) — assembling `GradientMildHalfStepRestartData` for the limit.

The ★ identity supplies the `hagree` field of `GradientMildHalfStepRestartData`
for a `GradientMildSolutionData D` (whose carrier `D.u` is the mild solution),
once the datum and source hypotheses are supplied per time slice.

NOTE (honest-partial).  The `a` and `src` fields require the LIMIT source family's
`DuhamelSourceTimeC1` package *uniformly in `t`* and the per-`t` mild fixed-point
reduction and per-slice continuity.  These are the M3-module output and the
`IntervalMildSolution`/`picardLimit_hasContinuousSlices` facts; they are taken
here as the named per-`t` hypothesis families `hfix`/`hsrc`/`hLc`/`hu₀_*`, which
match the field obligations exactly.  The genuinely new content — the ★
coefficient-level agreement — is discharged by `picardLimitRestart_cosineIdentity`.

`gradientMildHalfStepInitialCoeff D t = cosineCoeffs (lift (D.u (t/2)))` by
definition, which is exactly the half-step coefficient family the ★ identity uses,
so the `hagree` field is `picardLimitRestart_cosineIdentity` verbatim. -/
def gradientMildHalfStepRestartData_of_limit
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (D.u t) x = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩)
    (hsrc : ∀ t, 0 < t → t < D.T → DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (D.u s)) k))
    (hsrcShift : ∀ t, 0 < t → t < D.T → DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticLifted p (D.u (t/2 + σ))) k))
    (hLc : ∀ t, 0 < t → t < D.T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (D.u s))) :
    GradientMildHalfStepRestartData D where
  a := fun t σ k => cosineCoeffs (logisticLifted p (D.u (t/2 + σ))) k
  src := fun t ht htT => hsrcShift t ht htT
  hagree := fun t ht htT => by
    have h := picardLimitRestart_cosineIdentity p hχ0 u₀ D.u hfix
      hu₀_cont hu₀_bound (hsrc t ht htT) ht (hLc t ht htT)
    -- `gradientMildHalfStepInitialCoeff D t` is definitionally
    -- `cosineCoeffs (intervalDomainLift (D.u (t/2)))`.
    simpa only [gradientMildHalfStepInitialCoeff] using h

end ShenWork.IntervalPicardLimitRestart
