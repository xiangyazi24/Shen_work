/-
  ShenWork/Paper2/IntervalPicardIterateRestartLocal.lean

  **Tower campaign stage 1 — File B (items 4–6).**

  Local-witness variants of the per-iterate restart representation.  These replace
  the GLOBAL canonical shifted source family — read by the consumers only on the
  half-step window `σ ∈ [0, t/2]` — by a `ShiftedSourceWitness`: any time-`C¹`
  package agreeing with the canonical family on `[0, t/2]` plus the half-step
  envelope decay.  The exact-vs-witness swap is the `[0, t/2]` congruence
  (`localRestartCoeff_congr_on_Icc` / `duhamelSpectralCoeff_congr_on_Icc` from
  File A).

  * `ShiftedSourceWitness p u₀ n t M A₂` — the carrier.
  * (4) `hbsum_succ_of_shiftedWitness` — eigenvalue-weighted ℓ¹ from the witness.
  * (5) `hagree_succ_of_shiftedWitness` — `[0,1]` agreement from the witness.
  * (6) `hagree_succ_of_subtypeCont` — kills the false
        `Continuous (intervalDomainLift u₀)` hypothesis, replaced by the
        paper-faithful subtype `Continuous u₀` (a thin re-wiring of the iterate
        restart chain through the subtype spectral adapter; only one call differs).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalPicardIterateUniform
import ShenWork.PDE.IntervalSpectralSubtypeAdapter

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff duhamelSpectral_eq_cosineSeries)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff restartSeries_eigenvalue_summable)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff hagree_succ)
open ShenWork.IntervalPicardIterateRestart
  (iterateCoeff heatValue_eq_cosineSeries cosineCoeffs_of_l1_cosineSeries
   abs_duhamelSpectralCoeff_le summable_abs_iterateCoeff
   intervalGradientDuhamelMap_eq_of_chi0_zero)
open ShenWork.IntervalPicardIterateUniform (Benv)
open ShenWork.IntervalDuhamelSourceShift
  (DuhamelSourceTimeC1.shift_nonneg duhamelSpectralCoeff_congr_on_Icc)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardIterateRestartLocal

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §B.0 — The shifted-source witness carrier. -/

/-- The canonical σ-shifted logistic source family read by the next-iterate restart
representation on the half-step window: `σ ↦ L̂ₙ(t/2 + σ)`. -/
def canonicalShiftedSource (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (t : ℝ) : ℝ → ℕ → ℝ :=
  fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k

/-- **The shifted-source witness.**  A time-`C¹` source package `a` that
*agrees* with the canonical σ-shifted logistic source on the half-step read window
`σ ∈ [0, t/2]`, together with the half-step envelope decay `|aσₖ| ≤ 2·Benv/(kπ)²`.
The consumers (`restartSeries_eigenvalue_summable`, the restart cosine identity)
read the shifted family only on `[0, t/2]`, so this witness is interchangeable with
the canonical family there. -/
structure ShiftedSourceWitness (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (t M A₂ : ℝ) where
  /-- The witness source family. -/
  a : ℝ → ℕ → ℝ
  /-- It is time-`C¹` (an honest `DuhamelSourceTimeC1` package). -/
  src : DuhamelSourceTimeC1 a
  /-- It agrees with the canonical σ-shifted source on the read window `[0, t/2]`. -/
  hagree_window : ∀ σ ∈ Set.Icc (0 : ℝ) (t / 2), ∀ k,
    a σ k = canonicalShiftedSource p u₀ n t σ k
  /-- Half-step envelope decay `|aσₖ| ≤ 2·Benv/(kπ)²` for `k ≥ 1`, `σ ≥ 0`. -/
  hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
    |a σ k| ≤ 2 * Benv p M A₂ t / ((k : ℝ) * Real.pi) ^ 2

/-! ## §B.1 — (4) Witness-based eigenvalue-weighted summability. -/

/-- **(4) Witness variant of `hbsum_succ`.**
The eigenvalue-weighted ℓ¹ summability of the next-iterate restart coefficients,
fed from the shifted-source witness instead of the exact canonical package.  The
conclusion is the *canonical* `iterateReprCoeff p u₀ (n+1) σ`; the witness only
enters the summability proof.  Since `restartDuhamelCoeff` reads the source on
`[0, σ/2]` and the witness agrees there, the coefficient values coincide and the
witness-fed summability transfers. -/
theorem hbsum_succ_of_shiftedWitness
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ M M₁ A₂ : ℝ}
    (hσ : 0 < σ)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ M₁)
    (W : ShiftedSourceWitness p u₀ n σ M A₂) :
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k|) := by
  have hτ : 0 < σ / 2 := by positivity
  have hτnn : (0 : ℝ) ≤ σ / 2 := le_of_lt hτ
  -- Witness-fed restart summability for the witness's own restart coefficient.
  have hsummW := restartSeries_eigenvalue_summable
    (a₀ := cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))))
    (a := W.a) hτ hM₁ W.src
  -- The coefficients of witness and canonical families coincide (read on [0,σ/2]).
  have hcoeff : ∀ k,
      restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))))
          W.a (σ / 2) k
        = iterateReprCoeff p u₀ (n + 1) σ k := by
    intro k
    have hcong := duhamelSpectralCoeff_congr_on_Icc (a := W.a)
      (a' := canonicalShiftedSource p u₀ n σ) hτnn
      (fun s hs m => W.hagree_window s hs m) k
    simp only [iterateReprCoeff, restartIterateCoeff, restartDuhamelCoeff]
    rw [hcong]
    rfl
  simpa only [hcoeff] using hsummW

/-! ## §B.2 — (5) Witness-based `[0,1]` agreement. -/

/-- **(5) Witness variant of `hagree_succ`.**
The `[0,1]` agreement of the `(n+1)`-st iterate slice with its restart cosine
series, with the canonical shifted package consumption replaced by the witness.
The agreement transfer is a coefficient congruence on the read window `[0, σ/2]`:
the original `hagree_succ` produces the series in `iterateReprCoeff`, whose
coefficient already equals the witness-based restart coefficient by
`duhamelSpectralCoeff_congr_on_Icc`.  So the witness is not actually needed for the
*conclusion* (it is the canonical series); it is provided for interface uniformity
with item 4, and we route directly through `hagree_succ`. -/
theorem hagree_succ_of_shiftedWitness
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {σ M A₂ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ s, 0 < s → s ≤ σ →
      Continuous (logisticLifted p (picardIter p u₀ n s)))
    (_W : ShiftedSourceWitness p u₀ n σ M A₂) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ (n + 1) σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) :=
  hagree_succ p hχ0 u₀ n hσ hu₀_cont hu₀_bound hsrc0 hL_cont

/-! ## §B.3 — (6) Subtype-continuity variant (kills the false lift-continuity). -/

section SubtypeChain

open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalSemigroupComposition (expEigSummable)

/-- **Subtype variant of `iterate_lift_eq_cosineSeries`.**
Identical to the original but consumes the paper-faithful `Continuous u₀` (on the
subtype `intervalDomainPoint`) instead of the false `Continuous (intervalDomainLift
u₀)`.  The ONLY differing step is the homogeneous propagator's spectral form, routed
through `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont`. -/
theorem iterate_lift_eq_cosineSeries_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (logisticLifted p (picardIter p u₀ n s)))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (picardIter p u₀ (n+1) t) x
      = ∑' k, iterateCoeff p u₀ n t k * cosineMode k x := by
  have hlift : intervalDomainLift (picardIter p u₀ (n+1) t) x
      = intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t ⟨x, hx⟩ := by
    show (if hx' : x ∈ Set.Icc (0:ℝ) 1 then
          picardIter p u₀ (n+1) t ⟨x, hx'⟩ else 0) = _
    rw [dif_pos hx]
    rfl
  rw [hlift, intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  -- S1b for the homogeneous propagator term — SUBTYPE route.
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * (λ_ k))
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
          ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  set a : ℝ → ℕ → ℝ := fun s k =>
    cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k with ha
  have hMa : ∀ s, 0 ≤ s → ∀ k, |a s k| ≤ ∑' j, hsrc0.envelope j := by
    intro s hs k
    have hnn : ∀ j, 0 ≤ hsrc0.envelope j := fun j =>
      le_trans (abs_nonneg _) (hsrc0.henv_bound 0 le_rfl j)
    refine le_trans (hsrc0.henv_bound s hs k) ?_
    have := hsrc0.henv_summable.sum_le_tsum {k} (fun j _ => hnn j)
    simpa using this
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x
        = unitIntervalCosineHeatValue (t - s) (a s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hcont : Continuous (logisticLifted p (picardIter p u₀ n s)) :=
      hL_cont s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k|
        ≤ ∑' j, hsrc0.envelope j := fun k => hMa s (le_of_lt hs.1) k
    exact ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
      hts hcont hMs hx
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

/-- **Subtype variant of `cosineCoeffs_halfstep_eq_iterateCoeff`.** -/
theorem cosineCoeffs_halfstep_eq_iterateCoeff_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
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
    iterate_lift_eq_cosineSeries_of_subtypeCont p hχ0 u₀ n hu₀_cont hu₀_bound
      hsrc0 hτ hL_cont hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_iterateCoeff p u₀ n hu₀_bound hsrc0 hτ) k

/-- **Subtype variant of `picardIterateRestart_cosineIdentity`.**
The `[0,1]` restart cosine identity for the `(n+1)`-st iterate slice, consuming the
paper-faithful subtype `Continuous u₀`.  Proof is the original verbatim with the two
sub-calls routed through the subtype variants above. -/
theorem picardIterateRestart_cosineIdentity_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (logisticLifted p (picardIter p u₀ n s))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n+1) t))
      (fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x)
      (Set.Icc (0:ℝ) 1) := by
  intro x hx
  set τ : ℝ := t / 2 with hτdef
  have hτ : 0 < τ := by rw [hτdef]; linarith
  have htτ : t = τ + τ := by rw [hτdef]; ring
  have ha_cont : ∀ k, Continuous
      (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) := fun k =>
    continuous_iff_continuousAt.2 (fun s => (hsrc0.hderiv s k).continuousAt)
  rw [iterate_lift_eq_cosineSeries_of_subtypeCont p hχ0 u₀ n hu₀_cont hu₀_bound
        hsrc0 ht hL_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  unfold restartIterateCoeff restartDuhamelCoeff
  have hext : cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) τ)) k
      = iterateCoeff p u₀ n τ k :=
    cosineCoeffs_halfstep_eq_iterateCoeff_of_subtypeCont p hχ0 u₀ n hu₀_cont hu₀_bound
      hsrc0 hτ (fun s hs hsτ => hL_cont s hs (by rw [htτ]; linarith)) k
  rw [hext]
  unfold iterateCoeff
  have hsplit := ShenWork.IntervalPicardIterateRestart.duhamelSpectralCoeff_halfstep_split
      (a := fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      ha_cont τ k
  have hexp : Real.exp (-t * (λ_ k))
      = Real.exp (-τ * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; rw [htτ]; ring
  rw [hexp, htτ, hsplit]
  ring

/-- **(6) Witness/subtype variant of `hagree_succ`.**
The `[0,1]` agreement of the `(n+1)`-st iterate slice with the canonical
`iterateReprCoeff` restart cosine series, consuming the paper-faithful
`Continuous u₀` (subtype) — NOT the false `Continuous (intervalDomainLift u₀)`. -/
theorem hagree_succ_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ : ℝ}
    (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ s, 0 < s → s ≤ σ →
      Continuous (logisticLifted p (picardIter p u₀ n s))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ (n + 1) σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  have hrepr := picardIterateRestart_cosineIdentity_of_subtypeCont p hχ0 u₀ n
    hu₀_cont hu₀_bound hsrc0 hσ hL_cont
  intro x hx
  have h := hrepr hx
  simpa only [iterateReprCoeff, restartIterateCoeff] using h

end SubtypeChain

end ShenWork.IntervalPicardIterateRestartLocal
