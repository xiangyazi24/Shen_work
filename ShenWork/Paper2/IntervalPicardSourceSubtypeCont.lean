/-
  ShenWork/Paper2/IntervalPicardSourceSubtypeCont.lean

  **Vacuity fix — the source-slice subtype-continuity leg.**

  The former `TowerInputs.hL_cont` / `TowerConeAnalyticResidual.hL_cont` demanded
  GLOBAL ℝ-continuity of the ZERO-EXTENSION `logisticLifted p (picardIter p u₀ n s)
  = intervalDomainLift (intervalLogisticSource p (picardIter p u₀ n s))`.  The cone
  returns STRICT positivity of the iterates on all of `Icc 0 1` (endpoints
  INCLUDED), so the source at `0`/`1` is generically nonzero and the zero-extension
  JUMPS — the field is UNSATISFIABLE.  This is the same false lift-continuity disease
  the §B.3 subtype variants (`IntervalPicardIterateRestartLocal`) already fixed for
  the homogeneous `u₀` leg; this file fixes the MISSED source-slice leg.

  Contents:
  * `logisticSource_subtypeCont` — the producer: from per-slice subtype continuity
    of the iterate (`HasContinuousSlices T (picardIter p u₀ n)`) + `1 ≤ p.α`, derive
    `Continuous (intervalLogisticSource p (picardIter p u₀ n s))` on the SUBTYPE for
    every `0 < s ≤ T`.  The formula `u·(a − b·u^α)` is continuous on the compact
    subtype `intervalDomainPoint` by `Continuous.rpow_const` with `0 ≤ α` (no
    positivity needed: the exponent branch suffices).
  * `iterate_lift_eq_cosineSeries_of_sourceSubtypeCont` — the swapped-step clone of
    `iterate_lift_eq_cosineSeries`: the `u₀` homogeneous leg routes through the
    subtype adapter (inherited from the `_of_subtypeCont` clone), and the Duhamel
    integrand step routes the source operand through the SUBTYPE adapter
    `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont` (since
    `logisticLifted p w` IS `intervalDomainLift (intervalLogisticSource p w)`
    definitionally).  The false `hL_cont` is replaced by the subtype
    `hLs_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s))`.
  * `cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceSubtypeCont`,
    `picardIterateRestart_cosineIdentity_of_sourceSubtypeCont`,
    `hagree_succ_of_sourceSubtypeCont` — the wrapper clones up the chain, mirroring
    the §B.3 subtype variants with the new source-subtype hypothesis.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateRestartLocal

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff duhamelSpectral_eq_cosineSeries)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalMildPicard (picardIter HasContinuousSlices)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardIterateRestart
  (iterateCoeff heatValue_eq_cosineSeries cosineCoeffs_of_l1_cosineSeries
   abs_duhamelSpectralCoeff_le summable_abs_iterateCoeff
   intervalGradientDuhamelMap_eq_of_chi0_zero)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardSourceSubtypeCont

local notation "λ_" n => unitIntervalCosineEigenvalue n

open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalSemigroupComposition (expEigSummable)

/-! ## §1 — The producer.

`intervalLogisticSource p w x = w x * (p.a − p.b * (w x) ^ p.α)`.  On the compact
subtype `intervalDomainPoint`, continuity of `w` (the iterate slice) gives
continuity of the source: the product/difference/scalar legs are routine, and the
`rpow` leg `x ↦ (w x) ^ p.α` is continuous by `Continuous.rpow_const` since
`0 ≤ p.α` (from `1 ≤ p.α`) — the nonneg-exponent branch needs no positivity. -/

/-- **Source subtype continuity from iterate slice continuity.**  If the iterate
slice `picardIter p u₀ n s` is continuous on the subtype (for `0 < s ≤ T`, the
`HasContinuousSlices` data), and `1 ≤ p.α`, then the logistic source
`intervalLogisticSource p (picardIter p u₀ n s)` is continuous on the subtype.
This is the SATISFIABLE replacement for the false `hL_cont` lift-continuity. -/
theorem logisticSource_subtypeCont
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hα : 1 ≤ p.α)
    (hslice : HasContinuousSlices T (picardIter p u₀ n)) :
    ∀ s, 0 < s → s ≤ T →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s)) := by
  intro s hs hsT
  have hw : Continuous (picardIter p u₀ n s) := hslice s hs hsT
  have hαnn : (0 : ℝ) ≤ p.α := le_trans zero_le_one hα
  have hrpow : Continuous (fun x : intervalDomainPoint => (picardIter p u₀ n s x) ^ p.α) :=
    hw.rpow_const (fun _ => Or.inr hαnn)
  unfold intervalLogisticSource
  exact hw.mul (continuous_const.sub (continuous_const.mul hrpow))

/-! ## §2 — The swapped-step clone of `iterate_lift_eq_cosineSeries`.

Verbatim copy of the original, with TWO steps rerouted:
  * the homogeneous `S(t)(lift u₀)` leg via the subtype adapter (so `Continuous u₀`
    on the subtype, not the false `Continuous (intervalDomainLift u₀)`);
  * the Duhamel integrand `S(t−s)(logisticLifted …)` leg via the subtype adapter
    applied to the source operand `intervalLogisticSource p (picardIter p u₀ n s)`
    (since `logisticLifted p w = intervalDomainLift (intervalLogisticSource p w)`
    definitionally), so the SATISFIABLE source-subtype continuity replaces the false
    lift continuity. -/

/-- **Source-subtype variant of `iterate_lift_eq_cosineSeries`.**  Consumes the
paper-faithful subtype `Continuous u₀` AND the satisfiable source-slice subtype
continuity `hLs_cont`, NOT the false `Continuous (logisticLifted …)`. -/
theorem iterate_lift_eq_cosineSeries_of_sourceSubtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t)
    (hLs_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s)))
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
  -- Pointwise spectral form of the Duhamel integrand on `Ioo 0 t` — SUBTYPE route
  -- for the source operand `intervalLogisticSource p (picardIter p u₀ n s)`, since
  -- `logisticLifted p w = intervalDomainLift (intervalLogisticSource p w)` (rfl).
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x
        = unitIntervalCosineHeatValue (t - s) (a s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hcont : Continuous (intervalLogisticSource p (picardIter p u₀ n s)) :=
      hLs_cont s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs
        (intervalDomainLift (intervalLogisticSource p (picardIter p u₀ n s))) k|
        ≤ ∑' j, hsrc0.envelope j := fun k => hMa s (le_of_lt hs.1) k
    have hsub := intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      (f := intervalLogisticSource p (picardIter p u₀ n s)) hts hcont hMs hx
    -- `logisticLifted p w = intervalDomainLift (intervalLogisticSource p w)` (rfl).
    exact hsub
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

/-- **Source-subtype variant of `cosineCoeffs_halfstep_eq_iterateCoeff`.** -/
theorem cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceSubtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {τ : ℝ} (hτ : 0 < τ)
    (hLs_cont : ∀ s, 0 < s → s ≤ τ →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s)))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) τ)) k
      = iterateCoeff p u₀ n τ k := by
  have hrepr : ∀ x ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n+1) τ) x
        = ∑' j, iterateCoeff p u₀ n τ j * cosineMode j x := fun x hx =>
    iterate_lift_eq_cosineSeries_of_sourceSubtypeCont p hχ0 u₀ n hu₀_cont hu₀_bound
      hsrc0 hτ hLs_cont hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_iterateCoeff p u₀ n hu₀_bound hsrc0 hτ) k

/-- **Source-subtype variant of `picardIterateRestart_cosineIdentity`.** -/
theorem picardIterateRestart_cosineIdentity_of_sourceSubtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t)
    (hLs_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s))) :
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
  rw [iterate_lift_eq_cosineSeries_of_sourceSubtypeCont p hχ0 u₀ n hu₀_cont hu₀_bound
        hsrc0 ht hLs_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  unfold restartIterateCoeff restartDuhamelCoeff
  have hext : cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) τ)) k
      = iterateCoeff p u₀ n τ k :=
    cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceSubtypeCont p hχ0 u₀ n hu₀_cont
      hu₀_bound hsrc0 hτ (fun s hs hsτ => hLs_cont s hs (by rw [htτ]; linarith)) k
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

/-- **Source-subtype variant of `hagree_succ`.**  The `[0,1]` agreement of the
`(n+1)`-st iterate slice with the canonical `iterateReprCoeff` restart cosine
series, consuming the paper-faithful `Continuous u₀` (subtype) AND the satisfiable
source-slice subtype continuity `hLs_cont` — NOT the false `Continuous
(logisticLifted …)`. -/
theorem hagree_succ_of_sourceSubtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ : ℝ}
    (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hLs_cont : ∀ s, 0 < s → s ≤ σ →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ (n + 1) σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  have hrepr := picardIterateRestart_cosineIdentity_of_sourceSubtypeCont p hχ0 u₀ n
    hu₀_cont hu₀_bound hsrc0 hσ hLs_cont
  intro x hx
  have h := hrepr hx
  simpa only [iterateReprCoeff, restartIterateCoeff] using h

end ShenWork.IntervalPicardSourceSubtypeCont
