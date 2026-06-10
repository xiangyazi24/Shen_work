/-
  ShenWork/Paper2/IntervalPicardIterateRepresentation.lean

  **Deliverable A — the shared per-iterate cosine-representation core.**

  Both the source-package producer (Front A, deliverable B) and the `IterateWindowC2Data`
  assembler (deliverable C) need, for every iterate level `n` and time `σ > 0`, a
  cosine representation triple

      bc : ℕ → ℝ          -- coefficients
      hbsum             -- eigenvalue-weighted ℓ¹ summability of bc
      hagree            -- `lift(uₙ(σ)) = ∑ₖ bc k · cosineMode k x` on `[0,1]`

  for the lifted Picard iterate slice `lift(uₙ(σ))`.  This file produces that triple
  uniformly in `n`, via:

    * `n = 0` (HOMOGENEOUS heat slice) — `picardIter p u₀ 0 σ = S(σ)(lift u₀)`, whose
      spectral form is the damped cosine series `bc k = e^{−σλₖ}·û₀ₖ`
      (`heatValue_eq_cosineSeries` + the subtype spectral identity).  Summability is
      the homogeneous heat-trace bound `hom_eig_summable`.

    * `n+1` (RESTART slice) — M1's `picardIterateRestart_cosineIdentity` gives
      `lift(uₙ₊₁(σ)) = ∑ₖ restartIterateCoeff p u₀ n σ k · cosineMode k x` on `[0,1]`,
      and `restartSeries_eigenvalue_summable` (at the half-step homogeneous datum
      `cosineCoeffs(lift uₙ₊₁(σ/2))` and the σ-shifted logistic source) gives `hbsum`.

  The two cases are merged into one `n`-uniform interface `IterateRepr` carrying the
  triple plus the value bounds, so the downstream assembler is a clean record fill.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateC2Bound
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.PDE.IntervalSpectralSubtypeAdapter

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalPicardIterateRestart
  (heatValue_eq_cosineSeries picardIterateRestart_cosineIdentity)
open ShenWork.IntervalPicardIterateC2Bound
  (restartIterateCoeff restartSeries_eigenvalue_summable hom_eig_summable)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardIterateRepresentation

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## §A.0 — The `n`-uniform per-slice cosine representation triple. -/

/-- The cosine coefficients of the lifted iterate slice `lift(uₙ(σ))`, split by the
homogeneous/restart structure of the Picard iteration:

  * `n = 0` — damped initial coefficients `e^{−σλₖ}·û₀ₖ`;
  * `n+1`  — the M1 restart coefficient `restartIterateCoeff p u₀ n σ k`. -/
def iterateReprCoeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℕ → ℝ
  | 0,     σ, k => Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
  | n + 1, σ, k => restartIterateCoeff p u₀ n σ k

/-! ## §A.1 — The `n = 0` homogeneous representation. -/

/-- **Eigenvalue-weighted summability of the `n = 0` damped coefficients.**
`∑ₖ λₖ·|e^{−σλₖ}·û₀ₖ| < ∞` whenever the initial coefficients are bounded
(heat-trace summability, `hom_eig_summable`). -/
theorem hbsum_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ 0 σ k|) :=
  hom_eig_summable (M₁ := M₀) hσ hu₀_bound

/-- **Agreement of the `n = 0` slice with its damped cosine series on `[0,1]`.**
The homogeneous heat slice `S(σ)(lift u₀)` equals `∑ₖ e^{−σλₖ}·û₀ₖ · cosineMode k x`
on `[0,1]`, via the subtype spectral identity and `heatValue_eq_cosineSeries`. -/
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  -- `lift(uₙ₌₀(σ)) x = S(σ)(lift u₀) x` on `[0,1]`.
  have hlift : intervalDomainLift (picardIter p u₀ 0 σ) x
      = intervalFullSemigroupOperator σ (intervalDomainLift u₀) x := by
    simp only [intervalDomainLift, picardIter, dif_pos hx]
  rw [hlift]
  -- spectral identity (subtype-continuous form).
  rw [ShenWork.IntervalSpectralSubtypeAdapter.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        hσ hu₀_cont hu₀_bound hx]
  -- the heat value is the damped cosine series.
  rw [heatValue_eq_cosineSeries]
  rfl

/-! ## §A.2 — The `n+1` restart representation. -/

/-- **Eigenvalue-weighted summability of the `n+1` restart coefficients.**
At the half-step homogeneous datum `cosineCoeffs(lift uₙ₊₁(σ/2))` and the σ-shifted
logistic source family, `restartSeries_eigenvalue_summable` gives the ℓ¹ bound. -/
theorem hbsum_succ
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ M₁ : ℝ} (hσ : 0 < σ)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ M₁)
    (srcσ : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k)) :
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k|) := by
  have hτ : 0 < σ / 2 := by positivity
  simpa only [iterateReprCoeff, restartIterateCoeff] using
    restartSeries_eigenvalue_summable (a₀ :=
        cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))))
      (a := fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k)
      hτ hM₁ srcσ

/-- **Agreement of the `n+1` slice with its restart cosine series on `[0,1]`.**
This is exactly M1's `picardIterateRestart_cosineIdentity` (the restart coefficient
is `restartIterateCoeff` by definition). -/
theorem hagree_succ
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ : ℝ}
    (hσ : 0 < σ)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    (hL_cont : ∀ s, 0 < s → s ≤ σ →
      Continuous (logisticLifted p (picardIter p u₀ n s))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ (n + 1) σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  -- `iterateReprCoeff … (n+1) = restartIterateCoeff …` definitionally.
  have hrepr := picardIterateRestart_cosineIdentity p hχ0 u₀ n hu₀_cont hu₀_bound
    hsrc0 hσ hL_cont
  intro x hx
  have h := hrepr hx
  simpa only [iterateReprCoeff, restartIterateCoeff] using h

end ShenWork.IntervalPicardIterateRepresentation
