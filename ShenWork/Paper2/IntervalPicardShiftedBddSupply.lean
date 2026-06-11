/-
  ShenWork/Paper2/IntervalPicardShiftedBddSupply.lean

  **K1 endgame W2 — the `hagree_succ` BddOn mirror (`hsrc0`-free).**

  The tower's `(n+1)`-level representation agreement `hagree_succ` was proved by
  `IntervalPicardSourceSubtypeCont.hagree_succ_of_sourceSubtypeCont`, which consumes
  the canonical level-`n` `DuhamelSourceTimeC1` package `hsrc0` (the unfillable
  global ℓ¹-at-`s = 0` residual).  This file reproves it against the SATISFIABLE
  patched bounded-source package `DuhamelSourceBddOn (patchedSource …) T`, using the
  half-step specialisation (`τ = σ/2`, `s = σ`) of the general BddOn restart EqOn
  `IntervalPicardIterateBddRepr.picardIterateRestart_general_of_sourceBdd`.

  The coefficient bridge is definitional: `iterateReprCoeff (n+1) σ k =
  restartIterateCoeff p u₀ n σ k = restartDuhamelCoeff (coeffs(iter(n+1) (σ/2)))
  (σ/2-shifted source) (σ/2) k`, and `restartDuhamelCoeff` ≡ `localRestartCoeff`
  (identical bodies), while the general BddOn lemma at `τ = σ/2`, `s = σ` returns
  `localRestartCoeff (coeffs(iter(n+1) (σ/2))) (σ/2-shifted source) (σ − σ/2) k`
  with `σ − σ/2 = σ/2`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateBddRepr

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalPicardIterateBddRepr (picardIterateRestart_general_of_sourceBdd)

noncomputable section

namespace ShenWork.IntervalPicardShiftedBddSupply

/-- **`hagree_succ` BddOn mirror.**  The `[0,1]` agreement of the `(n+1)`-st iterate
slice with the canonical `iterateReprCoeff` restart cosine series, consuming the
SATISFIABLE patched bounded-source package `src` (and the satisfiable source-slice
subtype continuity `hLs_cont`) instead of the canonical `hsrc0`. -/
theorem hagree_succ_of_sourceBdd
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {σ : ℝ}
    (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {T : ℝ} (src : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) T)
    (hσT : σ ≤ T)
    (hLs_cont : ∀ s, 0 < s → s ≤ σ →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ (n + 1) σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  -- offset `τ = σ/2`, target `s = σ`; `s − τ = σ/2`.
  have hτpos : 0 < σ / 2 := by positivity
  have hτs : σ / 2 < σ := by linarith
  have hsub : σ - σ / 2 = σ / 2 := by ring
  -- the general BddOn restart EqOn at `(τ, s) = (σ/2, σ)`.
  have hgen := picardIterateRestart_general_of_sourceBdd p hχ0 u₀ n hu₀_cont hu₀_bound
    src hτpos hτs hσT
    (fun r hr hrσ => hLs_cont r hr hrσ)
  -- bridge the general restart coefficient to `iterateReprCoeff (n+1)` (definitional).
  intro x hx
  have h := hgen hx
  -- `localRestartCoeff … (σ − σ/2) ≡ restartDuhamelCoeff … (σ/2) = restartIterateCoeff`.
  rw [hsub] at h
  -- `iterateReprCoeff (n+1) σ = restartIterateCoeff p u₀ n σ` (def), and the latter is
  -- `restartDuhamelCoeff (coeffs(iter(n+1) (σ/2))) (σ/2-shifted source) (σ/2)`, which
  -- equals `localRestartCoeff (...) (...) (σ/2)` (identical bodies) — `simpa` with the
  -- two unfoldings closes the coefficient identity.
  simpa only [iterateReprCoeff, restartIterateCoeff,
    ShenWork.IntervalMildRegularityBootstrap.restartDuhamelCoeff, localRestartCoeff] using h

end ShenWork.IntervalPicardShiftedBddSupply
