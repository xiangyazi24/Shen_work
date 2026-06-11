/-
  ShenWork/Paper2/IntervalPicardSuccTowerLegs.lean

  **K1 endgame W3 (Deliverable 2) — the assembled `tower_succ` replacements.**

  `tower_succ` (IntervalPicardSourceTower) currently feeds the canonical level-`n`
  source `H.hsrc0 n` (via `shiftedSource_timeC1`) into two sites:

    * `hrepr_sum` (line ~452) = `hbsum_succ … (hsrcσ σ hσ)`;
    * the G2 interior branch (line ~498) = `iterate_abs_deriv2_le_of_windowDecay …
      (hsrcσ σ hσ) (hdecayW σ hσ hσT) x`.

  This file assembles the `hsrc0`-FREE replacements, built from `winAdot` data only,
  so that W4 (the `TowerInputs.hsrc0` field deletion) is a pure wiring pass: swap the
  two `have hrepr_sum`/G2-interior bodies for these.  Both internally:

    1. build the GLOBAL clamped σ/2-shifted source package + read-window agreement on
       `[0, σ/2]` via the W3 brick `clampedShiftedSource_duhamelSourceTimeC1`;
    2. derive the windowed decay on `[0, σ/2]` via stage F `shifted_source_windowDecay`;
    3. invoke the consumer variants `hbsum_succ_of_window` /
       `iterate_abs_deriv2_le_of_window` (IntervalPicardSuccLegsOfWinAdot).

  HONEST SCOPE: the W3 brick needs `σ < T` STRICT (the clamp pad `[σ/4,(σ+T)/2]` has
  room above the id-zone `[σ/2,σ]` only when `σ < T`).  These legs are therefore
  delivered on `0 < σ → σ < T`.  The `σ = T` endpoint is the documented terminal
  residual (W2 STATUS leftover (D)); W4 must split the `σ ≤ T` quantifier
  accordingly (or carry the `σ = T` slice through the surviving canonical route).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardSuccLegsOfWinAdot
import ShenWork.Paper2.IntervalPicardUniformWiringDischarge

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff)
open ShenWork.IntervalPicardIterateUniform (Benv G1profile G2profile)
open ShenWork.IntervalPicardUniformWiringDischarge (Benv_nonneg)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardWindowAdot (WindowAdotLegs)
open ShenWork.IntervalPicardShiftedClampedSupply (clampedShiftedSource_duhamelSourceTimeC1)
open ShenWork.IntervalPicardSliceWitnessSupply (shifted_source_windowDecay)
open ShenWork.IntervalPicardSuccLegsOfWinAdot
  (hbsum_succ_of_window iterate_abs_deriv2_le_of_window)

noncomputable section

namespace ShenWork.IntervalPicardSuccTowerLegs

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **The level-`n` data bundle for the assembled legs.**  Exactly the level-`n`
facts `tower_succ` has in scope from `TowerLevel n` / `TowerInputs` MINUS `hsrc0`,
plus the level-`n` `winAdot` legs.  Bundling keeps the two assembled legs (and the
eventual W4 wiring) a clean record fill. -/
structure SuccLegData (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (M A₂ T : ℝ) : Prop where
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  hMnn : 0 ≤ M
  hA₂nn : 0 ≤ A₂
  hrepr_sum : ∀ s, 0 < s → s ≤ T →
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ n s k|)
  hrepr_agree : ∀ s, 0 < s → s ≤ T →
    Set.EqOn (intervalDomainLift (picardIter p u₀ n s))
      (fun x => ∑' k, iterateReprCoeff p u₀ n s k * cosineMode k x) (Set.Icc (0 : ℝ) 1)
  hpos : ∀ s, 0 < s → s ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift (picardIter p u₀ n s) x
  hub : ∀ s, 0 < s → s ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    intervalDomainLift (picardIter p u₀ n s) x ≤ M
  hG1 : ∀ s, 0 < s → s ≤ T → ∀ x : ℝ,
    |deriv (intervalDomainLift (picardIter p u₀ n s)) x| ≤ G1profile p M s
  hG2 : ∀ s, 0 < s → s ≤ T → ∀ x : ℝ,
    |deriv (deriv (intervalDomainLift (picardIter p u₀ n s))) x| ≤ G2profile A₂ s
  winAdot : ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → WindowAdotLegs p u₀ n lo hi

/-- **The σ/2-shifted clamped package + read-window agreement, packaged.**
For `0 < σ < T`, the W3 brick fed by `SuccLegData`. -/
theorem shiftedPackage_of_succLegData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {M A₂ T : ℝ}
    (D : SuccLegData p u₀ n M A₂ T) {σ : ℝ} (hσ : 0 < σ) (hσT : σ < T) :
    ∃ asrc : ℝ → ℕ → ℝ, ∃ _ : DuhamelSourceTimeC1 asrc,
      ∀ s ∈ Set.Icc (0 : ℝ) (σ / 2), ∀ k,
        asrc s k = cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k :=
  clampedShiftedSource_duhamelSourceTimeC1 p u₀ n D.hα D.ha D.hb D.hMnn D.hA₂nn hσ hσT
    D.hrepr_sum D.hrepr_agree D.hpos D.hub D.hG1 D.hG2 D.winAdot

/-! ## §1 — (A) the assembled `hrepr_sum` leg. -/

/-- **`hrepr_sum_succ_of_winAdot` — the `tower_succ` `hrepr_sum` site, `hsrc0`-free.**
λ-weighted summability of `iterateReprCoeff (n+1) σ` from `winAdot` data, for the
half-step bound `hM₁`, on `0 < σ < T`. -/
theorem hrepr_sum_succ_of_winAdot
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {M A₂ T : ℝ}
    (D : SuccLegData p u₀ n M A₂ T)
    (hM₁ : ∀ σ, 0 < σ → σ ≤ T → ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ 2 * M) :
    ∀ σ, 0 < σ → σ < T →
      Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ (n + 1) σ k|) := by
  intro σ hσ hσT
  obtain ⟨asrc, srcC, hagree⟩ := shiftedPackage_of_succLegData p u₀ n D hσ hσT
  exact hbsum_succ_of_window p u₀ n hσ (fun k => hM₁ σ hσ (le_of_lt hσT) k) srcC hagree

/-! ## §2 — (B) the assembled G2 engine leg. -/

/-- **`hG2_succ_engine_of_winAdot` — the `tower_succ` G2 interior site, `hsrc0`-free.**
The explicit second-derivative sup bound for the next-iterate restart series from
`winAdot` data, for the half-step bound `hM₁ = 2M`, on `0 < σ < T`.  This is exactly
the `hbound` that the G2 interior branch of `tower_succ` consumes (with `M₁ = 2M`). -/
theorem hG2_succ_engine_of_winAdot
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {M A₂ T : ℝ}
    (D : SuccLegData p u₀ n M A₂ T)
    (hM₁ : ∀ σ, 0 < σ → σ ≤ T → ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (σ / 2))) k| ≤ 2 * M) :
    ∀ σ, 0 < σ → σ < T → ∀ x : ℝ,
      |deriv (deriv (fun z => ∑' k, restartIterateCoeff p u₀ n σ k * cosineMode k z)) x|
        ≤ 2 * M * eigExpWeight (σ / 2)
          + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
              Real.pi ^ ((3 : ℝ) / 2)) * (σ / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ σ := by
  intro σ hσ hσT x
  have hBenv : 0 ≤ Benv p M A₂ σ := Benv_nonneg D.hMnn
  obtain ⟨asrc, srcC, hagree⟩ := shiftedPackage_of_succLegData p u₀ n D hσ hσT
  -- windowed decay on `[0, σ/2]` (stage F, `winAdot`-free: level-`n` repr/ball/K2).
  have hdecayW : ∀ s ∈ Set.Icc (0 : ℝ) (σ / 2), ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n (σ / 2 + s))) k|
        ≤ 2 * Benv p M A₂ σ / ((k : ℝ) * Real.pi) ^ 2 :=
    shifted_source_windowDecay p u₀ n D.hα D.hMnn D.hA₂nn hσ (le_of_lt hσT)
      (iterateReprCoeff p u₀ n) D.hrepr_sum D.hrepr_agree D.hpos D.hub D.hG1 D.hG2
  exact iterate_abs_deriv2_le_of_window p u₀ n hσ hBenv
    (fun k => hM₁ σ hσ (le_of_lt hσT) k) srcC hagree hdecayW x

end ShenWork.IntervalPicardSuccTowerLegs
