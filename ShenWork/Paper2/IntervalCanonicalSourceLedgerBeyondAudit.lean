import ShenWork.Paper2.IntervalCanonicalSourceOnFromLedger
import ShenWork.Paper2.IntervalMildPicard

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.Paper2.CanonicalSourceOnFromLedger (CanonicalSourceLedgerBeyond)

noncomputable section

namespace ShenWork.Paper2.CanonicalSourceLedgerBeyondAudit

/-- Any beyond-ledger for a Picard iterate must prove that the iterate is a
self-solution for `intervalGradientDuhamelMap` on the larger horizon.  This is
the exact `CanonicalSourceLedger.hfix` projection. -/
theorem picardIterLedger_selfFix_obligation
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {T : ℝ}
    (L : CanonicalSourceLedgerBeyond p u₀ (picardIter p u₀ n) T) :
    ∀ s, 0 < s → s < L.U → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (picardIter p u₀ n s) x =
          intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) s ⟨x, hx⟩ :=
  L.ledger.hfix

/-- What the Picard recursion actually gives: level `n+1` is produced from the
previous level `n`, not from itself.  This is the field that mirrors the tower's
available construction and pinpoints the index mismatch in the ledger target. -/
theorem picardIter_succ_previousSourceFix
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {U : ℝ} :
    ∀ s, 0 < s → s < U → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (picardIter p u₀ (n + 1) s) x =
          intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) s ⟨x, hx⟩ := by
  intro s _hs _hU x hx
  simp only [picardIter, intervalDomainLift, dif_pos hx]

/-- Predecessor-indexed Duhamel representation.  This is the shape actually
available for Picard successors. -/
def PredecessorFix
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u prev : ℝ → intervalDomainPoint → ℝ) (U : ℝ) : Prop :=
  ∀ s, 0 < s → s < U → ∀ x : ℝ,
    (hx : x ∈ Set.Icc (0 : ℝ) 1) →
      intervalDomainLift (u s) x =
        intervalGradientDuhamelMap p u₀ prev s ⟨x, hx⟩

/-- A predecessor fix becomes the old self-fix only after an extra agreement of
the two Duhamel maps.  This is the missing bridge for path A. -/
theorem PredecessorFix.to_selfFix_of_duhamelMap_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u prev : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (hprev : PredecessorFix p u₀ u prev U)
    (hmap : ∀ s, 0 < s → s < U → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u₀ prev s x =
        intervalGradientDuhamelMap p u₀ u s x) :
    ∀ s, 0 < s → s < U → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (u s) x =
          intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩ := by
  intro s hs hU x hx
  rw [hprev s hs hU x hx]
  exact hmap s hs hU ⟨x, hx⟩

/-- The successor iterate has the predecessor-indexed representation with the
previous Picard level as source. -/
theorem picardIter_succ_predecessorFix
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {U : ℝ} :
    PredecessorFix p u₀ (picardIter p u₀ (n + 1)) (picardIter p u₀ n) U :=
  picardIter_succ_previousSourceFix p u₀ n

end ShenWork.Paper2.CanonicalSourceLedgerBeyondAudit
