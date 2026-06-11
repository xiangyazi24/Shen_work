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

end ShenWork.Paper2.CanonicalSourceLedgerBeyondAudit
