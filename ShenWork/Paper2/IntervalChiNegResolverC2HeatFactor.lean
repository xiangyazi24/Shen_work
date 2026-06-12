import ShenWork.Paper2.IntervalPicardLimitK1C2Heat
import ShenWork.Paper2.IntervalResolverSpectralAgreementC2CoeffFromK1
import ShenWork.Paper2.IntervalChiNegResolverC2SourceAudit

/-!
# χ₀ < 0 resolver C2 heat-factor lane

This module records the positive-time heat-factor route in the vocabulary of
the χ₀ < 0 resolver audit.  The actual K1 restart is evaluated at a positive
shifted time.  The source-field theorem below applies to coefficient families
that themselves carry the heat factor `exp (-ε * λₙ)`.

It does not assert that the current clamped K1 source family `aC` has that
form; the existing `SourceC2CoeffFields` target is still the raw source family.
-/

noncomputable section

namespace ShenWork.Paper2.ChiNegResolverC2HeatFactor

open ShenWork.Paper2.PicardLimitK1C2Heat

/-- The K1 local restart used by the resolver is evaluated at a positive
shifted time at its target slice. -/
theorem localRestart_target_shift_pos
    {p : CM2Params}
    {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {T σ : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ) :
    0 < σ - L.τ := by
  linarith [L.hστ]

/-- Positive-shift heat smoothing gives the source-side C2 coefficient fields
from only a bounded coefficient datum. -/
def sourceC2CoeffFields_of_heatFactor
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields
      (shiftedHeatCoeff_timeC1 hε hM ha₀) :=
  shiftedHeatCoeff_sourceC2CoeffFields hε hM ha₀

/-- The corresponding base `DuhamelSourceTimeC2Coeff` package. -/
def c2Coeff_of_heatFactor
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff
      (shiftedHeatCoeff ε a₀) :=
  shiftedHeatCoeff_c2Coeff hε hM ha₀

end ShenWork.Paper2.ChiNegResolverC2HeatFactor
