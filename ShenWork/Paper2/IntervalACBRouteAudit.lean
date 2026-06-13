import ShenWork.Paper2.IntervalBC2H3EResolverAudit

/-!
# ACB route audit

This module keeps the ACB branch pinned to proved interfaces while the raw
clamped source envelope is worked on.
-/

noncomputable section

namespace ShenWork.Paper2.ACBRouteAudit

open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.PicardLimitK1C2Coeff (SourceC2CoeffFields)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

variable {p : CM2Params}
variable {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
variable {T σ : ℝ}

/-- Route A's positive-time fact is about the restart target shift. -/
theorem routeA_target_shift_pos (L : LocalRestart p u T σ) :
    0 < σ - L.τ :=
  ShenWork.Paper2.BC2H3EResolverAudit.local_restart_target_shift_pos L

/-- The source-side C2 package required by BC2 is attached to raw `aC`. -/
abbrev routeA_raw_source_need (L : LocalRestart p u T σ) : Type :=
  SourceC2CoeffFields L.srcC

/-- Heat-factor bounds close the raw-source need when they are available for
the source and its coefficient derivative. -/
def routeA_fields_of_bounds
    {a : ℝ → ℕ → ℝ} {src : DuhamelSourceTimeC1 a}
    {eps M Mdot : ℝ} (heps : 0 < eps) (hM : 0 ≤ M)
    (hMdot : 0 ≤ Mdot)
    (hsrc : ∀ s, 0 ≤ s → ∀ n,
      |a s n| ≤ Real.exp (-eps * unitIntervalCosineEigenvalue n) * M)
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |src.adot s n| ≤ unitIntervalCosineEigenvalue n *
        Real.exp (-eps * unitIntervalCosineEigenvalue n) * Mdot) :
    SourceC2CoeffFields src :=
  ShenWork.Paper2.BC2H3EResolverAudit.source_fields_of_heat_factor_bounds
    heps hM hMdot hsrc hadot

/-- Route B must provide the same source fields, but by a polynomial envelope
for raw `aC` rather than by the restart target heat factor. -/
def routeB_fields_close_raw_source
    (L : LocalRestart p u T σ) (F : SourceC2CoeffFields L.srcC) :
    routeA_raw_source_need L :=
  F

/-- The committed quadratic source decay gives only a bounded one-eigenvalue
tail, so it is not by itself the BC2 source envelope. -/
theorem committed_quadratic_one_weight_only
    {a : ℕ → ℝ} {C : ℝ}
    (hdecay : ∀ k : ℕ, 1 ≤ k →
      |a k| ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k * |a k| ≤ C :=
  ShenWork.Paper2.ClampedK1SourceCubicBootstrap.committedQuadratic_oneEigenvalue_le_const
    hdecay hk

end ShenWork.Paper2.ACBRouteAudit
