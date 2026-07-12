import ShenWork.Paper2.IntervalBFormNegativePartCron2
import ShenWork.Paper2.IntervalRpowLipschitz

/-!
# Truncated logistic Lipschitz difference (the missing HD-logistic atom)

The `HD` producer's `logisticDiff` field needs a Lipschitz difference bound for the
**truncated** logistic reaction `truncatedLogisticLocal p r = r·(a − b·(positivePart r)^α)`.
The in-repo `logistic_duhamel_diff_bound_of_ball` is for the *untruncated* `logisticLifted`
under a nonnegativity hypothesis — and since the truncated reaction keeps `r` (not
`positivePart r`) as its leading factor, the two differ for sign-changing `r`, so that
lemma does not apply.  This file supplies the genuinely-missing atom.

Route (identity-free): with `g := positivePart` (1-Lipschitz, `0 ≤ g r ≤ M` on the ball),
split `r·g(r)^α − r'·g(r')^α = (r−r')·g(r)^α + r'·(g(r)^α − g(r')^α)` and bound each factor:
`g(r)^α ≤ M^α`, `|r'| ≤ M`, and `|g(r)^α − g(r')^α| ≤ L_rpow·|g(r)−g(r')| ≤ L_rpow·|r−r'|`
(from `rpow_lipschitz_on_Icc_nonneg`, `α ≥ 1`, and `positivePart` 1-Lipschitz).  Self-contained.
-/

namespace ShenWork.Paper2.TruncatedLogisticLipschitz

open ShenWork.Paper2
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.IntervalDomain

/-- **Truncated logistic reaction is Lipschitz on `[-M, M]`** (the missing HD atom).
`|truncatedLogisticLocal p r − truncatedLogisticLocal p r'| ≤ L·|r − r'|` with an
explicit `L = a + b·(M^α + M·L_rpow)`, for `|r|,|r'| ≤ M` — no nonnegativity needed. -/
theorem truncatedLogisticLocal_lipschitz_on_bounded
    (p : CM2Params) (hα : 1 ≤ p.α) {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r r' : ℝ, |r| ≤ M → |r'| ≤ M →
      |truncatedLogisticLocal p r - truncatedLogisticLocal p r'| ≤ L * |r - r'| := by
  obtain ⟨Lp, hLp_nn, hLp⟩ := ShenWork.Paper2.rpow_lipschitz_on_Icc_nonneg hα hM
  have hMα_nn : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  refine ⟨p.a + p.b * (M ^ p.α + M * Lp), ?_, ?_⟩
  · have h1 : 0 ≤ M ^ p.α + M * Lp := add_nonneg hMα_nn (mul_nonneg hM hLp_nn)
    exact add_nonneg p.ha (mul_nonneg p.hb h1)
  · intro r r' hr hr'
    -- positive parts: nonneg, ≤ M, 1-Lipschitz
    have hgr_nn : 0 ≤ positivePart r := le_max_right _ _
    have hgr'_nn : 0 ≤ positivePart r' := le_max_right _ _
    have hgr_le : positivePart r ≤ M := max_le (le_trans (le_abs_self r) hr) hM
    have hgr'_le : positivePart r' ≤ M := max_le (le_trans (le_abs_self r') hr') hM
    have hpr_nn : 0 ≤ positivePart r ^ p.α := Real.rpow_nonneg hgr_nn _
    have hpr_le : positivePart r ^ p.α ≤ M ^ p.α :=
      Real.rpow_le_rpow hgr_nn hgr_le (by linarith)
    have hpos_lip : |positivePart r - positivePart r'| ≤ |r - r'| := by
      simpa [positivePart] using abs_max_sub_max_le_abs r r' 0
    have hpow_diff :
        |positivePart r ^ p.α - positivePart r' ^ p.α| ≤ Lp * |r - r'| :=
      le_trans (hLp _ _ hgr_nn hgr_le hgr'_nn hgr'_le)
        (mul_le_mul_of_nonneg_left hpos_lip hLp_nn)
    -- key: |r·g(r)^α − r'·g(r')^α| ≤ (M^α + M·Lp)·|r−r'|
    have hkey : |r * positivePart r ^ p.α - r' * positivePart r' ^ p.α|
        ≤ (M ^ p.α + M * Lp) * |r - r'| := by
      have hsplit : r * positivePart r ^ p.α - r' * positivePart r' ^ p.α
          = (r - r') * positivePart r ^ p.α
            + r' * (positivePart r ^ p.α - positivePart r' ^ p.α) := by ring
      rw [hsplit]
      have hb1 : |(r - r') * positivePart r ^ p.α| ≤ |r - r'| * M ^ p.α := by
        rw [abs_mul, abs_of_nonneg hpr_nn]
        exact mul_le_mul_of_nonneg_left hpr_le (abs_nonneg _)
      have hb2 : |r' * (positivePart r ^ p.α - positivePart r' ^ p.α)|
          ≤ M * (Lp * |r - r'|) := by
        rw [abs_mul]
        exact mul_le_mul hr' hpow_diff (abs_nonneg _) hM
      calc |(r - r') * positivePart r ^ p.α
              + r' * (positivePart r ^ p.α - positivePart r' ^ p.α)|
          ≤ |(r - r') * positivePart r ^ p.α|
              + |r' * (positivePart r ^ p.α - positivePart r' ^ p.α)| := abs_add_le _ _
        _ ≤ |r - r'| * M ^ p.α + M * (Lp * |r - r'|) := add_le_add hb1 hb2
        _ = (M ^ p.α + M * Lp) * |r - r'| := by ring
    -- assemble: T(r)−T(r') = a·(r−r') − b·(r·g(r)^α − r'·g(r')^α)
    have hTexp : truncatedLogisticLocal p r - truncatedLogisticLocal p r'
        = p.a * (r - r')
          - p.b * (r * positivePart r ^ p.α - r' * positivePart r' ^ p.α) := by
      simp only [truncatedLogisticLocal]; ring
    rw [hTexp]
    have htri := abs_add_le (p.a * (r - r'))
      (-(p.b * (r * positivePart r ^ p.α - r' * positivePart r' ^ p.α)))
    rw [← sub_eq_add_neg, abs_neg] at htri
    have ha1 : |p.a * (r - r')| = p.a * |r - r'| := by
      rw [abs_mul, abs_of_nonneg p.ha]
    have hb3 : |p.b * (r * positivePart r ^ p.α - r' * positivePart r' ^ p.α)|
        ≤ p.b * ((M ^ p.α + M * Lp) * |r - r'|) := by
      rw [abs_mul, abs_of_nonneg p.hb]
      exact mul_le_mul_of_nonneg_left hkey p.hb
    calc |p.a * (r - r')
            - p.b * (r * positivePart r ^ p.α - r' * positivePart r' ^ p.α)|
        ≤ |p.a * (r - r')|
            + |p.b * (r * positivePart r ^ p.α - r' * positivePart r' ^ p.α)| := htri
      _ ≤ p.a * |r - r'| + p.b * ((M ^ p.α + M * Lp) * |r - r'|) := by
          rw [ha1]; linarith [hb3]
      _ = (p.a + p.b * (M ^ p.α + M * Lp)) * |r - r'| := by ring

/-- **Lifted form**: the truncated logistic Lipschitz difference for the lifted
sources `truncatedLogisticLifted p u`, `truncatedLogisticLifted p w`, pointwise in `y`,
from a pointwise bound `|lift u|,|lift w| ≤ M`.  This is the per-slice source-difference
input for the `logisticDiff` Duhamel bound. -/
theorem truncatedLogisticLifted_lipschitz_of_lift_bound
    (p : CM2Params) (hα : 1 ≤ p.α) {M : ℝ} (hM : 0 ≤ M)
    {u w : intervalDomainPoint → ℝ}
    (hu : ∀ y, |intervalDomainLift u y| ≤ M) (hw : ∀ y, |intervalDomainLift w y| ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ,
      |truncatedLogisticLifted p u y - truncatedLogisticLifted p w y|
        ≤ L * |intervalDomainLift u y - intervalDomainLift w y| := by
  obtain ⟨L, hL_nn, hL⟩ := truncatedLogisticLocal_lipschitz_on_bounded p hα hM
  exact ⟨L, hL_nn, fun y => by
    simpa [truncatedLogisticLifted] using hL _ _ (hu y) (hw y)⟩

end ShenWork.Paper2.TruncatedLogisticLipschitz
