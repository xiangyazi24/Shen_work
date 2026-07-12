/-
  ShenWork/Paper3/IntervalDomainWeightedYoung.lean

  **Fable roadmap D / L7 — the weighted Young inequality driving the chemotaxis
  cross-term absorption in the entropy dissipation.**

  In `dH/dt` the indefinite chemotaxis term `χ₀∫(1+v)^{-β}∇u·∇v` is absorbed by
  Young against the good dissipation `∫|∇u|²/u`:
    |χ₀(1+v)^{-β}∇u·∇v| ≤ ½∫|∇u|²/u + (χ₀²/2)∫u(1+v)^{-2β}|∇v|².
  The pointwise engine is the scalar **weighted Young** `|A·B| ≤ A²/(2w)+wB²/2`
  (`w>0`), from `(|A|−w|B|)² ≥ 0`.  Choosing the weight `w = 1/u` matches the good
  term; the leftover `(χ₀²/2)∫u(1+v)^{-2β}|∇v|²` is then dominated by the modal
  Poincaré gain under the `χ₀ < chiBeta` threshold.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace ShenWork.Paper3.WeightedYoung

/-- **Weighted Young inequality (Fable D/L7 core):** `|A · B| ≤ A²/(2w) + w·B²/2`
for any weight `w > 0`.  From `(|A| − w|B|)² ≥ 0`. -/
theorem weighted_young {A B w : ℝ} (hw : 0 < w) :
    |A * B| ≤ A ^ 2 / (2 * w) + w * B ^ 2 / 2 := by
  have hab : |A * B| = |A| * |B| := abs_mul A B
  have hA2 : |A| ^ 2 = A ^ 2 := sq_abs A
  have hB2 : |B| ^ 2 = B ^ 2 := sq_abs B
  have hpos : 0 ≤ (|A| - w * |B|) ^ 2 / (2 * w) := by positivity
  have hid : A ^ 2 / (2 * w) + w * B ^ 2 / 2 - |A| * |B|
      = (|A| - w * |B|) ^ 2 / (2 * w) := by
    rw [← hA2, ← hB2]
    field_simp
    ring
  rw [hab]
  linarith [hid, hpos]

end ShenWork.Paper3.WeightedYoung
