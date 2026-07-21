import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Two-sided band viability threshold `χ < √(c/2)`

Fable R1 (2026-07-21) derived the two-sided crest threshold.  For a symmetric
band `[1−δ, 1+δ]` (so the oscillation is `w = 2δ`), the crest gradient bound is
`K = χ w / (c − χ w) = 2χδ/(c − 2χδ)`.  The floor barrier `1 − a = δ ≥ χ K` and
the ceiling barrier `b − 1 = δ ≥ χ K` are the SAME condition, and

`δ ≥ χ K = χ · 2χδ/(c − 2χδ)  ⟺  c ≥ 2χ² + 2χδ`   (for `0 < δ`, `2χδ < c`).

So the band is forward-viable iff `c ≥ 2χ² + 2χδ`; a nonempty viable band
(`δ > 0`) exists iff `c > 2χ²`, i.e.

`χ < √(c/2)`.

At `c ≈ 2.9` this is `χ < 1.20`, strictly past the paper's `χ* = 1`.  This file
records those two algebraic facts.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The symmetric-band barrier `δ ≥ χ K`, with `K = 2χδ/(c − 2χδ)`, is equivalent
to `c ≥ 2χ² + 2χδ`. -/
theorem band_barrier_iff {χ δ c : ℝ} (_hχ : 0 < χ) (hδ : 0 < δ)
    (hden : 2 * χ * δ < c) :
    χ * (2 * χ * δ / (c - 2 * χ * δ)) ≤ δ ↔ 2 * χ ^ 2 + 2 * χ * δ ≤ c := by
  have hD : 0 < c - 2 * χ * δ := by linarith
  rw [← mul_div_assoc, div_le_iff₀ hD]
  constructor
  · intro h; nlinarith [h, hδ]
  · intro h; nlinarith [h, hδ.le]

/-- A nonempty viable symmetric band exists iff `χ < √(c/2)`. -/
theorem viable_band_threshold {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < c) :
    2 * χ ^ 2 < c ↔ χ < Real.sqrt (c / 2) := by
  have hc2 : 0 < c / 2 := by linarith
  constructor
  · intro h
    have hχ2 : χ ^ 2 < c / 2 := by linarith
    have := Real.sqrt_lt_sqrt (sq_nonneg χ) hχ2
    rwa [Real.sqrt_sq hχ.le] at this
  · intro h
    have hsqnn : 0 ≤ Real.sqrt (c / 2) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (c / 2) ^ 2 = c / 2 := Real.sq_sqrt hc2.le
    nlinarith [h, hχ, hsqnn, hsq]

section AxiomAudit

#print axioms band_barrier_iff
#print axioms viable_band_threshold

end AxiomAudit

end ShenWork.Paper1
