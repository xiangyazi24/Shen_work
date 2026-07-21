import ShenWork.Paper1.WholeLineChiPosPointwiseCaptureStep

/-!
# The pointwise ceiling step: `max u` falls toward `1 + χ G`

The floor step (`pointwise_min_rise_of_oscillation_bound`) shows the minimum rises
toward `1` for `χ < (1−a)/G`.  This file is its symmetric counterpart at an
interior MAXIMUM `z**` of `u` (so `u_z(z**) = 0`, `u_zz(z**) ≤ 0`), with
`γ = α = 1` and the elliptic identity `v − u = v_zz`:

`u_t(z**) = u_zz(z**) + u(1 − u) − χ · u · (v − u)(z**)`.

At a maximum the chemotaxis defect is `(v − u)(z**) ≤ 0` (the smoothing average
lies below the peak), so `−χ u (v−u) ≥ 0` fights the reaction — this is why
overshoot (`max u > 1`) is spontaneously generated (verified numerically).  But
the overshoot is BOUNDED: using `u_zz ≤ 0` and `|(v−u)| ≤ G`,

`u_t(z**) ≤ b · ((1 − b) + χ G)`,   `b = u(z**)`,

which is `≤ 0` as soon as `b ≥ 1 + χ G`.  So the maximum is trapped at
`max u ≤ 1 + χ G`, and as the band tightens (`G → 0`, since `G` is the
oscillation/gradient bound `≤ b − a` or `≤ K`) the ceiling descends to `1`.  This
discharges the no-overshoot concern: `b ≤ 1` is false, but `b ≤ 1 + χ G` holds
and `→ 1`, which is what the (corrected) crest route needs.

**Scope:** scalar inequalities in the extremal-point data — `curv = u_zz(z**) ≤ 0`,
`react ≤ b(1−b)` (reaction upper bound at the peak), `uval = b`, `defect =
(v−u)(z**)` with `|defect| ≤ G`.  The interior-maximum facts and the oscillation
bound are hypotheses (same status as the floor step).
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- **Pointwise max-fall under an oscillation bound.**  At an interior maximum,
with nonpositive curvature, the reaction bounded above by its peak value, and the
chemotaxis defect controlled by `G`, the instantaneous rate is strictly negative
when `1 + χ G < b` — so the maximum falls toward `1 + χ G`. -/
theorem pointwise_max_fall_of_oscillation_bound
    {curv react uval b defect G χ : ℝ}
    (hb1 : 1 < b)
    (hcurv : curv ≤ 0)
    (huval : uval = b)
    (hreact : react ≤ b * (1 - b))
    (_hG : 0 ≤ G) (hdefect : |defect| ≤ G)
    (hχ0 : 0 ≤ χ)
    (hχ : 1 + χ * G < b) :
    curv + react - χ * uval * defect < 0 := by
  have hb0 : 0 < b := lt_trans one_pos hb1
  -- `-defect ≤ |defect| ≤ G`, and `uval = b > 0`, so `-χ·b·defect ≤ χ·b·G`
  have hdef_ge : -G ≤ defect := (abs_le.mp hdefect).1
  have hchem_le : -(χ * uval * defect) ≤ χ * b * G := by
    rw [huval]
    have h1 : χ * b * (-defect) ≤ χ * b * G := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hχ0 hb0.le)
      linarith
    nlinarith [h1]
  -- `curv + react - χ b defect ≤ 0 + b(1-b) + χ b G = b((1-b) + χ G) < 0`
  have hkey : b * ((1 - b) + χ * G) < 0 :=
    mul_neg_of_pos_of_neg hb0 (by linarith)
  nlinarith [hcurv, hreact, hchem_le, hkey]

/-- The ceiling trap value `1 + χ G` descends to `1` as the oscillation bound
`G → 0` (monotone in `G`). -/
theorem ceiling_trap_mono {χ G1 G2 : ℝ} (hχ : 0 ≤ χ) (hG : G1 ≤ G2) :
    1 + χ * G1 ≤ 1 + χ * G2 := by
  have : χ * G1 ≤ χ * G2 := mul_le_mul_of_nonneg_left hG hχ
  linarith

section AxiomAudit

#print axioms pointwise_max_fall_of_oscillation_bound
#print axioms ceiling_trap_mono

end AxiomAudit

end ShenWork.Paper1
