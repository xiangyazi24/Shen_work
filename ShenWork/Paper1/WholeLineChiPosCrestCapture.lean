import ShenWork.Paper1.WholeLineChiPosCrestGradientBound

/-!
# Crest capture: the min rises under the crest gradient bound

This chains the two hand-built pieces of the far-left pointwise route:

* `crest_gradient_bound`  : `‖u_z‖ ≤ K := χ b (b−a) / (c − χ(b−a))`;
* `pointwise_min_rise_of_oscillation_bound` : the min rises for `χ < (1−a)/G`.

Feeding `G = K` resolves the self-consistency `χ < (1−a)/K` into an explicit
QUADRATIC threshold in `χ` (Fable A's synthesis, 2026-07-21):

`χ < (1 − a)/K ⟺ χ² b (b−a) + χ (1−a)(b−a) − (1−a) c < 0`,

whose positive root is `χ_max(c) ~ √c` — numerically `1.7152` at the empirical
`a = 0.15, b = 1, c = 4.4`, strictly past the paper's `χ* = 1`.  This file records
the composed capture step: under the quadratic threshold and the crest data, the
instantaneous min-rate at an interior minimum is strictly positive.

**Scope** (unchanged from the two inputs): the crest relation, the oscillation
bounds `|v−u|, |v_z| ≤ b−a`, no overshoot `b ≤ 1`, the interior-minimum data
(`curv ≥ 0`, `react ≥ a(1−a)`, defect `≤ K`), and the wave-speed condition
`c > χ(b−a)` are HYPOTHESES.  Discharging them against an actual steady profile
(Green representation for the oscillation bounds; a no-overshoot barrier; the
crest and the interior minimum both existing) is the remaining analytic work, and
the front flux at `z = Z` is the shared make-or-break with the L² route (see the
drift-flux obstruction and `INTEGRITY_GAPS.md`).
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The explicit quadratic threshold is equivalent to `χ < (1−a)/K`. -/
theorem crest_quadratic_iff
    {χ a b c : ℝ} (ha1 : a < 1) (hab : a < b)
    (hc : χ * (b - a) < c) (hχ0 : 0 < χ) (hb0 : 0 < b) :
    χ ^ 2 * (b * (b - a)) + χ * ((1 - a) * (b - a)) - (1 - a) * c < 0 ↔
      χ < (1 - a) / (χ * b * (b - a) / (c - χ * (b - a))) := by
  have hba : 0 < b - a := by linarith
  have hD0 : 0 < c - χ * (b - a) := by linarith
  have hK0 : 0 < χ * b * (b - a) / (c - χ * (b - a)) :=
    div_pos (by positivity) hD0
  rw [lt_div_iff₀ hK0, ← mul_div_assoc, div_lt_iff₀ hD0]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **Crest capture.**  At an interior minimum with the crest gradient bound as
the oscillation control, the min-rate is strictly positive under the quadratic
threshold.  `curv = u_zz(z*) ≥ 0`, `react ≥ a(1−a)`, `uval = a`, `defect = (v−u)(z*)`
with `|defect| ≤ K` the crest bound. -/
theorem crest_capture_min_rise
    {curv react uval a defect b c χ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hab : a < b) (hb0 : 0 < b)
    (hχ0 : 0 < χ) (hc : χ * (b - a) < c)
    (hcurv : 0 ≤ curv) (huval : uval = a)
    (hreact : a * (1 - a) ≤ react)
    (hdefect : |defect| ≤ χ * b * (b - a) / (c - χ * (b - a)))
    (hquad : χ ^ 2 * (b * (b - a)) + χ * ((1 - a) * (b - a)) - (1 - a) * c < 0) :
    0 < curv + react - χ * uval * defect := by
  have hba : 0 < b - a := by linarith
  have hD0 : 0 < c - χ * (b - a) := by linarith
  have hK0 : 0 < χ * b * (b - a) / (c - χ * (b - a)) :=
    div_pos (by positivity) hD0
  have hthr : χ < (1 - a) / (χ * b * (b - a) / (c - χ * (b - a))) :=
    (crest_quadratic_iff ha1 hab hc hχ0 hb0).mp hquad
  exact pointwise_min_rise_of_oscillation_bound ha0 ha1 hcurv huval hreact
    hK0 hdefect hχ0.le hthr

section AxiomAudit

#print axioms crest_quadratic_iff
#print axioms crest_capture_min_rise

end AxiomAudit

end ShenWork.Paper1
