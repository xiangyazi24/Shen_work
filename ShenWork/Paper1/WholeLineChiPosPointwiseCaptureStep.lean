import ShenWork.Paper1.WholeLineChiPosSpectralMargin

/-!
# The pointwise capture step under an oscillation / gradient bound

Fable's analysis (recorded in `INTEGRITY_GAPS.md`, 2026-07-21) isolates the
far-left global-capture crux to a single missing object: a pointwise a-priori
gradient bound `‖u_z‖∞ ≤ K`.  Given `-v_zz + v = u^γ`, the Green representation
`v = ½ e^{-|·|} ∗ u^γ` yields the oscillation bound

`|(v - u)(z)| ≤ min (b - a, ‖(u^γ)_z‖∞)`,

so the chemotaxis defect `(v - u)` — which the pointwise comparison principle can
otherwise bound only by the full band `b - a` — is controlled by the gradient.

This file records the ALGEBRAIC capture step that such an oscillation bound
feeds, at the abstract scalar level (no PDE objects, no integrals).  At an
interior minimum `z*` of `u` (so `u_z(z*) = 0`, `u_zz(z*) ≥ 0`), with `γ = α = 1`
and the elliptic identity `v - u = v_zz`, the co-moving evolution reads

`u_t(z*) = u_zz(z*) + u(1 - u) - χ · u · (v - u)(z*)`.

The minimum is non-decreasing as soon as this is `≥ 0`.  Using `u_zz(z*) ≥ 0`,
the reaction coercivity `u(1-u) ≥ (1-a)·a`-type lower bound on the plateau, and
an oscillation bound `|(v-u)(z*)| ≤ G`, the minimum strictly rises whenever

`χ < (1 - a) / G`.

With the crude band bound `G = b - a` this is `χ < (1-a)/(b-a)` — weak, and it
is why every purely pointwise route stalls at `χ ≈ 1/2`.  With a gradient bound
`G = K` it becomes `χ < (1-a)/K`; numerically `(1-a)/K ≈ 3.5` along the
dynamics, so a gradient estimate pushes the pointwise threshold PAST the paper's
`χ*`.  The open problem is precisely the Bernstein constant `K` — this brick
makes the reduction to it machine-checked.

**Scope:** these are scalar inequalities in the extremal-point data.  The
oscillation bound `G` and the interior-extremum facts `u_z(z*)=0`, `u_zz(z*)≥0`
are HYPOTHESES; discharging them against actual PDE solutions (the Green
representation + a Bernstein gradient estimate + the maximum principle at a
barrier touch) is the analytic work that remains, and the gradient estimate is
the single open quantitative ingredient.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- **Pointwise min-rise under an oscillation bound.**  At an interior minimum,
with the curvature nonnegative, the reaction bounded below by its plateau value,
and the chemotaxis defect controlled by `G`, the instantaneous rate is strictly
positive when `χ < (1 - a)/G`.  Everything is scalar: `curv = u_zz(z*) ≥ 0`,
`react ≥ a(1-a)` is the reaction lower bound, `uval = u(z*) = a`, `defect = (v-u)(z*)`
with `|defect| ≤ G`. -/
theorem pointwise_min_rise_of_oscillation_bound
    {curv react uval a defect G χ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hcurv : 0 ≤ curv)
    (huval : uval = a)
    (hreact : a * (1 - a) ≤ react)
    (hG : 0 < G) (hdefect : |defect| ≤ G)
    (hχ0 : 0 ≤ χ)
    (hχ : χ < (1 - a) / G) :
    0 < curv + react - χ * uval * defect := by
  -- χ · G < 1 - a  from the threshold
  have hthr : χ * G < 1 - a := by
    rw [← lt_div_iff₀ hG]; exact hχ
  -- the chemotaxis term is at most χ · a · G (uval = a > 0)
  have hdef_le : defect ≤ G := (abs_le.mp hdefect).2
  have hchem_le : χ * uval * defect ≤ χ * a * G := by
    rw [huval]
    have h1 : χ * a * defect ≤ χ * a * G :=
      mul_le_mul_of_nonneg_left hdef_le (mul_nonneg hχ0 ha0.le)
    linarith [h1]
  -- curv + react - chem ≥ 0 + a(1-a) - χ a G = a((1-a) - χG) > 0
  have hkey : 0 < a * ((1 - a) - χ * G) := mul_pos ha0 (by linarith)
  nlinarith [hcurv, hreact, hchem_le, hkey]

/-- **The gradient bound beats the band bound.**  With the crude band bound
`G = b - a`, the admissible threshold is `(1-a)/(b-a)`; with a gradient bound
`G = K < b - a`, it is strictly larger.  So any genuine gradient control widens
the pointwise capture window. -/
theorem pointwise_threshold_mono_in_bound
    {a K1 K2 : ℝ} (ha0 : 0 < a) (hK1 : 0 < K1) (hK2 : K2 < K1) (hK2pos : 0 < K2)
    (ha1 : a < 1) :
    (1 - a) / K1 < (1 - a) / K2 := by
  have hnum : 0 < 1 - a := by linarith
  exact div_lt_div_of_pos_left hnum hK2pos hK2

section AxiomAudit

#print axioms pointwise_min_rise_of_oscillation_bound
#print axioms pointwise_threshold_mono_in_bound

end AxiomAudit

end ShenWork.Paper1
