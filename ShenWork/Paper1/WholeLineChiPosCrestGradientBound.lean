import ShenWork.Paper1.WholeLineChiPosPointwiseCaptureStep

/-!
# The crest gradient bound (steady co-moving profile)

The three-oracle synthesis (`INTEGRITY_GAPS.md`, 2026-07-21) identified the
hand-buildable, non-circular route to a gradient bound `‖u_z‖∞ ≤ K` that beats
the paper's `χ*`: evaluate the ORIGINAL steady co-moving equation at an interior
maximum of `q = u_z` (where `u_zz = 0`).  With `γ = α = 1` the steady equation
`0 = u_zz + c·u_z − χ(u v_z)_z + u(1−u)`, expanded via `(u v_z)_z = q v_z + u(v−u)`,
gives at the crest (`u_zz = 0`)

`q·(c − χ v_z) = χ·u·(v − u) − u·(1 − u)`.

The nonlocal factors are controlled by the OSCILLATION, not the gradient (the
key that breaks circularity): `v = ½ e^{−|·|} ∗ u` is a unit-mass average, so
`|v − u| ≤ b − a` and `|v_z| ≤ b − a`, both `O(1)`.  Hence, when the profile does
not overshoot (`u ≤ 1`, so the reaction `u(1−u) ≥ 0` only helps) and the wave
speed dominates the transport defect (`c > χ(b−a)`),

`q ≤ χ·b·(b − a) / (c − χ(b − a))  =:  K`.

Verified numerically tight: `K(χ=1, c=4.4) = 0.239 ≈ 0.9/3.5`, matching the
measured gradient.  Composed with `pointwise_min_rise_of_oscillation_bound`
(`G = K`) it gives min-rise for `χ < (1−a)/K`; self-consistently `χ_max(c) ~ √c`,
≈ 1.7 at the empirical `c ≈ 4.4` — strictly past the paper's `χ* = 1`.

**Scope:** this is the ALGEBRAIC crest step at the abstract scalar level — the
crest relation, the oscillation bounds, and the no-overshoot `b ≤ 1` are
HYPOTHESES.  Discharging them against an actual steady profile (the crest exists;
the oscillation bounds from the Green representation; no overshoot as a barrier)
is the remaining analytic work.  The wave speed `c` is the binding physical
parameter; `b ≤ 1` (no overshoot) is an assumption, not a theorem (chemotaxis can
push a maximum through `1` — see the adversarial note in `INTEGRITY_GAPS.md`).
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- **Crest gradient bound.**  From the interior-maximum steady relation
`q(c − χ v_z) = χ u (v−u) − u(1−u)`, with the oscillation bounds and no
overshoot, the crest slope obeys `q ≤ χ b (b−a) / (c − χ(b−a))`. -/
theorem crest_gradient_bound
    {q c χ u vz vmu a b : ℝ}
    (hrel : q * (c - χ * vz) = χ * u * vmu - u * (1 - u))
    (hq : 0 ≤ q) (hχ : 0 ≤ χ)
    (hvz : |vz| ≤ b - a) (hvmu : vmu ≤ b - a) (hvmu0 : 0 ≤ vmu)
    (hua : a ≤ u) (hub : u ≤ b) (hb1 : b ≤ 1) (ha0 : 0 < a)
    (hc : χ * (b - a) < c) :
    q ≤ χ * b * (b - a) / (c - χ * (b - a)) := by
  have hab : a ≤ b := hua.trans hub
  have hba : 0 ≤ b - a := by linarith
  -- denominator `c − χ v_z ≥ c − χ(b−a) > 0`
  have hvz_le : vz ≤ b - a := (abs_le.mp hvz).2
  have hD0 : 0 < c - χ * (b - a) := by linarith
  have hden : c - χ * (b - a) ≤ c - χ * vz := by
    have : χ * vz ≤ χ * (b - a) := mul_le_mul_of_nonneg_left hvz_le hχ
    linarith
  have hden_pos : 0 < c - χ * vz := lt_of_lt_of_le hD0 hden
  -- numerator `= q · (c − χ v_z) ≥ 0`, and `≤ χ b (b−a)`
  have hnum_nonneg : 0 ≤ χ * u * vmu - u * (1 - u) := by
    rw [← hrel]; exact mul_nonneg hq hden_pos.le
  have hu0 : 0 ≤ u := ha0.le.trans hua
  have hreact_nonneg : 0 ≤ u * (1 - u) := mul_nonneg hu0 (by linarith)
  have hchem_le : χ * u * vmu ≤ χ * b * (b - a) := by
    have h1 : χ * u ≤ χ * b := mul_le_mul_of_nonneg_left hub hχ
    have h2 : χ * u * vmu ≤ χ * b * vmu :=
      mul_le_mul_of_nonneg_right h1 hvmu0
    have h3 : χ * b * vmu ≤ χ * b * (b - a) :=
      mul_le_mul_of_nonneg_left hvmu (mul_nonneg hχ (hu0.trans hub))
    exact h2.trans h3
  have hnum_le : χ * u * vmu - u * (1 - u) ≤ χ * b * (b - a) := by linarith
  -- q = num / (c − χ v_z) ≤ χ b (b−a) / (c − χ(b−a))
  have hq_eq : q = (χ * u * vmu - u * (1 - u)) / (c - χ * vz) := by
    rw [← hrel]; field_simp
  rw [hq_eq]
  rw [div_le_div_iff₀ hden_pos hD0]
  nlinarith [hnum_le, hden, hnum_nonneg, mul_nonneg hχ (mul_nonneg (hu0.trans hub) hba)]

section AxiomAudit

#print axioms crest_gradient_bound

end AxiomAudit

end ShenWork.Paper1
