import ShenWork.Paper1.WholeLineChiPosDispersion
import ShenWork.Paper1.WholeLineChiPosDispersionSharp

/-!
# Quantitative spectral margin and abstract local nonlinear stability

`WholeLineChiPosDispersionSharp` proves `dispersion α (χγ) s < 0` for every mode
`s ≥ 0` exactly when `χγ < (1 + √α)²`.  For a NONLINEAR argument one needs the
strict inequality quantified: a uniform gap `g0 > 0` below the linearized decay,
which is the budget available to absorb the `O(δ)` errors of a plateau of
half-width `δ`.

The modewise polynomial is
`q s = (s + α)(s + 1) - χγ·s = s² + (1 + α - χγ) s + α`, and
`q s ≥ 0 ⟺ dispersion α χγ s ≤ 0`.  Its minimum over `s ≥ 0` is the spectral
margin

`spectralMargin α χγ = α - (max 0 ((χγ - 1 - α)/2))²`

(`= α` when `χγ ≤ 1 + α`, the reaction floor at `s = 0`; `= α - ((χγ-1-α)/2)²`
when `χγ > 1 + α`, the interior Turing minimum).  It is `> 0` exactly on the
sub-threshold range `χγ < (1 + √α)²`, and `→ 0` at the threshold.

The final lemma packages the local nonlinear stability at the scalar level: the
spectral margin pays for the plateau errors.  It carries the linear coercivity
and the `O(δ)` remainder as HYPOTHESES; discharging those against actual PDE
solutions (the time-derivative energy identity `Ė = ∫ w·u_t` and the genuine
nonlinear remainder estimates) is the PDE interface and is NOT done here — the
repository's `IsClassicalSolution` is pointwise-classical, with no `L²`/energy
framework, so that step is a separate infrastructure build.  This brick is also
strictly LOCAL: it requires the plateau already tight (`δ` small).  GLOBAL
CAPTURE of the wide available band into a tight near-`1` neighbourhood for
sub-Turing `χ` remains the open problem (see `INTEGRITY_GAPS.md`).
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The modewise polynomial controlling `dispersion ≤ 0`.  `q_mode = (s+α)(s+1) −
χγ·s`; it satisfies `dispersion α χγ s = -(q_mode)/(1+s)`. -/
def qMode (α χγ s : ℝ) : ℝ := s ^ 2 + (1 + α - χγ) * s + α

/-- The spectral margin: the minimum of `qMode` over `s ≥ 0`. -/
def spectralMargin (α χγ : ℝ) : ℝ := α - (max 0 ((χγ - 1 - α) / 2)) ^ 2

theorem qMode_eq_dispersion_mul {α χγ s : ℝ} (hs : 0 ≤ s) :
    qMode α χγ s = -(dispersion α χγ s) * (1 + s) := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  unfold qMode dispersion
  field_simp
  ring

/-- **The quantitative margin.**  `qMode ≥ spectralMargin` at every mode. -/
theorem qMode_ge_spectralMargin (α χγ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    spectralMargin α χγ ≥ 0 → qMode α χγ s ≥ spectralMargin α χγ := by
  intro _
  have hcomplete :
      qMode α χγ s = (s + (1 + α - χγ) / 2) ^ 2 + (α - ((1 + α - χγ) / 2) ^ 2) := by
    unfold qMode; ring
  rw [hcomplete]
  unfold spectralMargin
  rcases le_or_gt (χγ - 1 - α) 0 with hsign | hsign
  · -- χγ ≤ 1 + α : `max 0 ((χγ-1-α)/2) = 0`, margin `= α`, and vertex `≥ 0`
    have hmax : max 0 ((χγ - 1 - α) / 2) = 0 := by
      apply max_eq_left; linarith
    rw [hmax]
    have hv : 0 ≤ (1 + α - χγ) / 2 := by linarith
    have hsq : 0 ≤ (s + (1 + α - χγ) / 2) ^ 2 - ((1 + α - χγ) / 2) ^ 2 := by
      have : ((1 + α - χγ) / 2) ^ 2 ≤ (s + (1 + α - χγ) / 2) ^ 2 := by
        apply sq_le_sq'
        · nlinarith
        · nlinarith
      linarith
    nlinarith [hsq]
  · -- χγ > 1 + α : `max 0 ((χγ-1-α)/2) = (χγ-1-α)/2`, margin is the interior min
    have hmax : max 0 ((χγ - 1 - α) / 2) = (χγ - 1 - α) / 2 := by
      apply max_eq_right; linarith
    rw [hmax]
    have heq : ((χγ - 1 - α) / 2) ^ 2 = ((1 + α - χγ) / 2) ^ 2 := by ring
    rw [heq]
    nlinarith [sq_nonneg (s + (1 + α - χγ) / 2)]

/-- **Margin positivity is exactly the sub-threshold condition.** -/
theorem spectralMargin_pos_iff (α χγ : ℝ) (hα : 0 < α) (_hχγ : 0 ≤ χγ) :
    0 < spectralMargin α χγ ↔ χγ < (1 + Real.sqrt α) ^ 2 := by
  have hsqrt : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  have hsqrt_pos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hthr : (1 + Real.sqrt α) ^ 2 = 1 + α + 2 * Real.sqrt α := by
    have : (1 + Real.sqrt α) ^ 2 = 1 + 2 * Real.sqrt α + Real.sqrt α ^ 2 := by ring
    rw [this, hsqrt]; ring
  unfold spectralMargin
  rcases le_or_gt (χγ - 1 - α) 0 with hsign | hsign
  · -- margin = α > 0, and χγ ≤ 1+α < threshold
    have hmax : max 0 ((χγ - 1 - α) / 2) = 0 := by apply max_eq_left; linarith
    rw [hmax]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
    constructor
    · intro _; rw [hthr]; nlinarith
    · intro _; exact hα
  · have hmax : max 0 ((χγ - 1 - α) / 2) = (χγ - 1 - α) / 2 := by
      apply max_eq_right; linarith
    rw [hmax, hthr]
    constructor
    · intro hpos
      -- α - ((χγ-1-α)/2)^2 > 0  ⟹  (χγ-1-α)^2 < 4α = (2√α)^2  ⟹  χγ-1-α < 2√α
      have h4 : (χγ - 1 - α) ^ 2 < (2 * Real.sqrt α) ^ 2 := by
        have : ((χγ - 1 - α) / 2) ^ 2 < α := by nlinarith
        have h2 : (2 * Real.sqrt α) ^ 2 = 4 * α := by rw [mul_pow]; nlinarith [hsqrt]
        nlinarith [this]
      have hb : |χγ - 1 - α| < |2 * Real.sqrt α| := by
        apply abs_lt_abs_of_sq_lt_sq h4
        positivity
      rw [abs_of_pos (by linarith : (0:ℝ) < 2 * Real.sqrt α)] at hb
      have := (abs_lt.mp hb).2
      linarith
    · intro hlt
      -- χγ < 1+α+2√α  ⟹  χγ-1-α < 2√α  ⟹  ((χγ-1-α)/2)^2 < α
      have hb : χγ - 1 - α < 2 * Real.sqrt α := by linarith
      have hsq : ((χγ - 1 - α) / 2) ^ 2 < α := by
        have hpos : 0 < χγ - 1 - α := hsign
        have : (χγ - 1 - α) ^ 2 < (2 * Real.sqrt α) ^ 2 := by
          apply sq_lt_sq'
          · nlinarith [hsqrt_pos]
          · exact hb
        have h2 : (2 * Real.sqrt α) ^ 2 = 4 * α := by rw [mul_pow]; nlinarith [hsqrt]
        nlinarith [this]
      linarith
  where
    abs_lt_abs_of_sq_lt_sq {a b : ℝ} (h : a ^ 2 < b ^ 2) (_hb : 0 ≤ b) : |a| < |b| := by
      nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]

/-- **Abstract local nonlinear stability.**  If the linear part decays at the
spectral-margin rate `g0` on the energy `M`, and the plateau remainder is
`O(δ)·M` with `C·δ ≤ g0/2`, then the full dissipation is strictly negative:
`Edot ≤ -(g0/2)·M`.  This is the precise sense in which the spectral margin pays
for the plateau errors — local nonlinear stability holds for ALL `χγ < (1+√α)²`
once the plateau is tight enough (`δ ≤ g0/(2C)`).  Carries the coercivity and the
remainder bound as hypotheses; the PDE discharge is separate. -/
theorem local_nonlinear_decay_of_margin
    {Edot Elin M δ C g0 : ℝ}
    (hM : 0 < M) (_hg0 : 0 < g0)
    (hlin : Elin ≤ -g0 * M)
    (herr : |Edot - Elin| ≤ C * δ * M)
    (hδ : C * δ ≤ g0 / 2) :
    Edot ≤ -(g0 / 2) * M := by
  have h1 : Edot - Elin ≤ C * δ * M := (abs_le.mp herr).2
  have h2 : C * δ * M ≤ (g0 / 2) * M := by
    apply mul_le_mul_of_nonneg_right hδ hM.le
  nlinarith [h1, hlin, h2]

section AxiomAudit

#print axioms qMode_eq_dispersion_mul
#print axioms qMode_ge_spectralMargin
#print axioms spectralMargin_pos_iff
#print axioms local_nonlinear_decay_of_margin

end AxiomAudit

end ShenWork.Paper1
