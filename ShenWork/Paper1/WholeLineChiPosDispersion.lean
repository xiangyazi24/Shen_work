import ShenWork.Defs

/-!
# The linear dispersion relation at the equilibrium `u ≡ 1`

Linearizing `u_t = u_xx − χ(u^m v_x)_x + u(1−u^α)`, `0 = v_xx − v + u^γ` at the
constant state `(u,v) = (1,1)` and testing with a Fourier mode `e^{ikx}` gives
the growth rate

  `λ(k) = −α − k² + χγ · k²/(1+k²)`,

because the elliptic component contributes `z = γ/(1+k²) w` and the chemotactic
flux linearizes to `−χ z_xx` (the `u^{m-1}` prefactor drops at `u ≡ 1`).

Writing `s = k² ≥ 0`, this file proves the SPECTRAL BOUND that decides the
`χ ∈ [1/2, χ*)` question: for `χγ ≤ 1` every mode decays at rate at least `α`,

  `λ(s) ≤ −α`      for all `s ≥ 0`,

so the constant state is linearly stable with a UNIFORM gap `α`, independent of
`χ` throughout `χγ ≤ 1`.  Since `χ* ≤ 1`, the whole range claimed by Theorem 1.2
has `χγ ≤ γ`; at `γ = 1` this is exactly `χ ≤ 1`, covering the disputed window.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The dispersion function in the mode variable `s = k²`. -/
def dispersion (α χγ s : ℝ) : ℝ := -α - s + χγ * s / (1 + s)

/-- SPECTRAL GAP.  For `χγ ≤ 1` the dispersion is at most `−α` at every mode:
the constant state is linearly stable with uniform gap `α`. -/
theorem dispersion_le_neg_alpha
    (α χγ : ℝ) (hχγ0 : 0 ≤ χγ) (hχγ1 : χγ ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    dispersion α χγ s ≤ -α := by
  unfold dispersion
  have hden : 0 < 1 + s := by linarith
  have hkey : χγ * s ≤ s * (1 + s) := by nlinarith [mul_nonneg hs hs]
  have hstep : χγ * s / (1 + s) ≤ s := by
    rw [div_le_iff₀ hden]; nlinarith [hkey]
  linarith

/-- Consequently the maximal growth rate is exactly `−α` on `χγ ≤ 1` (the bound
is attained at `s = 0`). -/
theorem dispersion_sup_eq_neg_alpha
    (α χγ : ℝ) (hχγ0 : 0 ≤ χγ) (hχγ1 : χγ ≤ 1) :
    dispersion α χγ 0 = -α ∧
      ∀ s : ℝ, 0 ≤ s → dispersion α χγ s ≤ dispersion α χγ 0 := by
  refine ⟨by simp [dispersion], ?_⟩
  intro s hs
  have h := dispersion_le_neg_alpha α χγ hχγ0 hχγ1 hs
  simpa [dispersion] using h

/-- Strict linear stability on the physically relevant range: for `α > 0` and
`χγ ≤ 1`, every mode has strictly negative growth.  Immediate from the spectral
gap (the bound `−α` is strictly negative). -/
theorem dispersion_neg_of_chiGamma_le_one
    (α χγ : ℝ) (hα : 0 < α) (hχγ0 : 0 ≤ χγ) (hχγ1 : χγ ≤ 1)
    {s : ℝ} (hs : 0 ≤ s) :
    dispersion α χγ s < 0 :=
  lt_of_le_of_lt (dispersion_le_neg_alpha α χγ hχγ0 hχγ1 hs) (by linarith)

/-!
## The sharp far-left spectral threshold `χγ < (1 + √α)²`

Beyond the easy `χγ ≤ 1` gap above, the true onset of the essential/plane-wave
spectrum sits at `χγ = (1 + √α)²` (at `α = γ = 1`, exactly `χ = 4`).  Optimizing
`s ↦ dispersion α χγ s` over `s ≥ 0` gives the maximal growth rate

  `max_{s ≥ 0} dispersion α χγ s = (√(χγ) − 1)² − α`,

attained at `s* = √(χγ) − 1` (for `χγ ≥ 1`).  The maximum is `< 0` iff
`(√(χγ) − 1)² < α`, i.e. `√(χγ) < 1 + √α`, i.e. `χγ < (1 + √α)²`.  This is the
plane-wave / essential-spectrum certification that `(1 + √α)²` is the sharp
linear far-left threshold: no unstable ("Turing") mode exists below it, so the
constant plateau `u ≡ 1` is linearly stable throughout the full range, matching
the sharp entropy coefficient `1 − χ²/16 > 0 ⟺ χ < 4` at `α = γ = 1`. -/

/-- SHARP SPECTRAL BOUND.  For every mode `s ≥ 0` the growth rate is bounded by
the optimized value `(√(χγ) − 1)² − α`.  The slack is a perfect square,
`(√(χγ) − 1 − s)² ≥ 0`, so the bound holds for all `χγ ≥ 0` (it is attained at
`s = √(χγ) − 1` when `χγ ≥ 1`). -/
theorem dispersion_le_sharp
    (α χγ : ℝ) (hχγ0 : 0 ≤ χγ) {s : ℝ} (hs : 0 ≤ s) :
    dispersion α χγ s ≤ (Real.sqrt χγ - 1) ^ 2 - α := by
  unfold dispersion
  have hden : 0 < 1 + s := by linarith
  have hq : Real.sqrt χγ ^ 2 = χγ := Real.sq_sqrt hχγ0
  -- reduce to the polynomial bound after clearing the positive denominator;
  -- the slack is the perfect square `(√χγ − 1 − s)² ≥ 0`
  have hfrac : χγ * s / (1 + s) ≤ (Real.sqrt χγ - 1) ^ 2 + s := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (Real.sqrt χγ - 1 - s), hq, hs, hden]
  linarith

/-- SHARPNESS.  For `χγ ≥ 1` the optimized bound is ATTAINED at the critical
mode `s* = √(χγ) − 1`, so `(√(χγ) − 1)² − α` is genuinely the maximum, not a
loose bound. -/
theorem dispersion_max_attained
    (α χγ : ℝ) (hχγ1 : 1 ≤ χγ) :
    dispersion α χγ (Real.sqrt χγ - 1) = (Real.sqrt χγ - 1) ^ 2 - α := by
  have hq : Real.sqrt χγ ^ 2 = χγ := Real.sq_sqrt (by linarith)
  have hqpos : 0 < Real.sqrt χγ := Real.sqrt_pos.mpr (by linarith)
  unfold dispersion
  rw [show (1 : ℝ) + (Real.sqrt χγ - 1) = Real.sqrt χγ from by ring]
  field_simp
  nlinarith [hq, hqpos]

/-- SHARP THRESHOLD.  For `α > 0`, the constant plateau is linearly stable
(every mode `s ≥ 0` strictly decays) whenever `χγ < (1 + √α)²`.  This is the
plane-wave / essential-spectrum certification of the sharp far-left threshold
`(1 + √α)²`; below `χγ ≤ 1` it reduces to the uniform gap `α`, and on
`1 < χγ < (1 + √α)²` it uses the optimized bound `(√(χγ) − 1)² − α < 0`. -/
theorem dispersion_neg_of_below_sharpThreshold
    (α χγ : ℝ) (hα : 0 < α) (hχγ0 : 0 ≤ χγ)
    (hthr : χγ < (1 + Real.sqrt α) ^ 2) {s : ℝ} (hs : 0 ≤ s) :
    dispersion α χγ s < 0 := by
  by_cases h1 : χγ ≤ 1
  · exact dispersion_neg_of_chiGamma_le_one α χγ hα hχγ0 h1 hs
  · have h1' : 1 < χγ := not_le.mp h1
    have hbound := dispersion_le_sharp α χγ hχγ0 hs
    have hsqα : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
    have hsqrtα_pos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
    have hq1 : (1 : ℝ) ≤ Real.sqrt χγ := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt h1'.le
    have hsqrt : Real.sqrt χγ < 1 + Real.sqrt α := by
      have h := Real.sqrt_lt_sqrt hχγ0 hthr
      rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt α)] at h
    have hd0 : 0 ≤ Real.sqrt χγ - 1 := by linarith
    have hd1 : Real.sqrt χγ - 1 < Real.sqrt α := by linarith
    have hmax_neg : (Real.sqrt χγ - 1) ^ 2 - α < 0 := by
      nlinarith [hd0, hd1, hsqrtα_pos, hsqα]
    linarith

/-- The disputed `α = γ = 1` case: the plateau `u ≡ 1` is linearly stable for
every `0 ≤ χ < 4`.  The threshold `4 = (1 + √1)²` matches the sharp entropy
coefficient `1 − χ²/16 > 0 ⟺ χ < 4`. -/
theorem dispersion_neg_of_chi_lt_four
    (χ : ℝ) (hχ0 : 0 ≤ χ) (hχ4 : χ < 4) {s : ℝ} (hs : 0 ≤ s) :
    dispersion 1 χ s < 0 := by
  have h : χ < (1 + Real.sqrt 1) ^ 2 := by rw [Real.sqrt_one]; norm_num; linarith
  exact dispersion_neg_of_below_sharpThreshold 1 χ (by norm_num) hχ0 h hs

section AxiomAudit

#print axioms dispersion_le_neg_alpha
#print axioms dispersion_sup_eq_neg_alpha
#print axioms dispersion_neg_of_chiGamma_le_one
#print axioms dispersion_le_sharp
#print axioms dispersion_max_attained
#print axioms dispersion_neg_of_below_sharpThreshold
#print axioms dispersion_neg_of_chi_lt_four

end AxiomAudit

end ShenWork.Paper1
