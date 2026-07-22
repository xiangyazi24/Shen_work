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

section AxiomAudit

#print axioms dispersion_le_neg_alpha
#print axioms dispersion_sup_eq_neg_alpha
#print axioms dispersion_neg_of_chiGamma_le_one

end AxiomAudit

end ShenWork.Paper1
