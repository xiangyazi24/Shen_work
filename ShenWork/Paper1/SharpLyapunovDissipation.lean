import ShenWork.Paper1.SharpConstant
import ShenWork.Paper1.SharpDissipationCollapse
import ShenWork.Paper1.WholeLineChiPosDispersion

/-!
# The sharp linearized Lyapunov dissipation inequality

After the resolver identities collapse the chemotactic contribution, the
remaining scalar multiplier is controlled mode by mode by the sharp constant
`(1 + √α)²`.  The statements here stop at the Fourier/quadratic-form level:
turning them into an integral theorem would require separate transform and
integrability hypotheses.  In particular, the sharp threshold is asserted
only for the linearized quadratic form, not for nonlinear stability.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- At or below the sharp threshold, the destabilizing multiplier is bounded
by the diffusive-reaction multiplier at every nonnegative mode.  This is only
a linearized Fourier/quadratic-form statement and does not assert nonlinear
stability up to the same threshold. -/
theorem sharp_linearized_mode_dissipation
    (alpha chi gamma : ℝ) (_hgamma : 0 < gamma) (halpha : 0 < alpha)
    (hthreshold : chi * gamma ≤ (1 + Real.sqrt alpha) ^ 2) :
    ∀ s : ℝ, 0 ≤ s → chi * gamma * s / (s + 1) ≤ s + alpha := by
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    simpa using halpha.le
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hratio := sharp_constant_le_mode_ratio alpha halpha hspos
    have hchi : chi * gamma ≤ (s + alpha) * (s + 1) / s :=
      le_trans hthreshold hratio
    have hden : 0 < s + 1 := by linarith
    rw [div_le_iff₀ hden]
    exact (le_div_iff₀ hspos).mp hchi

/-- The mode inequality is exactly nonpositivity of the existing dispersion
function, including equality at the sharp threshold.  This conclusion is only
about the linearized dispersion/quadratic form; it is not a nonlinear
stability theorem. -/
theorem sharp_linearized_dispersion_nonpos
    (alpha chi gamma : ℝ) (hgamma : 0 < gamma) (halpha : 0 < alpha)
    (hthreshold : chi * gamma ≤ (1 + Real.sqrt alpha) ^ 2) :
    ∀ s : ℝ, 0 ≤ s → dispersion alpha (chi * gamma) s ≤ 0 := by
  intro s hs
  have hmode :=
    sharp_linearized_mode_dissipation alpha chi gamma hgamma halpha hthreshold s hs
  unfold dispersion
  rw [add_comm 1 s]
  linarith

/-- The algebraic resolver collapse and its sharp modewise control, packaged
as one linearized dissipation brick.  This remains an algebraic/Fourier
quadratic-form result: no integral-level analytic side conditions are supplied,
and no nonlinear stability threshold is claimed. -/
theorem sharp_linearized_dissipation_brick
    (alpha chi gamma W P Z Zz S : ℝ)
    (hgamma : 0 < gamma) (halpha : 0 < alpha)
    (hthreshold : chi * gamma ≤ (1 + Real.sqrt alpha) ^ 2)
    (hfirst : gamma * P = Z + S)
    (hsecond : gamma ^ 2 * W = Zz + 2 * Z + S) :
    chi * gamma * W - chi * P = (chi / gamma) * (Zz + Z) ∧
      (∀ s : ℝ, 0 ≤ s → chi * gamma * s / (s + 1) ≤ s + alpha) ∧
      (∀ s : ℝ, 0 ≤ s → dispersion alpha (chi * gamma) s ≤ 0) := by
  exact ⟨sharp_dissipation_collapse chi gamma W P Z Zz S
      (ne_of_gt hgamma) hfirst hsecond,
    sharp_linearized_mode_dissipation alpha chi gamma hgamma halpha hthreshold,
    sharp_linearized_dispersion_nonpos alpha chi gamma hgamma halpha hthreshold⟩

section AxiomAudit

#print axioms sharp_linearized_mode_dissipation
#print axioms sharp_linearized_dispersion_nonpos
#print axioms sharp_linearized_dissipation_brick

end AxiomAudit

end ShenWork.Paper1
