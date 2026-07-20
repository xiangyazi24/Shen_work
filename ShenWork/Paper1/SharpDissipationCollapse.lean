import ShenWork.Paper1.WholeLineResolverTestingIdentities

/-!
# Algebraic collapse in the linearized dissipation

The two resolver testing identities are kept as hypotheses here, so the result
is a purely algebraic substitution.  This file makes no nonlinear stability
claim: any sharp threshold obtained from this collapse applies only to the
linearized quadratic form.
-/

namespace ShenWork.Paper1

/-- The two linearized resolver energy identities collapse the chemotactic
contribution to the sum of the first- and second-derivative energies.  This is
only a linear/quadratic identity; in particular, a sharp threshold derived from
it is not asserted to be a sharp nonlinear stability threshold. -/
theorem sharp_dissipation_collapse
    (chi gamma W P Z Zz S : ℝ)
    (hgamma : gamma ≠ 0)
    (hfirst : gamma * P = Z + S)
    (hsecond : gamma ^ 2 * W = Zz + 2 * Z + S) :
    chi * gamma * W - chi * P = (chi / gamma) * (Zz + Z) := by
  calc
    chi * gamma * W - chi * P =
        (chi / gamma) * (gamma ^ 2 * W - gamma * P) := by
      field_simp [hgamma]
    _ = (chi / gamma) * ((Zz + 2 * Z + S) - (Z + S)) := by
      rw [hsecond, hfirst]
    _ = (chi / gamma) * (Zz + Z) := by ring

section AxiomAudit

#print axioms sharp_dissipation_collapse

end AxiomAudit

end ShenWork.Paper1
