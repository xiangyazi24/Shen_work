import ShenWork.Paper1.WholeLineChiPosEntropyClassicalCompactness
import ShenWork.Paper1.WholeLineCauchyGlobalBounds

/-!
# Exact remaining obstructions for the normalized far-left theorem

Two independent bookkeeping facts matter when specializing the abstract
`chi < 4` entropy criterion to the current canonical Cauchy orbit.

* The compactness criterion itself applies `coMovingPath`, so its orbit must
  be supplied in laboratory coordinates.
* In the normalized critical case, the existing canonical ceiling regime
  already forces `chi < 1`; it therefore cannot justify the canonical global
  solution/ceiling on the new range `1 ≤ chi < 4`.

The remaining analytic statement inside the range where the canonical orbit
is available is exactly `CanonicalChiOneFarLeftParabolicCompactness`: uniform
local bounds and equicontinuity of the seven translated fields, in particular
of `uₓₓ` and `uₜ`.
-/

namespace ShenWork.Paper1

/-- On the critical exponent branch, the existing global ceiling regime has
no nonnegative-sensitivity cases at or above one. -/
theorem chi_lt_one_of_critical_ceilingRegime
    {p : CMParams} (hcritical : p.α = p.m + p.γ - 1)
    (hregime : WholeLineCauchyCeilingRegime p) :
    p.χ < 1 := by
  rcases hregime with hnonpos | ⟨_hchi, hsuper | hcriticalBranch⟩
  · linarith
  · rw [hcritical] at hsuper
    exact (lt_irrefl _ hsuper).elim
  · exact hcriticalBranch.1

theorem not_critical_ceilingRegime_of_one_le_chi
    {p : CMParams} (hchi : 1 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1) :
    ¬ WholeLineCauchyCeilingRegime p := by
  intro hregime
  have := chi_lt_one_of_critical_ceilingRegime
    (p := p) hcritical hregime
  linarith

section AxiomAudit

#print axioms chi_lt_one_of_critical_ceilingRegime
#print axioms not_critical_ceilingRegime_of_one_le_chi

end AxiomAudit

end ShenWork.Paper1
