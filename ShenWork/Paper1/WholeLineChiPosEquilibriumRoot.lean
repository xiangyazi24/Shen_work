import ShenWork.Paper1.WholeLineChiPosEquilibriumCeiling
import ShenWork.Paper1.WholeLineChiPosSupercriticalCeiling

/-!
# The exact positive-sensitivity equilibrium root

In the supercritical branch, the scalar equilibrium equation is nonpositive at
`1` and nonnegative at the explicit parameter ceiling.  Continuity and the
intermediate value theorem therefore select an exact equilibrium in between.
-/

open Real Set

noncomputable section

namespace ShenWork.Paper1

/-- The positive-branch scalar equilibrium equation is continuous on the
half-line starting at `1`. -/
theorem continuousOn_chiPosEquilibriumEq_Ici (p : CMParams) :
    ContinuousOn (chiPosEquilibriumEq p) (Set.Ici 1) := by
  have hα : Continuous (fun M : ℝ => M ^ p.α) :=
    Real.continuous_rpow_const (zero_le_one.trans p.hα)
  have hq : (0 : ℝ) ≤ p.m + p.γ - 1 := by
    linarith [p.hm, p.hγ]
  have hpow : Continuous (fun M : ℝ => M ^ (p.m + p.γ - 1)) :=
    Real.continuous_rpow_const hq
  exact (hα.sub (continuous_const.mul hpow)).sub continuous_const |>.continuousOn

/-- In the supercritical nonnegative-sensitivity regime, an exact equilibrium
lies between `1` and the explicit parameter ceiling. -/
theorem exists_chiPosEquilibriumRoot
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α) :
    ∃ M, 1 ≤ M ∧ M ≤ wholeLineCauchyParameterCeiling p ∧
      chiPosEquilibriumEq p M = 0 := by
  let C : ℝ := wholeLineCauchyParameterCeiling p
  have h1C : (1 : ℝ) ≤ C :=
    one_le_wholeLineCauchyParameterCeiling_of_supercritical p hsuper
  have hlarge : 1 + p.χ ≤ C ^ (p.α - (p.m + p.γ - 1)) :=
    wholeLineCauchyParameterCeiling_pow_gap_of_supercritical
      p hχ hsuper (le_refl C)
  have hCnonneg : 0 ≤ chiPosEquilibriumEq p C :=
    chiPosEquilibriumEq_pos_of_large p hχ hsuper h1C hlarge
  have h1nonpos : chiPosEquilibriumEq p 1 ≤ 0 := by
    rw [chiPosEquilibriumEq_one]
    linarith
  have hcont : ContinuousOn (chiPosEquilibriumEq p) (Set.Icc 1 C) :=
    (continuousOn_chiPosEquilibriumEq_Ici p).mono Set.Icc_subset_Ici_self
  have hzero : (0 : ℝ) ∈
      Set.Icc (chiPosEquilibriumEq p 1) (chiPosEquilibriumEq p C) :=
    ⟨h1nonpos, hCnonneg⟩
  rcases intermediate_value_Icc h1C hcont hzero with ⟨M, hM, heq⟩
  exact ⟨M, hM.1, hM.2, heq⟩

/-- The selected exact positive-sensitivity equilibrium ceiling.  Outside the
supercritical nonnegative-sensitivity regime, where the required root need not
exist in the prescribed interval, the definition uses the harmless default
value `1`. -/
def chiPosEquilibriumCeiling (p : CMParams) : ℝ :=
  if h : 0 ≤ p.χ ∧ p.m + p.γ - 1 < p.α then
    Classical.choose (exists_chiPosEquilibriumRoot p h.1 h.2)
  else
    1

theorem chiPosEquilibriumCeiling_one_le
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α) :
    1 ≤ chiPosEquilibriumCeiling p := by
  rw [chiPosEquilibriumCeiling, dif_pos ⟨hχ, hsuper⟩]
  exact (Classical.choose_spec
    (exists_chiPosEquilibriumRoot p hχ hsuper)).1

theorem chiPosEquilibriumCeiling_le_parameterCeiling
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α) :
    chiPosEquilibriumCeiling p ≤ wholeLineCauchyParameterCeiling p := by
  rw [chiPosEquilibriumCeiling, dif_pos ⟨hχ, hsuper⟩]
  exact (Classical.choose_spec
    (exists_chiPosEquilibriumRoot p hχ hsuper)).2.1

theorem chiPosEquilibriumCeiling_eq_zero
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α) :
    chiPosEquilibriumEq p (chiPosEquilibriumCeiling p) = 0 := by
  rw [chiPosEquilibriumCeiling, dif_pos ⟨hχ, hsuper⟩]
  exact (Classical.choose_spec
    (exists_chiPosEquilibriumRoot p hχ hsuper)).2.2

section AxiomAudit

#print axioms continuousOn_chiPosEquilibriumEq_Ici
#print axioms exists_chiPosEquilibriumRoot
#print axioms chiPosEquilibriumCeiling_one_le
#print axioms chiPosEquilibriumCeiling_le_parameterCeiling
#print axioms chiPosEquilibriumCeiling_eq_zero

end AxiomAudit

end ShenWork.Paper1
