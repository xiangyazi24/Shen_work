/-
  B2/B4 (MinPersistence): the elliptic source bound `|ν·u^γ| ≤ ν·M'^γ`.

  The chemical resolver source `Src = ν·u^γ` is bounded by `ν·M'^γ` whenever
  `0 ≤ u ≤ M'` (with `0 ≤ γ`, `0 ≤ ν`).  This is the `|Src| ≤ B` input of
  `elliptic_coeff_bounds` (the B4 v-field bounds), with `B := ν·M'^γ`.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Power-source bound.**  `|ν·u^γ| ≤ ν·M'^γ` for `0 ≤ u ≤ M'`, `0 ≤ γ`,
`0 ≤ ν`. -/
theorem power_source_abs_le
    {ν γ M' u : ℝ} (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hu_nonneg : 0 ≤ u) (hu_le : u ≤ M') :
    |ν * u ^ γ| ≤ ν * M' ^ γ := by
  have hpow_nonneg : 0 ≤ u ^ γ := Real.rpow_nonneg hu_nonneg γ
  have hprod_nonneg : 0 ≤ ν * u ^ γ := mul_nonneg hν hpow_nonneg
  rw [abs_of_nonneg hprod_nonneg]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu_nonneg hu_le hγ) hν

end ShenWork.MinPersistenceAtoms
