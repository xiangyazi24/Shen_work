/-
  ShenWork/Paper2/IntervalRpowLipschitz.lean

  Thin floorless scalar-power Lipschitz adapter for the strict-negative
  all-PPID route.  The underlying `[0,M]` estimate already exists in
  `IntervalDomainL2UEnergyUniformGammaGeOne`; this file exposes the existential
  interface used by floor-free fixed-point planning.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyUniformGammaGeOne

namespace ShenWork.Paper2

noncomputable section

/-- Floorless Lipschitz control for real powers on a bounded nonnegative
interval.  The constant may depend on `q` and `M`, but not on a positive lower
floor. -/
theorem rpow_lipschitz_on_Icc_nonneg
    {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ r s : ℝ, 0 ≤ r → r ≤ M → 0 ≤ s → s ≤ M →
        |r ^ q - s ^ q| ≤ L * |r - s| := by
  refine ⟨q * M ^ (q - 1), ?_, ?_⟩
  · exact mul_nonneg (le_trans zero_le_one hq) (Real.rpow_nonneg hM _)
  · intro r s hr0 hrM hs0 hsM
    exact rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma hq hM
      ⟨hr0, hrM⟩ ⟨hs0, hsM⟩

end

end ShenWork.Paper2

#print axioms ShenWork.Paper2.rpow_lipschitz_on_Icc_nonneg
