import ShenWork.Paper2.IntervalPicardLimitK1C2Coeff
import ShenWork.Paper2.IntervalPicardWeightedC2Bootstrap

/-!
# Clamped K1 source C2-coefficient envelope audit

This module is the construction site for the clamped K1 source
`SourceC2CoeffFields`.  It starts by pinning the committed source coefficient
decay theorem used by the K1 clamp path.
-/

noncomputable section

namespace ShenWork.Paper2.ClampedK1SourceC2CoeffEnvelope

/-- The committed per-slice source coefficient decay available to the K1 clamp. -/
abbrev committedSourceCoeffDecay :=
  ShenWork.IntervalPicardWeightedC2Bootstrap.slice_source_coeff_decay

/-- Algebraic content of the committed `C/(kπ)^2` source decay after one
Neumann eigenvalue weight.  This is only a uniform bound in `k`. -/
theorem quadraticDecay_oneEigenvalue_le_const
    {a : ℕ → ℝ} {C : ℝ}
    (hdecay : ∀ k : ℕ, 1 ≤ k →
      |a k| ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k * |a k| ≤ C := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam :
      unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
    unfold unitIntervalCosineEigenvalue
    ring
  calc
    unitIntervalCosineEigenvalue k * |a k|
        = ((k : ℝ) * Real.pi) ^ 2 * |a k| := by rw [hlam]
    _ ≤ ((k : ℝ) * Real.pi) ^ 2 *
          (C / ((k : ℝ) * Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left (hdecay k hk) hden.le
    _ = C := by field_simp [ne_of_gt hden]

/-- A positive constant tail is not summable.  Thus a decay theorem whose best
weighted consequence is only `λ_k |a_k| ≤ C` cannot provide the summable
`sourceEigenEnvelope` field unless a stronger coefficient tail is available. -/
theorem not_summable_const_of_ne {C : ℝ} (hC : C ≠ 0) :
    ¬ Summable (fun _ : ℕ => C) := by
  intro hsum
  exact hC ((summable_const_iff C).mp hsum)

/-- After two Neumann eigenvalue weights, the same committed quadratic decay
leaves the non-summable-looking majorant `C * λ_k`. -/
theorem quadraticDecay_twoEigenvalues_le_const_mul_eigen
    {a : ℕ → ℝ} {C : ℝ}
    (hdecay : ∀ k : ℕ, 1 ≤ k →
      |a k| ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k *
      (unitIntervalCosineEigenvalue k * |a k|)
        ≤ C * unitIntervalCosineEigenvalue k := by
  have hlam_nonneg : 0 ≤ unitIntervalCosineEigenvalue k := by
    unfold unitIntervalCosineEigenvalue
    positivity
  calc
    unitIntervalCosineEigenvalue k *
      (unitIntervalCosineEigenvalue k * |a k|)
        ≤ unitIntervalCosineEigenvalue k * C :=
          mul_le_mul_of_nonneg_left
            (quadraticDecay_oneEigenvalue_le_const hdecay hk) hlam_nonneg
    _ = C * unitIntervalCosineEigenvalue k := by ring

end ShenWork.Paper2.ClampedK1SourceC2CoeffEnvelope
