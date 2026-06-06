/-
  B2/B4 (MinPersistence): the flux coefficient bound `|g| ≤ K₁`.

  The chemotaxis flux divergence at a spatial critical point of `u`
  (`u_x = 0`) is `m·g`, where
    `g = ∂ₓ(φ(v)·v_x) = φ'(v)·v_x² + φ(v)·v_xx`,   `φ(w) = (1+w)^{−β}`.
  With the B4 coefficient bounds `|v_x| ≤ 2B`, `|v_xx| ≤ 2B` and `v ≥ 0`
  (so `1+v ≥ 1`, hence `(1+v)^{−β} ≤ 1` and `β(1+v)^{−β−1} ≤ β`), this gives
  the explicit slab-independent constant
    `|g| ≤ K₁(B) := β·(2B)² + 2B`.

  Stated over abstract reals (the caller supplies `v_x`, `v_xx`, `v` and the
  B4 bounds); the differential-calculus identity `g = φ'v_x² + φv_xx` is a
  separate `HasDerivAt` lemma.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- The explicit flux-coefficient constant `K₁(β,B) = β·(2B)² + 2B`. -/
def fluxCoeffConst (β B : ℝ) : ℝ := β * (2 * B) ^ 2 + 2 * B

theorem fluxCoeffConst_nonneg {β B : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B) :
    0 ≤ fluxCoeffConst β B := by
  unfold fluxCoeffConst; positivity

/-- **Flux coefficient bound.**  The flux-divergence coefficient
`g = −β(1+v)^{−β−1}·v_x² + (1+v)^{−β}·v_xx` is bounded by `K₁(β,B) = β(2B)²+2B`
whenever `v ≥ 0`, `|v_x| ≤ 2B`, `|v_xx| ≤ 2B`. -/
theorem flux_coeff_bound
    {β v vx vxx B : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B) (hv : 0 ≤ v)
    (hvx : |vx| ≤ 2 * B) (hvxx : |vxx| ≤ 2 * B) :
    |(-β * (1 + v) ^ (-β - 1) * vx ^ 2 + (1 + v) ^ (-β) * vxx)|
      ≤ fluxCoeffConst β B := by
  have h1v : (1 : ℝ) ≤ 1 + v := by linarith
  have h1v_pos : (0 : ℝ) < 1 + v := by linarith
  -- `(1+v)^{−β} ≤ 1`.
  have hφ_le : (1 + v) ^ (-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1v (by linarith)
  have hφ_nonneg : 0 ≤ (1 + v) ^ (-β) := Real.rpow_nonneg h1v_pos.le _
  -- `(1+v)^{−β−1} ≤ 1`.
  have hφ1_le : (1 + v) ^ (-β - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1v (by linarith)
  have hφ1_nonneg : 0 ≤ (1 + v) ^ (-β - 1) := Real.rpow_nonneg h1v_pos.le _
  -- `vx² ≤ (2B)²`  and  `|vxx| ≤ 2B`.
  have hvx_sq : vx ^ 2 ≤ (2 * B) ^ 2 := by
    have := abs_le.mp hvx
    nlinarith [sq_nonneg vx, sq_nonneg (2 * B)]
  have hvx_sq_nonneg : 0 ≤ vx ^ 2 := sq_nonneg _
  have h2B_nonneg : 0 ≤ 2 * B := by linarith
  -- Triangle inequality on the two terms.
  calc |(-β * (1 + v) ^ (-β - 1) * vx ^ 2 + (1 + v) ^ (-β) * vxx)|
      ≤ |(-β * (1 + v) ^ (-β - 1) * vx ^ 2)| + |((1 + v) ^ (-β) * vxx)| :=
        abs_add_le _ _
    _ = β * (1 + v) ^ (-β - 1) * vx ^ 2 + (1 + v) ^ (-β) * |vxx| := by
        rw [abs_mul, abs_mul, abs_mul]
        rw [abs_of_nonneg hvx_sq_nonneg, abs_of_nonneg hφ1_nonneg,
          abs_of_nonneg hφ_nonneg, abs_neg, abs_of_nonneg hβ]
    _ ≤ β * 1 * (2 * B) ^ 2 + 1 * (2 * B) := by
        refine add_le_add ?_ ?_
        · refine mul_le_mul ?_ hvx_sq hvx_sq_nonneg (by positivity)
          exact mul_le_mul_of_nonneg_left hφ1_le hβ
        · exact mul_le_mul hφ_le hvxx (abs_nonneg _) (by norm_num)
    _ = fluxCoeffConst β B := by unfold fluxCoeffConst; ring

end ShenWork.MinPersistenceAtoms
