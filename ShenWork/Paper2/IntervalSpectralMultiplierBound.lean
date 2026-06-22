import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
  Brick 1 of the two-step parabolic-smoothing bootstrap (Paper 2).

  The sharp scalar spectral multiplier bound
    `λ^θ · exp(−d·r·λ) ≤ C_θ · d^(−θ) · r^(−θ)`,
  with `C_θ = θ^θ · exp(−θ)` (the value of `sup_λ λ^θ e^{−d r λ}` at
  `λ = θ/(d r)`).  This generalizes the proven `θ = 1` scalar case in
  `IntervalBFormDirectSmoothingCalc` to an arbitrary real exponent `θ > 0`,
  the exponent needed by the fractional H^σ smoothing estimate
  (there `θ = (σ+1)/2`).

  Stated existentially (the `∃ C_θ > 0` form requested by the design note), and
  also in the explicit-constant form.
-/

noncomputable section

namespace ShenWork.Paper2.SpectralMultiplierBound

open Real

/-- Core scalar maximum: `y^θ · exp(−y) ≤ θ^θ · exp(−θ)` for `θ, y ≥ 0`.
The maximum of `y ↦ y^θ e^{−y}` is attained at `y = θ`. -/
theorem rpow_mul_exp_neg_le (θ y : ℝ) (hθ : 0 < θ) (hy : 0 ≤ y) :
    y ^ θ * Real.exp (-y) ≤ θ ^ θ * Real.exp (-θ) := by
  rcases eq_or_lt_of_le hy with hy0 | hy0
  · -- y = 0: lhs = 0 ≤ rhs.
    have hlhs : (0 : ℝ) ^ θ * Real.exp (-0 : ℝ) = 0 := by
      rw [Real.zero_rpow (ne_of_gt hθ)]; ring
    rw [← hy0, hlhs]
    positivity
  · -- y > 0: take logs.  log(y^θ e^{−y}) = θ log y − y.
    -- Want: θ log y − y ≤ θ log θ − θ, i.e. θ (log y − log θ) ≤ y − θ,
    -- i.e. θ · log (y/θ) ≤ y − θ, which is `log (y/θ) ≤ y/θ − 1` scaled by θ.
    have hlogkey : θ * Real.log y - y ≤ θ * Real.log θ - θ := by
      have hquot : Real.log (y / θ) ≤ y / θ - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hlogdiv : Real.log (y / θ) = Real.log y - Real.log θ := by
        rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hθ)]
      rw [hlogdiv] at hquot
      have hscaled : θ * (Real.log y - Real.log θ) ≤ θ * (y / θ - 1) :=
        mul_le_mul_of_nonneg_left hquot hθ.le
      have hrhs : θ * (y / θ - 1) = y - θ := by
        field_simp
      nlinarith [hscaled, hrhs]
    -- Exponentiate back.
    have hlhs_pos : 0 < y ^ θ * Real.exp (-y) := by positivity
    have hrhs_pos : 0 < θ ^ θ * Real.exp (-θ) := by positivity
    have hloglhs : Real.log (y ^ θ * Real.exp (-y)) = θ * Real.log y - y := by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_rpow hy0, Real.log_exp]
      ring
    have hlogrhs : Real.log (θ ^ θ * Real.exp (-θ)) = θ * Real.log θ - θ := by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_rpow hθ, Real.log_exp]
      ring
    have hlog_le : Real.log (y ^ θ * Real.exp (-y))
        ≤ Real.log (θ ^ θ * Real.exp (-θ)) := by
      rw [hloglhs, hlogrhs]; exact hlogkey
    exact (Real.log_le_log_iff hlhs_pos hrhs_pos).mp hlog_le

/-- The explicit-constant spectral multiplier bound:
`λ^θ · exp(−d·r·λ) ≤ (θ^θ exp(−θ)) · (d·r)^(−θ)` for `θ, d, r > 0`, `λ ≥ 0`. -/
theorem spectral_multiplier_bound_explicit
    {θ d r lam : ℝ} (hθ : 0 < θ) (hd : 0 < d) (hr : 0 < r) (hlam : 0 ≤ lam) :
    lam ^ θ * Real.exp (-(d * r * lam)) ≤
      (θ ^ θ * Real.exp (-θ)) * (d * r) ^ (-θ) := by
  set y : ℝ := d * r * lam with hy_def
  have hdr : 0 < d * r := by positivity
  have hy : 0 ≤ y := by positivity
  -- λ = y/(d r), so λ^θ = y^θ · (d r)^(−θ).
  have hlam_rpow : lam ^ θ = y ^ θ * (d * r) ^ (-θ) := by
    have hlam_eq : lam = y / (d * r) := by
      rw [hy_def]; field_simp
    rw [hlam_eq, Real.div_rpow hy hdr.le, Real.rpow_neg hdr.le]
    rw [div_eq_mul_inv]
  rw [hlam_rpow]
  calc
    y ^ θ * (d * r) ^ (-θ) * Real.exp (-y)
        = (y ^ θ * Real.exp (-y)) * (d * r) ^ (-θ) := by ring
    _ ≤ (θ ^ θ * Real.exp (-θ)) * (d * r) ^ (-θ) := by
        apply mul_le_mul_of_nonneg_right (rpow_mul_exp_neg_le θ y hθ hy)
        positivity

/-- Existential form requested by the design note:
`∃ C_θ > 0, ∀ d r λ, 0 < d → 0 < r → 0 ≤ λ →
   λ^θ exp(−d r λ) ≤ C_θ · d^(−θ) · r^(−θ)`. -/
theorem spectral_multiplier_bound (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ d r lam : ℝ, 0 < d → 0 < r → 0 ≤ lam →
        lam ^ θ * Real.exp (-(d * r * lam)) ≤ C * d ^ (-θ) * r ^ (-θ) := by
  refine ⟨θ ^ θ * Real.exp (-θ), by positivity, ?_⟩
  intro d r lam hd hr hlam
  have h := spectral_multiplier_bound_explicit (θ := θ) (d := d) (r := r)
    (lam := lam) hθ hd hr hlam
  -- (d r)^(−θ) = d^(−θ) r^(−θ).
  have hsplit : (d * r) ^ (-θ) = d ^ (-θ) * r ^ (-θ) :=
    Real.mul_rpow hd.le hr.le
  rw [hsplit] at h
  calc
    lam ^ θ * Real.exp (-(d * r * lam))
        ≤ (θ ^ θ * Real.exp (-θ)) * (d ^ (-θ) * r ^ (-θ)) := h
    _ = (θ ^ θ * Real.exp (-θ)) * d ^ (-θ) * r ^ (-θ) := by ring

#print axioms rpow_mul_exp_neg_le
#print axioms spectral_multiplier_bound_explicit
#print axioms spectral_multiplier_bound

end ShenWork.Paper2.SpectralMultiplierBound
