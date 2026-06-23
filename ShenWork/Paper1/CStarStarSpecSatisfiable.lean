import ShenWork.Paper1.Statements

/-!
# §3.3 non-vacuity: the (now `≤`) `cStarStar_spec` is satisfiable

After the faithful refactor of the `cStarStar` faithfulness clause from strict
`<` to `≤` (the paper's `c** > 1+|χ|^{1/6}+(1+|χ|^{1/6})⁻¹` holds with equality
at the degenerate stable-regime boundary `χ = 0, γ = 1`, which the paper
explicitly includes), we confirm the bundle is no longer vacuous: there is a
concrete threshold family `cStarStarFn` that simultaneously satisfies the
`|χ|^{1/6}` asymptotic AND the baseline lower bound for *every* stable-regime
parameter, including the degenerate point.

The witness is `cStarStarFn p χ := (p.γ + p.γ⁻¹) + |χ|^{1/6}`.
* Asymptotic: `|cStarStarFn p χ - (γ+γ⁻¹)| = |χ|^{1/6} ≤ 1·|χ|^{1/6}` (A=1, δ=1).
* Baseline `≤`: reduces to `1 + (1+|χ|^{1/6})⁻¹ ≤ γ + γ⁻¹`, where the left side
  is `≤ 2` (the inverse of a quantity `≥ 1` is `≤ 1`) and the right side is `≥ 2`
  (AM–GM for `γ ≥ 1`).  At `χ = 0, γ = 1` both sides are exactly `2`: equality.
-/

namespace ShenWork.Paper1

/-- Concrete satisfying threshold family for the (now `≤`) `cStarStar_spec`. -/
noncomputable def cStarStarWitness (p : CMParams) (χ : ℝ) : ℝ :=
  (p.γ + p.γ⁻¹) + |χ| ^ (1 / 6 : ℝ)

theorem cStarStarWitness_asymptotic (p : CMParams) :
    StabilitySpeedThresholdFamilyAsymptotic p (cStarStarWitness p) := by
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro χ _hχ
  have hpow_nonneg : 0 ≤ |χ| ^ (1 / 6 : ℝ) := Real.rpow_nonneg (abs_nonneg χ) _
  have : cStarStarWitness p χ - (p.γ + p.γ⁻¹) = |χ| ^ (1 / 6 : ℝ) := by
    unfold cStarStarWitness; ring
  rw [this, abs_of_nonneg hpow_nonneg, one_mul]

theorem stabilitySpeedBaseline_le_cStarStarWitness (p : CMParams) :
    stabilitySpeedBaseline p ≤ cStarStarWitness p p.χ := by
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) := Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_pos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by linarith
  have hinv_le_one : (1 + |p.χ| ^ (1 / 6 : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith)
  -- `γ + γ⁻¹ ≥ 2` from AM–GM (γ ≥ 1 > 0)
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le one_pos p.hγ
  have hγinv_pos : 0 < p.γ⁻¹ := inv_pos.mpr hγ_pos
  have hγ_mul : p.γ * p.γ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hγ_pos)
  have hge_two : (2 : ℝ) ≤ p.γ + p.γ⁻¹ := by
    nlinarith [sq_nonneg (p.γ - 1), hγ_mul, hγ_pos]
  unfold stabilitySpeedBaseline cStarStarWitness
  -- reduces to `1 + (1+t)⁻¹ ≤ γ + γ⁻¹` after cancelling `t = |χ|^{1/6}`
  nlinarith [hinv_le_one, hge_two]

/-- §3.3 non-vacuity confirmation: the (now `≤`) `cStarStar_spec` interface is
satisfiable by a concrete threshold family, for every stable-regime parameter
including the degenerate `χ = 0, γ = 1` boundary point. -/
theorem cStarStar_spec_satisfiable :
    ∃ cStarStarFn : CMParams → ℝ → ℝ,
      ∀ p : CMParams, StableWaveParameterRegime p →
        StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
          stabilitySpeedBaseline p ≤ cStarStarFn p p.χ := by
  refine ⟨cStarStarWitness, ?_⟩
  intro p _hreg
  exact ⟨cStarStarWitness_asymptotic p, stabilitySpeedBaseline_le_cStarStarWitness p⟩

end ShenWork.Paper1
