import ShenWork.Paper1.WholeLineWeightedRegularityChiPosLeftEquilibriumMGTOneNatural

/-!
# The sharp `m > 1` threshold covers the paper's full window when `m ≥ γ + 2`

The sharp half-line rectangle closes whenever

`chi * gamma < alpha * (1 - chi)`,  i.e.  `chi < alpha / (alpha + gamma)`.

Paper 1 Theorem 1.2 asserts stability on `0 ≤ chi < chiStar p`, where
`chiStar p = min 1 ((2 m + 2 γ) / (m ^ 2 + m + 2 γ))`.

At the critical exponent `alpha = m + γ - 1` the comparison

`chiStar p ≤ alpha / (alpha + gamma)`

holds exactly when the cubic

`P (m, γ) = m ^ 3 + m ^ 2 * (γ - 2) + m * (1 - 3 γ) - 2 γ ^ 2`

is nonnegative, and `γ + 2 ≤ m` is a clean sufficient condition: writing
`m = γ + 2 + s` with `s ≥ 0` turns `P` into a polynomial in `(γ, s)` with all
coefficients nonnegative and constant term `2`.

Consequence (`..._chi_pos_full_window` below): for `γ + 2 ≤ m` at the critical
exponent, the far-left equilibrium step — and hence Theorem 1.2's weighted and
uniform moving-frame convergence — is unconditional on the **entire** window
`0 < chi < chiStar p` claimed by the paper, not merely on `chi < 1 / 2`.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- The cubic governing `chiStar ≤ alpha / (alpha + gamma)` is positive as soon
as `gamma + 2 ≤ m`. -/
theorem sharpThreshold_cubic_pos {m g : ℝ} (hg : 0 ≤ g) (hmg : g + 2 ≤ m) :
    0 < m ^ 3 + m ^ 2 * (g - 2) + m * (1 - 3 * g) - 2 * g ^ 2 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ m = g + 2 + s :=
    ⟨m - g - 2, by linarith, by ring⟩
  have hrewrite :
      (g + 2 + s) ^ 3 + (g + 2 + s) ^ 2 * (g - 2) + (g + 2 + s) * (1 - 3 * g)
          - 2 * g ^ 2
        = 2 * g ^ 3 + 5 * g ^ 2 * s + 3 * g ^ 2 + 4 * g * s ^ 2 + 9 * g * s
            + 3 * g + s ^ 3 + 4 * s ^ 2 + 5 * s + 2 := by ring
  rw [hrewrite]
  have t1 : 0 ≤ g ^ 3 := pow_nonneg hg 3
  have t2 : 0 ≤ g ^ 2 * s := mul_nonneg (sq_nonneg g) hs
  have t3 : 0 ≤ g ^ 2 := sq_nonneg g
  have t4 : 0 ≤ g * s ^ 2 := mul_nonneg hg (sq_nonneg s)
  have t5 : 0 ≤ g * s := mul_nonneg hg hs
  have t6 : 0 ≤ s ^ 3 := pow_nonneg hs 3
  have t7 : 0 ≤ s ^ 2 := sq_nonneg s
  linarith

/-- At the critical exponent with `gamma + 2 ≤ m`, the paper's threshold
`chiStar` is dominated by the sharp rectangle threshold
`alpha / (alpha + gamma)`. -/
theorem chiStar_le_sharpThreshold (p : CMParams)
    (hcritical : p.α = p.m + p.γ - 1) (hmg : p.γ + 2 ≤ p.m) :
    chiStar p ≤ p.α / (p.α + p.γ) := by
  have hg1 : (1 : ℝ) ≤ p.γ := p.hγ
  have hg0 : (0 : ℝ) ≤ p.γ := zero_le_one.trans hg1
  have hm3 : (3 : ℝ) ≤ p.m := by linarith
  have halpha : 0 < p.α := by rw [hcritical]; linarith
  have hden1 : 0 < p.α + p.γ := by linarith
  have hden2 : 0 < p.m ^ 2 + p.m + 2 * p.γ := by nlinarith
  refine (min_le_right _ _).trans ?_
  rw [div_le_div_iff₀ hden2 hden1]
  have hcubic := sharpThreshold_cubic_pos hg0 hmg
  rw [hcritical]
  nlinarith [hcubic]

/-- **Theorem 1.2, positive sensitivity, full paper window for `γ + 2 ≤ m`.**
No `chi < 1 / 2` restriction: the sharp `m > 1` half-line rectangle covers the
whole range `0 < chi < chiStar p` asserted by the paper. -/
theorem
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_full_window
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_star : p.χ < chiStar p)
    (hcritical : p.α = p.m + p.γ - 1) (hmg : p.γ + 2 ≤ p.m)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    IsGlobalCauchySolutionFrom p u₀.1
        (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) ∧
      CoMovingWeightedL2Convergence eta c (wholeLineCauchyGlobalU p u₀) U ∧
        UniformMovingFrameConvergence c (wholeLineCauchyGlobalU p u₀) U := by
  have hg1 : (1 : ℝ) ≤ p.γ := p.hγ
  have hm : 1 < p.m := by linarith
  have halpha : 0 < p.α := by rw [hcritical]; linarith
  have hden1 : 0 < p.α + p.γ := by linarith
  have hchi_one : p.χ < 1 := lt_of_lt_of_le hchi_star (min_le_left _ _)
  have hchi_thr : p.χ < p.α / (p.α + p.γ) :=
    hchi_star.trans_le (chiStar_le_sharpThreshold p hcritical hmg)
  have hcontract : p.χ * p.γ < p.α * (1 - p.χ) := by
    have := (lt_div_iff₀ hden1).1 hchi_thr
    nlinarith [this]
  exact
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_m_gt_one
      p hregime hchi hchi_one hm hcritical hcontract hc hTW hreg hbound
        hroot hetaCap u₀ hu₀ hleft hinitial

/-- The far-left equilibrium step alone, on the full paper window. -/
theorem
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_full_window
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_star : p.χ < chiStar p)
    (hcritical : p.α = p.m + p.γ - 1) (hmg : p.γ + 2 ≤ p.m)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) := by
  have hg1 : (1 : ℝ) ≤ p.γ := p.hγ
  have hm : 1 < p.m := by linarith
  have halpha : 0 < p.α := by rw [hcritical]; linarith
  have hden1 : 0 < p.α + p.γ := by linarith
  have hchi_one : p.χ < 1 := lt_of_lt_of_le hchi_star (min_le_left _ _)
  have hchi_thr : p.χ < p.α / (p.α + p.γ) :=
    hchi_star.trans_le (chiStar_le_sharpThreshold p hcritical hmg)
  have hcontract : p.χ * p.γ < p.α * (1 - p.χ) := by
    have := (lt_div_iff₀ hden1).1 hchi_thr
    nlinarith [this]
  exact
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_m_gt_one
      p hregime hchi hchi_one hm hcritical hcontract hc hTW hreg hbound
        hroot hetaCap u₀ hu₀ hleft hinitial

section AxiomAudit

#print axioms sharpThreshold_cubic_pos
#print axioms chiStar_le_sharpThreshold
#print axioms
  wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_full_window
#print axioms
  wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_full_window

end AxiomAudit

end ShenWork.Paper1
