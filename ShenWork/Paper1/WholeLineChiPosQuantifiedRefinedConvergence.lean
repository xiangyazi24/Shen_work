import ShenWork.Paper1.WholeLineChiPosQuantifiedHalfLineSeed
import ShenWork.Paper1.WholeLineChiPosRefinedHalfLineRectangle

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Refined convergence from the quantified half-line seed

The contraction coefficient below is evaluated at the explicit aspect-ratio
lower bound `ell₀ / (MChi p + 1)`.  Both quantities depend only on the equation
parameters, not on the initial datum.
-/

/-- Critical positive-sensitivity far-left convergence under the refined
contraction condition furnished by the explicit quantified seed. -/
theorem
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_quantified
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_lt : p.χ < 1) (hm : 1 < p.m)
    (hcritical : p.α = p.m + p.γ - 1)
    (hcontract : p.χ * p.γ < p.α *
      (1 - p.χ *
        ((1 -
            ((min (1 / 4 : ℝ)
                ((1 / (8 * (1 + p.χ * (MChi p + 1) ^ p.γ))) ^
                  (1 / (p.m - 1))) / 2) / (MChi p + 1)) ^ p.γ) /
          (1 -
            ((min (1 / 4 : ℝ)
                ((1 / (8 * (1 + p.χ * (MChi p + 1) ^ p.γ))) ^
                  (1 / (p.m - 1))) / 2) / (MChi p + 1)) ^ p.α))))
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
  let Q : ℝ := MChi p + 1
  let ell₀ : ℝ :=
    min (1 / 4 : ℝ)
        ((1 / (8 * (1 + p.χ * Q ^ p.γ))) ^ (1 / (p.m - 1))) / 2
  have hMChi_pos : 0 < MChi p := MChi_pos_of_chi_lt_one p hchi_lt
  have hQone : 1 < Q := by
    dsimp [Q]
    linarith
  have hQpos : 0 < Q := zero_lt_one.trans hQone
  obtain ⟨_L, _hL, _hLone, _hreserve, hell₀raw, _hell₀L⟩ :=
    exists_chiPos_quantified_floor_with_halfKernel_reserve
      p hm hchi.le Q hQone
  have hell₀ : 0 < ell₀ := by
    simpa only [ell₀] using hell₀raw
  obtain ⟨seed, hseedEll, hseedM⟩ :=
    exists_initial_chiPosHalfLineRectangle_quantified
      p hregime hchi hchi_lt hm hcritical hc hTW hreg hbound hroot
        hetaCap u₀ hu₀ hleft hinitial
  have hcontract' : p.χ * p.γ < p.α *
      (1 - p.χ * ((1 - (ell₀ / Q) ^ p.γ) /
        (1 - (ell₀ / Q) ^ p.α))) := by
    simpa only [ell₀, Q] using hcontract
  have hgamma : 0 < p.γ := zero_lt_one.trans_le p.hγ
  have hs : 0 ≤ p.m - 1 := by linarith
  have hsum : (p.m - 1) + p.γ = p.α := by
    rw [hcritical]
    ring
  have ht₀ : 0 < ell₀ / Q := div_pos hell₀ hQpos
  refine
    uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_refined
      p hm hchi.le hcritical hcontract' seed ?_
        (fun delta hdelta old =>
          exists_next_chiPosHalfLineRectangle
            p hregime hchi hchi_lt hcritical hc hTW hreg hbound hroot
              hetaCap u₀ hu₀ hleft hinitial hdelta old)
  intro r hell hM
  have hrM : 0 < r.M := zero_lt_one.trans r.one_lt_M
  have hlt : r.ell < r.M := r.ell_lt_one.trans r.one_lt_M
  have hell₀r : ell₀ ≤ r.ell := by
    have hseedEll' : ell₀ ≤ seed.ell := by
      simpa only [ell₀, Q] using hseedEll
    exact hseedEll'.trans hell
  have hrMQ : r.M ≤ Q := by
    have hseedM' : seed.M ≤ Q := by
      simpa only [Q] using hseedM
    exact hM.trans hseedM'
  have hratio : ell₀ / Q ≤ r.ell / r.M := by
    rw [div_le_div_iff₀ hQpos hrM]
    exact (mul_le_mul_of_nonneg_right hell₀r hrM.le).trans
      (mul_le_mul_of_nonneg_left hrMQ r.ell_pos.le)
  exact rpow_large_prefactor_gap_le_of_ratio_ge
    r.ell_pos hlt.le hs hgamma hsum ht₀ hratio hlt

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_quantified

end AxiomAudit

end ShenWork.Paper1
