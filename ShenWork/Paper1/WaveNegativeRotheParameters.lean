import ShenWork.Paper1.WaveGreenParameterAsymptotics
import ShenWork.Paper1.WaveLemma42Paper
import ShenWork.Paper1.WaveNegativeSuperBarrier
import ShenWork.Paper1.WaveLemma42ParamCore

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Global scalar choices for every local Green step in the negative headline
branch.  The constants are independent of the frozen profile and the old
iterate; only the comparison/Route-A analytic theorem remains profile-indexed. -/
structure Paper1NegativeLocalStepScalarData
    (p : CMParams) (c : ℝ) : Type where
  lam : ℝ
  B : ℝ
  Λ : ℝ
  Cmono : ℝ
  hlam : 0 < lam
  hκ : 0 < kappa c
  hrpκ : kappa c < greenRootPlus c lam
  hrmκ : kappa c < -greenRootMinus c lam
  hB : 0 ≤ B
  hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * (B * 1)
  hΛ0 : 0 ≤ Λ
  Cmono_eq : Cmono = paperCmono p (-p.χ) 1 1 2
  Cmono_small : (1 / lam) * Cmono < 1
  sourceScalar :
    |(-p.χ * p.m)| * (1 : ℝ) ^ (p.m - 1) * (1 : ℝ) ^ p.γ *
          greenWeightedMass1 c lam (kappa c) * B
      + (1 + |p.χ| * (1 : ℝ) ^ (p.m - 1) * (1 : ℝ) ^ p.γ
          + (1 : ℝ) ^ p.α + |p.χ| * (1 : ℝ) ^ (p.m + p.γ - 1))
      + lam ≤ B
  barrier : PaperUpperBarrierSuperScalarConditions p c (kappa c) 1

/-- Large resolvent parameter simultaneously closes both characteristic-root
conditions, the weighted Green derivative budget, and the Route-A strict
maximum-principle gap. -/
theorem paper1NegativeLocalStepScalarData_exists
    (p : CMParams) {c : ℝ}
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    (hc : cStarLower p < c) :
    Nonempty (Paper1NegativeLocalStepScalarData p c) := by
  let κ : ℝ := kappa c
  let A : ℝ := |(-p.χ * p.m)|
  let C : ℝ := 2 + 2 * |p.χ|
  let Cmono : ℝ := paperCmono p (-p.χ) 1 1 2
  have hmassT : Tendsto
      (fun lam : ℝ => A * greenWeightedMass1 c lam κ) atTop (nhds 0) := by
    simpa [A] using (greenWeightedMass1_tendsto_zero c κ).const_mul A
  have hmass : ∀ᶠ lam in atTop,
      A * greenWeightedMass1 c lam κ < 1 / 2 :=
    hmassT.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hrp : ∀ᶠ lam in atTop, κ < greenRootPlus c lam :=
    (greenRootPlus_tendsto_atTop c).eventually_gt_atTop κ
  have hrm : ∀ᶠ lam in atTop, κ < -greenRootMinus c lam :=
    (neg_greenRootMinus_tendsto_atTop c).eventually_gt_atTop κ
  have hlamLarge : ∀ᶠ lam : ℝ in atTop, max Cmono 0 < lam :=
    eventually_gt_atTop (max Cmono 0)
  obtain ⟨lam, hmassLam, hrpLam, hrmLam, hlamLarge⟩ :=
    (hmass.and (hrp.and (hrm.and hlamLarge))).exists
  have hlam : 0 < lam := lt_of_le_of_lt (le_max_right Cmono 0) hlamLarge
  have hCmonoLam : Cmono < lam :=
    lt_of_le_of_lt (le_max_left Cmono 0) hlamLarge
  have hsmall : (1 / lam) * Cmono < 1 := by
    rw [one_div_mul_eq_div]
    exact (div_lt_one hlam).2 hCmonoLam
  let B : ℝ := 2 * (C + lam)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmass0 :
      0 ≤ A * greenWeightedMass1 c lam κ := by
    exact mul_nonneg (abs_nonneg _)
      (greenWeightedMass1_nonneg hlam hrpLam hrmLam)
  have hsource :
      A * greenWeightedMass1 c lam κ * B + C + lam ≤ B := by
    have hmul :
        A * greenWeightedMass1 c lam κ * B ≤ (1 / 2 : ℝ) * B :=
      mul_le_mul_of_nonneg_right hmassLam.le hB
    dsimp [B]
    nlinarith
  let Λ : ℝ := 2 * (greenDelta c lam)⁻¹ * (B * 1)
  have hΛ0 : 0 ≤ Λ := by
    dsimp [Λ]
    exact mul_nonneg
      (mul_nonneg zero_le_two
        (inv_nonneg.mpr (greenDelta_pos (c := c) hlam).le))
      (mul_nonneg hB zero_le_one)
  refine
    ⟨{ lam := lam
       B := B
       Λ := Λ
       Cmono := Cmono
       hlam := hlam
       hκ := kappa_pos_of_cStarLower_lt hc
       hrpκ := hrpLam
       hrmκ := hrmLam
       hB := hB
       hΛ := rfl
       hΛ0 := hΛ0
       Cmono_eq := rfl
       Cmono_small := hsmall
       sourceScalar := ?_
       barrier :=
         paperUpperBarrierSuperScalarConditions_one_of_cStarLower_lt
           p hχ hα hc }⟩
  simp only [Real.one_rpow, mul_one]
  change A * greenWeightedMass1 c lam κ * B +
      (1 + |p.χ| + 1 + |p.χ|) + lam ≤ B
  rw [show 1 + |p.χ| + 1 + |p.χ| = C by
    dsimp [C]
    ring]
  exact hsource

namespace Paper1NegativeLocalStepScalarData

/-- Attach one trapped frozen profile and the genuinely profile-indexed order
theorem to the global scalar choices.  Every source-box and barrier field is
then already discharged. -/
def toLocalRouteAStepParameters
    {p : CMParams} {c : ℝ}
    (h : Paper1NegativeLocalStepScalarData p c)
    {u : ℝ → ℝ}
    (hu : InMonotoneWaveTrapSet (kappa c) 1 u)
    (hrest : PaperLocalFixedStepRestProvider
      p c h.lam 1 (kappa c) h.Λ u) :
    PaperLocalRouteAStepParameters p c h.lam 1 (kappa c) h.Λ u :=
  { B := h.B
    hlam := h.hlam
    hrpκ := h.hrpκ
    hrmκ := h.hrmκ
    hκ := h.hκ
    hM := one_pos
    hB := h.hB
    chi_nonpos := h.barrier.hχ
    hu := hu
    sourceScalar := h.sourceScalar
    barrier := h.barrier
    derivBound := h.hΛ
    rest := hrest }

end Paper1NegativeLocalStepScalarData

section AxiomAudit

#print axioms paper1NegativeLocalStepScalarData_exists
#print axioms Paper1NegativeLocalStepScalarData.toLocalRouteAStepParameters

end AxiomAudit

end ShenWork.Paper1
