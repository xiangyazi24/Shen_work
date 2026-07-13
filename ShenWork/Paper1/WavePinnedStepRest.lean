import ShenWork.Paper1.WavePinnedStepComparison
import ShenWork.Paper1.WaveLocalStepPositivity

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- After one lower-pinned smooth step is available, the next genuine local
Green step automatically has both order fields required by the Route-A orbit.
This closes every successor beyond the kinked seed. -/
theorem PaperLocalFixedStepData.rest_of_lowerPinned_old
    {p : CMParams} {c lam M κ κtilde D Λ B Cmono : ℝ}
    {u Z₀ : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hbox : PaperFrozenEllipticSourceBox p κ M)
    (hχ : p.χ ≤ 0)
    (hpinnedSmall :
      (1 / lam) * paperPinnedStepCmono p c lam M κ κtilde D B < 1)
    (hrouteSmall : (1 / lam) * Cmono < 1)
    (hrouteCmono :
      paperCmono p (-p.χ) M (M ^ p.γ) (2 * M ^ p.γ) ≤ Cmono)
    (dOld : PaperLocalFixedStepData p c lam M κ Λ B u Z₀)
    (hOldPinned : InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D) dOld.fixed.W)
    (hOldSuper : ∀ x, paperWaveOperator p c u dOld.fixed.W x ≤ 0)
    (dNew : PaperLocalFixedStepData p c lam M κ Λ B u dOld.fixed.W) :
    PaperLocalFixedStepRestData p c lam M κ Λ B u dOld.fixed.W dNew := by
  have hDpos : 0 < D := hD
  have hOldPos : ∀ x, 0 < dOld.fixed.W x := by
    intro x
    exact lt_of_lt_of_le
      (lowerBarrierPlateau_pos hκ hgap hDpos x)
      (plateau_le_of_lowerPinnedRaw hOldPinned x)
  have hOldOne : ContDiff ℝ 1 dOld.fixed.W :=
    (dOld.contDiff_two hlam).of_le (by norm_num)
  refine
    { le_old := PaperLocalFixedStepData.le_old_of_lowerPinned_old
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
        (κtilde := κtilde) (D := D) (Λ := Λ) (B := B)
        (u := u) (Z₀ := Z₀)
        hlam hrpκ hrmκ hκ hgap hD hM hB hu hbox hχ hpinnedSmall
        dOld (fun x => plateau_le_of_lowerPinnedRaw hOldPinned x)
        hOldSuper dNew
      anti := ?_ }
  exact dNew.antitone_of_old_pos_contDiff_one
    hlam hu hbox hχ hrouteSmall hrouteCmono
      hOldOne hOldPos hOldPinned.bare.antitone

section AxiomAudit

#print axioms PaperLocalFixedStepData.rest_of_lowerPinned_old

end AxiomAudit

end ShenWork.Paper1
