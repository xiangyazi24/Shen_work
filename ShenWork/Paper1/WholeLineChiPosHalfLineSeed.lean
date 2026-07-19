import ShenWork.Paper1.WholeLineChiPosPlateauPersistence
import ShenWork.Paper1.WholeLineChiPosHalfLineRectangle

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Initial positive-sensitivity half-line rectangle

The persistent lower plateau supplies a uniform positive floor on one
co-moving left half-line.  Its trap height `Q` lies strictly above `MChi p`,
so the same `Q` also provides a strict ceiling margin.  Shrinking the extracted
floor gives the strict floor margin required by the half-line iteration.
-/

/-- The canonical positive-sensitivity orbit eventually lies in a strict
rectangle on a fixed co-moving left half-line. -/
theorem exists_initial_chiPosHalfLineRectangle
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_lt : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    {c eta kappaOne : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hkappaOne : kappa c < kappaOne)
    (hkappaOne_one : kappaOne < 1)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    Nonempty
      (ChiPosHalfLineRectangle p c (wholeLineCauchyGlobalU p u₀)) := by
  obtain ⟨N, kappaTilde, D, Q, hMChiQ, hQone, hQtrap,
      hkappaTilde, _hkappaTildeOne, _hkappaTildeEta, hcond, hD1,
      _hDscaled, _hplateau, _htrap, hpersist⟩ :=
    wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_pos_natural
      p hregime hchi hchi_lt hcritical hc hTW hreg hstrict hkappaOne
        hkappaOne_one htail hroot hetaCap u₀ hu₀ hleft hinitial
  obtain ⟨Tlower, R, d, hd, hlower⟩ :=
    wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau
      p u₀ hcond.hκ0 hkappaTilde hD1 hpersist
  have hchi_one : p.χ < 1 := by linarith
  obtain ⟨ellRaw, hellRaw, hellRaw_one, hfloorRawExpanded⟩ :=
    exists_ell_with_positive_rectangle_floor_margin
      p (fun _hm => hQtrap)
  have hfloorRaw : 0 < chiPosFloorGap p Q ellRaw := by
    simpa only [chiPosFloorGap, mul_assoc] using hfloorRawExpanded
  let ell : ℝ := min (d / 2) (ellRaw / 2)
  have hell : 0 < ell := by
    dsimp only [ell]
    exact lt_min (half_pos hd) (half_pos hellRaw)
  have hell_d : ell ≤ d := by
    have : ell ≤ d / 2 := by
      dsimp only [ell]
      exact min_le_left _ _
    linarith
  have hell_ellRaw : ell < ellRaw := by
    have : ell ≤ ellRaw / 2 := by
      dsimp only [ell]
      exact min_le_right _ _
    linarith
  have hell_one : ell < 1 := hell_ellRaw.trans hellRaw_one
  have hQnonneg : 0 ≤ Q := zero_le_one.trans hQone.le
  have hfloorMargin : 0 < chiPosFloorGap p Q ell := by
    have hanti := chiPosFloorGap_strictAntiOn_Ioi
      hcritical hchi.le hchi_one hQnonneg
      (show ell ∈ Set.Ioi (0 : ℝ) from hell)
      (show ellRaw ∈ Set.Ioi (0 : ℝ) from hellRaw)
      hell_ellRaw
    exact hfloorRaw.trans hanti
  have hceilingMargin : 0 < chiPosCeilingGap p ell Q := by
    simpa only [chiPosCeilingGap, mul_assoc] using
      chiPos_rectangle_ceiling_margin_pos_of_MChi_lt
        p hchi hchi_one hcritical hMChiQ hell.le
  have hlimsup := wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
    p hchi hchi_one hcritical
      hregime.toWholeLineCauchyCeilingRegime u₀ hu₀
  obtain ⟨Tupper, hTupper⟩ := eventually_atTop.1
    (hlimsup (Q - MChi p) (sub_pos.mpr hMChiQ))
  refine ⟨
    { ell := ell
      M := Q
      start := max Tlower Tupper
      cut := R
      ell_pos := hell
      ell_lt_one := hell_one
      one_lt_M := hQone
      floor_margin := hfloorMargin
      ceiling_margin := hceilingMargin
      bounds := ?_ }⟩
  intro t ht z hz
  have htLower : Tlower ≤ t := (le_max_left _ _).trans ht
  have htUpper : Tupper ≤ t := (le_max_right _ _).trans ht
  have hlo : ell ≤ coMovingPath c
      (wholeLineCauchyGlobalU p u₀) t z := by
    exact hell_d.trans (by
      simpa only [coMovingPath] using hlower t htLower z hz)
  have hupRaw := hTupper t htUpper (z + c * t)
  have hup : coMovingPath c
      (wholeLineCauchyGlobalU p u₀) t z ≤ Q := by
    dsimp only [coMovingPath]
    linarith [hupRaw]
  exact ⟨hlo, hup⟩

section AxiomAudit

#print axioms exists_initial_chiPosHalfLineRectangle

end AxiomAudit

end ShenWork.Paper1
