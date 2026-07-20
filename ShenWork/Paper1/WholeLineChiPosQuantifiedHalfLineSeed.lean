import ShenWork.Paper1.WholeLineChiPosQuantifiedFloor
import ShenWork.Paper1.WholeLineChiPosHalfLineSeedMGTOne

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# A datum-independent lower bound for the positive-sensitivity seed

An arbitrary positive seed first supplies a strictly positive starting height.
After the global ceiling has settled below `Q = MChi p + 1`, a new floor
barrier is restarted with both its local resolver ceiling and its half-kernel
tail measured against `Q`.  The barrier then grows past the explicit floor
from `WholeLineChiPosQuantifiedFloor`.
-/

/-- The `m > 1` half-line seed can be chosen with an explicit floor and the
datum-independent ceiling `MChi p + 1`. -/
theorem exists_initial_chiPosHalfLineRectangle_quantified
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_lt : p.χ < 1)
    (hm : 1 < p.m)
    (hcritical : p.α = p.m + p.γ - 1)
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
    ∃ seed : ChiPosHalfLineRectangle p c
        (wholeLineCauchyGlobalU p u₀),
      min (1 / 4 : ℝ)
          ((1 / (8 * (1 + p.χ * (MChi p + 1) ^ p.γ))) ^
            (1 / (p.m - 1))) / 2 ≤ seed.ell ∧
      seed.M ≤ MChi p + 1 := by
  have hceiling : WholeLineCauchyCeilingRegime p :=
    Or.inr ⟨hchi.le, Or.inr ⟨hchi_lt, hcritical⟩⟩
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans hroot
  have hweighted : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U :=
    wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural
      p hregime hchi hc hTW hbound hreg hroot hetaCap u₀ hu₀ hinitial
  have hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U :=
    wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
      p hceiling u₀ hu₀ c hTW hreg
  let Q : ℝ := MChi p + 1
  have hMChi_pos : 0 < MChi p := MChi_pos_of_chi_lt_one p hchi_lt
  have hMChiQ : MChi p < Q := by
    dsimp [Q]
    linarith
  have hQone : 1 < Q := by
    dsimp [Q]
    linarith
  obtain ⟨L, hL, hLone, hreserveExpanded, hell₀, hell₀L⟩ :=
    exists_chiPos_quantified_floor_with_halfKernel_reserve
      p hm hchi.le Q hQone
  let ell₀ : ℝ :=
    min (1 / 4 : ℝ)
        ((1 / (8 * (1 + p.χ * Q ^ p.γ))) ^ (1 / (p.m - 1))) / 2
  have hreserve :
      0 < chiPosHalfLineFloorReserve p Q L (1 / 2 : ℝ) Q := by
    simpa only [chiPosHalfLineFloorReserve] using hreserveExpanded
  have hell₀pos : 0 < ell₀ := by
    simpa only [ell₀] using hell₀
  have hell₀L' : ell₀ < L := by
    simpa only [ell₀] using hell₀L
  have hell₀one : ell₀ < 1 := hell₀L'.trans hLone
  obtain ⟨old⟩ := exists_initial_chiPosHalfLineRectangle_m_gt_one
    p hregime hchi hchi_lt hm hcritical hc hTW hreg hbound hroot
      hetaCap u₀ hu₀ hleft hinitial
  obtain ⟨cut, Tbuf, hcutOld, _hcutOld', hbuffer⟩ :=
    exists_eventual_chiPos_farLeft_buffer
      heta hweighted hmod hTW.lim_neg_inf.1
      (L := L) (A := Q) (R := 0) (oldCut := old.cut)
      hLone hQone (by norm_num)
  have hlimsup := wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
    p hchi hchi_lt hcritical hceiling u₀ hu₀
  obtain ⟨Tupper, hupperEventually⟩ := eventually_atTop.1
    (hlimsup (Q - MChi p) (sub_pos.mpr hMChiQ))
  let t₀ : ℝ := max (max (max old.start Tbuf) Tupper) 1
  have ht₀ : 0 < t₀ := by
    dsimp [t₀]
    exact zero_lt_one.trans_le (le_max_right _ _)
  have holdStart : old.start ≤ t₀ := by
    dsimp [t₀]
    exact ((le_max_left old.start Tbuf).trans
      (le_max_left (max old.start Tbuf) Tupper)).trans
        (le_max_left (max (max old.start Tbuf) Tupper) 1)
  have hTbuf : Tbuf ≤ t₀ := by
    dsimp [t₀]
    exact ((le_max_right old.start Tbuf).trans
      (le_max_left (max old.start Tbuf) Tupper)).trans
        (le_max_left (max (max old.start Tbuf) Tupper) 1)
  have hTupper : Tupper ≤ t₀ := by
    dsimp [t₀]
    exact (le_max_right (max old.start Tbuf) Tupper).trans
      (le_max_left (max (max old.start Tbuf) Tupper) 1)
  let G : ℝ := max (max 1 ‖u₀‖) (MChi p)
  have hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G := by
    intro t ht x
    simpa only [G] using
      wholeLineCauchyGlobal_le_max_max_one_norm_MChi_of_chi_pos
        p hchi hchi_lt hcritical hceiling u₀ hu₀ ht x
  let globalData := wholeLineCauchyGlobal_positiveCoMovingRestartData
    p hceiling u₀ hu₀ hleft c (G := G) ht₀
      (fun {_t} ht x => hglobal ht x)
  have hfutureUpper : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ z,
      globalData.q s z ≤ Q := by
    intro s hs z
    rw [globalData.eq_global hs z]
    have htime : Tupper ≤ t₀ + s :=
      hTupper.trans (le_add_of_nonneg_right hs)
    have hup := hupperEventually (t₀ + s) htime
      (z + c * (t₀ + s))
    dsimp only [coMovingPath]
    linarith
  let data : WholeLineChiPosCoMovingRestartData p u₀ c t₀ Q :=
    { q := globalData.q
      eq_global := globalData.eq_global
      continuous := globalData.continuous
      mem_Icc := by
        intro s hs z
        exact ⟨(globalData.mem_Icc hs z).1, hfutureUpper hs z⟩
      positive := globalData.positive
      time_operator := globalData.time_operator
      slice_contDiff_two := globalData.slice_contDiff_two }
  let C : ℝ := min (old.ell / 2) (ell₀ / 2)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_min (half_pos old.ell_pos) (half_pos hell₀pos)
  have hCold : C ≤ old.ell := by
    have hhalf : C ≤ old.ell / 2 := by
      dsimp [C]
      exact min_le_left _ _
    linarith
  have hCell₀ : C < ell₀ := by
    have hhalf : C ≤ ell₀ / 2 := by
      dsimp [C]
      exact min_le_right _ _
    linarith
  have hCL : C < L := hCell₀.trans hell₀L'
  let rate : ℝ := chiPosHalfLineFloorRate p Q C L (1 / 2 : ℝ) Q
  let barrier : ℝ → ℝ := fun s => chiZeroKPPFloor C L rate s
  have hrate : 0 < rate := by
    exact chiPosHalfLineFloorRate_pos hC hCL hreserve
  have hbarrierAll : ∀ s, 0 ≤ s → ∀ z ∈ Set.Iic cut,
      barrier s ≤ data.q s z := by
    apply data.ge_of_weighted_buffered_floor
        (x₀ := cut) (R := 0) (ell := 0) (M := Q)
        (b := barrier) hchi (by norm_num) (by norm_num)
        (zero_le_one.trans hQone.le)
        (zero_le_one.trans hQone.le) (le_rfl)
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiZeroKPPFloor_hasDerivAt C L rate s).continuousAt
    · intro s hs z _hz
      exact data.mem_Icc hs z
    · intro s hs
      have hlo : C ≤ barrier s :=
        chiZeroKPPFloor_ge_start hCL.le hrate.le hs
      have hhi : barrier s ≤ L := chiZeroKPPFloor_le_target hCL.le
      exact ⟨hC.le.trans hlo,
        hhi.trans (hLone.le.trans hQone.le)⟩
    · intro z hz
      rw [show barrier 0 = C by simp [barrier]]
      rw [data.eq_global (s := 0) le_rfl z]
      simpa only [add_zero] using hCold.trans
        (old.bounds t₀ holdStart z (hz.trans hcutOld)).1
    · intro s hs z hz
      have hbarrier : barrier s ≤ L :=
        chiZeroKPPFloor_le_target hCL.le
      rw [data.eq_global hs z]
      exact hbarrier.trans
        (hbuffer (t₀ + s)
          (hTbuf.trans (le_add_of_nonneg_right hs)) z hz).1.le
    · intro s _hs
      exact (chiZeroKPPFloor_hasDerivAt C L rate s).differentiableAt.hasDerivAt
    · intro s hs
      have hb := chiZeroKPPFloor_tail_weighted_subsolution
        (p := p) (M := Q) (C := C) (L := L) (tau := (1 / 2 : ℝ))
        (G := Q) (t := s) hcritical hchi.le hchi_lt hC hCL hLone.le
        hQone.le (by norm_num) (zero_le_one.trans hQone.le) hreserve hs.le
      dsimp [barrier, rate] at hb ⊢
      unfold reactionFun at hb
      norm_num at hb ⊢
      linarith
  have hbarrierTend : Tendsto barrier atTop (nhds L) := by
    dsimp [barrier]
    exact chiZeroKPPFloor_tendsto_target hrate
  have hbarrierNhd : Set.Ioi ell₀ ∈ nhds L :=
    Ioi_mem_nhds hell₀L'
  obtain ⟨Sfloor, hSfloor⟩ := eventually_atTop.1
    (hbarrierTend.eventually hbarrierNhd)
  let sfloor : ℝ := max Sfloor 0
  have hsfloor : 0 ≤ sfloor := le_max_right Sfloor 0
  have hS_sfloor : Sfloor ≤ sfloor := le_max_left Sfloor 0
  let start : ℝ := t₀ + sfloor
  have hfloorMarginL : 0 < chiPosFloorGap p Q L := by
    have htail :
        0 ≤ p.χ * L ^ (p.m - 1) * (1 / 2 : ℝ) * Q ^ p.γ := by
      positivity
    linarith
  have hfloorMargin : 0 < chiPosFloorGap p Q ell₀ := by
    exact hfloorMarginL.trans
      (chiPosFloorGap_strictAntiOn_Ioi hcritical hchi.le hchi_lt
        (zero_le_one.trans hQone.le) hell₀pos hL hell₀L')
  have hceilingMargin : 0 < chiPosCeilingGap p ell₀ Q := by
    simpa only [chiPosCeilingGap, mul_assoc] using
      chiPos_rectangle_ceiling_margin_pos_of_MChi_lt
        p hchi hchi_lt hcritical hMChiQ hell₀pos.le
  refine ⟨
    { ell := ell₀
      M := Q
      start := start
      cut := cut
      ell_pos := hell₀pos
      ell_lt_one := hell₀one
      one_lt_M := hQone
      floor_margin := hfloorMargin
      ceiling_margin := hceilingMargin
      bounds := ?_ }, ?_, ?_⟩
  · intro t ht z hz
    let s : ℝ := t - t₀
    have hs : 0 ≤ s := by
      dsimp [s, start] at ht ⊢
      linarith
    have hsettled : Sfloor ≤ s := by
      dsimp [s, start] at ht ⊢
      linarith
    have hcomp := hbarrierAll s hs z (Set.mem_Iic.mpr hz)
    have hbar := (hSfloor s hsettled).le
    rw [data.eq_global hs z] at hcomp
    have htime : t₀ + s = t := by
      dsimp [s]
      ring
    rw [htime] at hcomp
    have hlo : ell₀ ≤ coMovingPath c
        (wholeLineCauchyGlobalU p u₀) t z := hbar.trans hcomp
    have hTuppert : Tupper ≤ t := by
      have ht₀t : t₀ ≤ t := by
        dsimp [start] at ht
        linarith
      exact hTupper.trans ht₀t
    have hupRaw := hupperEventually t hTuppert (z + c * t)
    have hup : coMovingPath c
        (wholeLineCauchyGlobalU p u₀) t z ≤ Q := by
      dsimp only [coMovingPath]
      dsimp [Q]
      linarith
    exact ⟨hlo, hup⟩
  · dsimp [ell₀, Q]
    exact le_rfl
  · rfl

section AxiomAudit

#print axioms exists_initial_chiPosHalfLineRectangle_quantified

end AxiomAudit

end ShenWork.Paper1
