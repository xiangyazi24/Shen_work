import ShenWork.Paper1.WholeLineChiPosHalfLineSuccessor
import ShenWork.Paper1.WholeLineWeightedRegularityPlateauSeedNatural

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# A direct half-line seed when `1 < m`

For a genuinely degenerate mobility, a sufficiently small constant is a
strict floor subsolution even after the missing-kernel tail is included.  We
start that floor at a small positive time, keep it through a fixed compact
boundary point using positivity and weighted compact convergence, and combine
it with the eventual `MChi` upper bound.  This avoids the lower-plateau
construction, and in particular does not use `χ < 1 / 2`.
-/

/-- If `1 < m`, a sufficiently small floor has positive reaction reserve even
after a fixed half-kernel defect is charged at the global ceiling `G`. -/
theorem exists_small_chiPos_floor_with_halfKernel_reserve
    (p : CMParams) (hm : 1 < p.m) (G : ℝ) :
    ∃ ell : ℝ, 0 < ell ∧ ell < 1 ∧
      0 < chiPosFloorGap p G ell -
        p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * G ^ p.γ := by
  let phi : ℝ → ℝ := fun ell =>
    chiPosFloorGap p G ell -
      p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * G ^ p.γ
  have halpha_pos : 0 < p.α := zero_lt_one.trans_le p.hα
  have hm_sub_pos : 0 < p.m - 1 := sub_pos.mpr hm
  have hgamma_pos : 0 < p.γ := zero_lt_one.trans_le p.hγ
  have hphi_zero : 0 < phi 0 := by
    simp [phi, chiPosFloorGap, Real.zero_rpow halpha_pos.ne',
      Real.zero_rpow hm_sub_pos.ne', Real.zero_rpow hgamma_pos.ne']
  have hcont : ContinuousAt phi 0 := by
    dsimp [phi]
    exact (chiPosFloorGap_continuous p G).continuousAt.sub
      ((((continuousAt_const.mul
          (Real.continuous_rpow_const hm_sub_pos.le).continuousAt).mul
            continuousAt_const).mul continuousAt_const))
  have hpre : phi ⁻¹' Ioi 0 ∈ 𝓝 0 :=
    hcont (Ioi_mem_nhds hphi_zero)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨delta, hdelta, hball⟩
  let ell : ℝ := min (delta / 2) (1 / 2)
  have hell_pos : 0 < ell := by
    dsimp [ell]
    exact lt_min (half_pos hdelta) (by norm_num)
  have hell_delta : ell < delta :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hell_one : ell < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hell_mem : ell ∈ Metric.ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hell_pos]
    exact hell_delta
  exact ⟨ell, hell_pos, hell_one, hball hell_mem⟩

/-- At every nonnegative physical time, the canonical co-moving slice retains
the one-sided positive floor of the datum. -/
theorem wholeLineCauchyGlobal_coMoving_strictlyPositiveAtLeft
    (p : CMParams) (hceiling : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    StrictlyPositiveAtLeft
      (coMovingPath c (wholeLineCauchyGlobalU p u₀) t) := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hsegment : StrictlyPositiveAtLeft
      (wholeLineCauchyGlobalSegment p u₀ n z).1 :=
    (wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
      p hceiling u₀ hu₀ hleft n).2.2 z
  have heq : ∀ x,
      wholeLineCauchyGlobalU p u₀ t x =
        (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    intro x
    have h := congrArg (fun w : WholeLineBUC => w.1 x)
      (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
    simpa [wholeLineCauchyGlobalU, n, q, z] using h
  rcases hsegment with ⟨d, hd, hdevent⟩
  refine ⟨d, hd, ?_⟩
  have hshift :=
    (tendsto_atBot_add_const_right atBot (c * t) tendsto_id).eventually
      hdevent
  filter_upwards [hshift] with x hx
  simpa [coMovingPath, heq (x + c * t)] using hx

/-- The canonical positive-sensitivity orbit admits an initial strict
half-line rectangle throughout `0 < χ < 1` when `1 < m`. -/
theorem exists_initial_chiPosHalfLineRectangle_m_gt_one
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
    Nonempty
      (ChiPosHalfLineRectangle p c (wholeLineCauchyGlobalU p u₀)) := by
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
  let canonicalG : ℝ := max (max 1 ‖u₀‖) (MChi p)
  let G : ℝ := max canonicalG Q
  have hMChi_pos : 0 < MChi p := MChi_pos_of_chi_lt_one p hchi_lt
  have hMChiQ : MChi p < Q := by dsimp [Q]; linarith
  have hQone : 1 < Q := by dsimp [Q]; linarith
  have hQG : Q ≤ G := by dsimp [G]; exact le_max_right _ _
  have hG : 0 ≤ G := (zero_le_one.trans hQone.le).trans hQG
  have hglobal : ∀ {t : ℝ}, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G := by
    intro t ht x
    exact (wholeLineCauchyGlobal_le_max_max_one_norm_MChi_of_chi_pos
      p hchi hchi_lt hcritical hceiling u₀ hu₀ ht x).trans
        (by dsimp [G, canonicalG]; exact le_max_left _ _)
  obtain ⟨ellSeed, hellSeed, hellSeed_one, hseedReserve⟩ :=
    exists_small_chiPos_floor_with_halfKernel_reserve p hm G
  obtain ⟨t₀, ht₀, hslice⟩ :=
    exists_positive_time_strictlyPositiveAtLeft_of_uniformInitialTrace
      (c := c) hleft (wholeLineCauchyGlobal_hasUniformInitialTrace p u₀)
  rcases hslice with ⟨d₀, hd₀, hd₀event⟩
  obtain ⟨B, hB⟩ := eventually_atBot.1 hd₀event
  obtain ⟨cut, Tbuf, hcutB, _hcutB', hbuffer⟩ :=
    exists_eventual_chiPos_farLeft_buffer
      heta hweighted hmod hTW.lim_neg_inf.1
      (L := ellSeed) (A := Q) (R := 0) (oldCut := B)
      hellSeed_one hQone (by norm_num)
  let data := wholeLineCauchyGlobal_positiveCoMovingRestartData
    p hceiling u₀ hu₀ hleft c (G := G) ht₀
      (fun {_t} ht x => hglobal ht x)
  let S : ℝ := max (Tbuf - t₀) 0
  have hS : 0 ≤ S := by dsimp [S]; exact le_max_right _ _
  have htimeContinuous : Continuous (fun s : ℝ => data.q s cut) := by
    have hmap : Continuous (fun s : ℝ => (s, cut)) := by fun_prop
    exact data.continuous.comp hmap
  have htimePositive : ∀ s ∈ Set.Icc (0 : ℝ) S, 0 < data.q s cut := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | hspos
    · rw [data.eq_global (s := 0) le_rfl cut]
      simpa using hd₀.trans_le (hB cut hcutB)
    · exact data.positive hspos
  obtain ⟨dcompact, hdcompact, hcompact⟩ :=
    isCompact_Icc.exists_forall_le' htimeContinuous.continuousOn
      htimePositive
  let ell : ℝ := min (min (ellSeed / 2) (d₀ / 2)) (dcompact / 2)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (lt_min (half_pos hellSeed) (half_pos hd₀))
      (half_pos hdcompact)
  have hell_seed : ell < ellSeed := by
    have hle : ell ≤ ellSeed / 2 := by
      dsimp [ell]
      exact (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hell_d₀ : ell ≤ d₀ := by
    have hle : ell ≤ d₀ / 2 := by
      dsimp [ell]
      exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hell_compact : ell ≤ dcompact := by
    have hle : ell ≤ dcompact / 2 := by
      dsimp [ell]
      exact min_le_right _ _
    linarith
  have hell_one : ell < 1 := hell_seed.trans hellSeed_one
  have hgapMono : chiPosFloorGap p G ellSeed < chiPosFloorGap p G ell :=
    chiPosFloorGap_strictAntiOn_Ioi hcritical hchi.le hchi_lt hG
      hell hellSeed hell_seed
  have htailMono :
      p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * G ^ p.γ ≤
        p.χ * ellSeed ^ (p.m - 1) * (1 / 2 : ℝ) * G ^ p.γ := by
    have hpow : ell ^ (p.m - 1) ≤ ellSeed ^ (p.m - 1) :=
      Real.rpow_le_rpow hell.le hell_seed.le (sub_nonneg.mpr p.hm)
    have hcoeff : 0 ≤ p.χ * (1 / 2 : ℝ) * G ^ p.γ := by positivity
    nlinarith
  have hreserve :
      0 < chiPosFloorGap p G ell -
        p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * G ^ p.γ := by
    linarith
  have hfloorMarginG : 0 < chiPosFloorGap p G ell := by
    have htail_nonneg :
        0 ≤ p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * G ^ p.γ := by
      positivity
    linarith
  have hfloorMargin : 0 < chiPosFloorGap p Q ell := by
    exact hfloorMarginG.trans_le
      (chiPosFloorGap_anti_resolver_ceiling hchi.le hell.le
        (zero_le_one.trans hQone.le) hQG)
  have hceilingMargin : 0 < chiPosCeilingGap p ell Q := by
    simpa only [chiPosCeilingGap, mul_assoc] using
      chiPos_rectangle_ceiling_margin_pos_of_MChi_lt
        p hchi hchi_lt hcritical hMChiQ hell.le
  have hbufferAll : ∀ s, 0 ≤ s →
      ∀ x ∈ Set.Icc cut (cut + 0), ell ≤ data.q s x := by
    intro s hs x hx
    have hxcut : x = cut := by simp only [add_zero] at hx; exact le_antisymm hx.2 hx.1
    subst x
    by_cases hsS : s ≤ S
    · exact hell_compact.trans (hcompact s ⟨hs, hsS⟩)
    · rw [data.eq_global hs cut]
      have hTbuf : Tbuf ≤ t₀ + s := by
        have hTS : Tbuf - t₀ ≤ S := by
          dsimp [S]
          exact le_max_left _ _
        linarith
      exact hell_seed.le.trans
        (hbuffer (t₀ + s) hTbuf cut (by simp)).1.le
  have hfloorAll : ∀ s, 0 ≤ s → ∀ x ∈ Set.Iic cut,
      ell ≤ data.q s x := by
    apply data.ge_of_weighted_buffered_floor
        (x₀ := cut) (R := 0) (ell := 0) (M := G)
        (b := fun _ => ell) hchi (by norm_num) (by norm_num) hG
        hG (le_rfl)
    · exact continuous_const
    · intro s hs x _hx
      exact data.mem_Icc hs x
    · intro s _hs
      exact ⟨hell.le, (hell_one.le.trans hQone.le).trans hQG⟩
    · intro x hx
      rw [data.eq_global (s := 0) le_rfl x]
      simpa using hell_d₀.trans (hB x (hx.trans hcutB))
    · exact hbufferAll
    · intro s _hs
      simpa using (hasDerivAt_const (x := s) (c := ell))
    · intro s _hs
      have hpow : ell ^ p.m = ell * ell ^ (p.m - 1) := by
        calc
          ell ^ p.m = ell ^ (1 + (p.m - 1)) := by congr 1 <;> ring
          _ = ell ^ (1 : ℝ) * ell ^ (p.m - 1) :=
            Real.rpow_add hell 1 (p.m - 1)
          _ = ell * ell ^ (p.m - 1) := by rw [Real.rpow_one]
      have hfactor :
          ell * (1 - ell ^ p.α) -
              p.χ * ell ^ p.m * (G ^ p.γ - ell ^ p.γ) -
              p.χ * ell ^ p.m * (Real.exp (-(0 : ℝ)) / 2) * G ^ p.γ =
            ell * (chiPosFloorGap p G ell -
              p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * G ^ p.γ) := by
        rw [hpow, neg_zero, Real.exp_zero]
        unfold chiPosFloorGap
        ring
      rw [deriv_const, hfactor]
      exact mul_nonneg hell.le hreserve.le
  have hlimsup := wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
    p hchi hchi_lt hcritical hceiling u₀ hu₀
  obtain ⟨Tupper, hTupper⟩ := eventually_atTop.1
    (hlimsup (Q - MChi p) (sub_pos.mpr hMChiQ))
  let start : ℝ := max t₀ Tupper
  refine ⟨
    { ell := ell
      M := Q
      start := start
      cut := cut
      ell_pos := hell
      ell_lt_one := hell_one
      one_lt_M := hQone
      floor_margin := hfloorMargin
      ceiling_margin := hceilingMargin
      bounds := ?_ }⟩
  intro t ht z hz
  have ht₀t : t₀ ≤ t := (le_max_left _ _).trans ht
  let s : ℝ := t - t₀
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hloRaw := hfloorAll s hs z (Set.mem_Iic.mpr hz)
  rw [data.eq_global hs z] at hloRaw
  have htime : t₀ + s = t := by dsimp [s]; ring
  rw [htime] at hloRaw
  have hTuppert : Tupper ≤ t := (le_max_right _ _).trans ht
  have hupRaw := hTupper t hTuppert (z + c * t)
  have hup : coMovingPath c (wholeLineCauchyGlobalU p u₀) t z ≤ Q := by
    dsimp only [coMovingPath]
    linarith
  exact ⟨hloRaw, hup⟩

section AxiomAudit

#print axioms exists_small_chiPos_floor_with_halfKernel_reserve
#print axioms wholeLineCauchyGlobal_coMoving_strictlyPositiveAtLeft
#print axioms exists_initial_chiPosHalfLineRectangle_m_gt_one

end AxiomAudit

end ShenWork.Paper1
