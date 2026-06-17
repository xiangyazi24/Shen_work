import ShenWork.Paper1.WaveG1Bridge
import ShenWork.Paper1.WaveLemma42Paper

namespace ShenWork.Paper1

open Filter Topology

noncomputable section

/-- Concrete projected order-cube approximation data for one lower-pinned
wave-map.  This is the finite-dimensional residual left by the `proj/lift`
construction; it is not the old provider over all self-maps. -/
abbrev LowerPinnedOrderCubeApproxData
    (κ M : ℝ) (φ : ℝ → ℝ) (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Type :=
  ProjectedCubeApproxData (InLowerPinnedMonotoneTrap κ M φ) Tmap

abbrev LowerPinnedWaveCubeApproxData
    (κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Type :=
  LowerPinnedOrderCubeApproxData κ M φ
    (fun u => rotheLimit (rotheSeq u))

/-- Lower-pinned Rothe fixed point with `hprinciple` replaced by finite cube
approximation data. -/
theorem paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData
    (p : CMParams) (c lam M κ : ℝ) (φ : ℝ → ℝ)
    (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        PaperRotheOrbitData p c lam M κ rotheSeq u)
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq)
    (Happrox : LowerPinnedWaveCubeApproxData κ M φ rotheSeq) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      rotheLimit (rotheSeq U) = U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u => rotheLimit (rotheSeq u)
  have hbareInv :
      ∀ u, InMonotoneWaveTrapSet κ M u → InMonotoneWaveTrapSet κ M (Tmap u) :=
    paperTmap_maps_trap p c lam M κ hM rotheSeq hŪbdd hdata
  have hlowerT :
      ∀ u, InLowerPinnedMonotoneTrap κ M φ u → ∀ x, φ x ≤ Tmap u x :=
    Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower
  have hcont : LocalUniformContinuousOn (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
    intro seq u hseq hu hconv
    exact hdep seq u (fun n => (hseq n).bare) hu.bare hconv
  have hcompactBare :
      LocalUniformSequentiallyCompactRange (InMonotoneWaveTrapSet κ M) Tmap :=
    paperTmap_compactRange p c lam M κ hM rotheSeq hHelly hdata
  have hcompact :
      LocalUniformSequentiallyCompactRange
        (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
    intro seq hseq
    obtain ⟨subseq, hsubseq, U, hUbare, hconv⟩ :=
      hcompactBare seq (fun n => (hseq n).bare)
    refine ⟨subseq, hsubseq, U, ⟨hUbare, ?_⟩, hconv⟩
    intro x
    have hlimit :
        Tendsto (fun n => Tmap (seq (subseq n)) x) atTop (𝓝 (U x)) :=
      hconv.tendsto_at x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
      (Filter.Eventually.of_forall fun n =>
        hlowerT (seq (subseq n)) (hseq (subseq n)) x)
  obtain ⟨U, hU, hfix⟩ :=
    localUniformFixedPoint_of_cubeApproxData hcont hcompact
      (ProjectedCubeApproxData.toLocalUniformCubeApproxData Happrox)
  exact ⟨U, hU, by simpa [Tmap] using hfix⟩

theorem b1_chiNeg_existence_paper_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll))
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll u
                (k + 1)))
    (Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hstep :
      RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) zseq := by
    have haux' : ∀ u,
        InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
          ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
            rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hcond.hκ0.le hM0 k x) →
            ∃ C_chem La Lb,
              PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
                (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
                  hcond.hκ0.le hM0 (k + 1)) := by
      simpa [zseq, rotheSeqOfPaperFromCond, hM0] using hauxData
    simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
      rotheSeqOfPaper_lowerBarrierRaw_stepInvariant hcond hD hD_ge_one
        hprodAll hcond.hκ0.le hM0 haux'
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
          rotheSeqOfPaper_lowerPinned_base (hprodAll u) hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u _hu
    simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
      paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := u) hprodAll hcond.hκ0.le hM0
        hΛ0 hΛM hbarLip
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq hŪbdd
      (helly_pointwise_selection M) hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

theorem b1_chiNeg_existence_paper'_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM (fun u => (hprodAll u).producer)
    hbarLip (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    hdep (hauxData_of_conditions hcond hD hD_ge_one hprodAll)
    Happrox hstationary (hsmp_of_odeRealization hrealize) hflat

theorem b1_chiNeg_existence_paper_clean_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper'_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM hprodAll hbarLip
    (by
      simpa [rotheSeqOfPaperFromCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hprodAll u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hstep htail)
    Happrox hstationary hrealize hflat

theorem b1_chiPos_existence_paper_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond hprodAll))
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            hprodAll u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
                hprodAll u (k + 1)))
    (Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond hprodAll))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            hprodAll U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond hprodAll
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hstep :
      RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) zseq := by
    have haux' : ∀ u,
        InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
          ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
            rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hcond.hκ0.le hM0 k x) →
            ∃ C_chem La Lb,
              PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
                (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
                  hcond.hκ0.le hM0 (k + 1)) := by
      simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using hauxData
    simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
      rotheSeqOfPaper_lowerBarrierRaw_positive_stepInvariant hcond hD
        hD_ge_one hprodAll hcond.hκ0.le hM0 haux'
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
          rotheSeqOfPaper_lowerPinned_base (hprodAll u) hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u _hu
    simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
      paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := u) hprodAll hcond.hκ0.le hM0
        hΛ0 hΛM hbarLip
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq hŪbdd
      (helly_pointwise_selection M) hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_positive_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

theorem b1_chiPos_existence_paper'_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM (fun u => (hprodAll u).producer)
    hbarLip (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    hdep (hauxData_of_positive_conditions hcond hD hD_ge_one hprodAll)
    Happrox hstationary (hsmp_of_odeRealization hrealize) hflat

theorem b1_chiPos_existence_paper_clean_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper'_of_cubeApproxData p c lam M κ κtilde D Λ
    hcond hD hD_ge_one hΛ0 hΛM hprodAll hbarLip
    (by
      simpa [rotheSeqOfPaperFromPositiveCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hprodAll u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hstep htail)
    Happrox hstationary hrealize hflat

#print axioms paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper'_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_clean_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_of_cubeApproxData
#print axioms b1_chiPos_existence_paper'_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_clean_of_cubeApproxData

end

end ShenWork.Paper1
