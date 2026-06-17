import ShenWork.Paper1.WaveG1Bridge
import ShenWork.Paper1.WaveLemma42Paper

namespace ShenWork.Paper1

open Filter Topology

noncomputable section

/-- Finite cube approximation provider for a lower-pinned wave trap. -/
abbrev LowerPinnedCubeApproxProvider
    (κ M : ℝ) (φ : ℝ → ℝ) : Type :=
  ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
    (∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      InLowerPinnedMonotoneTrap κ M φ (Tmap u)) →
    LocalUniformContinuousOn (InLowerPinnedMonotoneTrap κ M φ) Tmap →
    LocalUniformSequentiallyCompactRange
      (InLowerPinnedMonotoneTrap κ M φ) Tmap →
      LocalUniformCubeApproxData (InLowerPinnedMonotoneTrap κ M φ) Tmap

/-- Brouwer cube approximation discharges the lower-pinned G1 principle once the
finite profile order-cube approximation provider is supplied. -/
theorem lowerPinned_schauderPrinciple_of_cubeApproxData
    {κ M : ℝ} {φ : ℝ → ℝ}
    (Hcube : LowerPinnedCubeApproxProvider κ M φ) :
    LocalUniformSchauderFixedPointPrinciple
      (InLowerPinnedMonotoneTrap κ M φ) :=
  localUniformSchauderFixedPointPrinciple_of_cubeApproxData
    (trap := InLowerPinnedMonotoneTrap κ M φ) Hcube

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
    (Hcube : LowerPinnedCubeApproxProvider κ M φ) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      rotheLimit (rotheSeq U) = U :=
  paperLowerPinnedSchauder_fixedPoint p c lam M κ φ hM rotheSeq hŪbdd
    hHelly hdep hdata hlower
    (lowerPinned_schauderPrinciple_of_cubeApproxData Hcube)

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
    (Hcube :
      LowerPinnedCubeApproxProvider κ M (lowerBarrierRaw κ κtilde D))
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
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip hŪbdd hdep hauxData
    (lowerPinned_schauderPrinciple_of_cubeApproxData Hcube)
    hstationary hsmp hflat

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
    (Hcube :
      LowerPinnedCubeApproxProvider κ M (lowerBarrierRaw κ κtilde D))
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
  b1_chiNeg_existence_paper' p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip hdep
    (lowerPinned_schauderPrinciple_of_cubeApproxData Hcube)
    hstationary hrealize hflat

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
    (Hcube :
      LowerPinnedCubeApproxProvider κ M (lowerBarrierRaw κ κtilde D))
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
  b1_chiNeg_existence_paper_clean p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip hstep htail
    (lowerPinned_schauderPrinciple_of_cubeApproxData Hcube)
    hstationary hrealize hflat

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
    (Hcube :
      LowerPinnedCubeApproxProvider κ M (lowerBarrierRaw κ κtilde D))
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
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip hŪbdd hdep hauxData
    (lowerPinned_schauderPrinciple_of_cubeApproxData Hcube)
    hstationary hsmp hflat

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
    (Hcube :
      LowerPinnedCubeApproxProvider κ M (lowerBarrierRaw κ κtilde D))
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
  b1_chiPos_existence_paper' p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip hdep
    (lowerPinned_schauderPrinciple_of_cubeApproxData Hcube)
    hstationary hrealize hflat

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
    (Hcube :
      LowerPinnedCubeApproxProvider κ M (lowerBarrierRaw κ κtilde D))
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
  b1_chiPos_existence_paper_clean p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip hstep htail
    (lowerPinned_schauderPrinciple_of_cubeApproxData Hcube)
    hstationary hrealize hflat

#print axioms lowerPinned_schauderPrinciple_of_cubeApproxData
#print axioms paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper'_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_clean_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_of_cubeApproxData
#print axioms b1_chiPos_existence_paper'_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_clean_of_cubeApproxData

end

end ShenWork.Paper1
