import ShenWork.Paper1.IntervalP1PerStepFixedSource
import ShenWork.Paper1.WaveLemma42G1Discharge
import ShenWork.Paper1.WavePaperRotheCompactness

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Build the Route-A Green core from the explicit source-box parameter layer.

This is the concrete source-box route from `IntervalP1PerStepFixedSource`, kept
as a reusable adapter so the B1 lower-raw floor can expose these smaller
residuals instead of a monolithic `PaperGreenStepInputRouteACore`. -/
def paperRouteAParamGreenCore
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap)
    (hrest : PaperGreenStepInputRouteASuperRestProvider p c lam M κ Λ u) :
    PaperGreenStepInputRouteACore p c lam M κ Λ u :=
  paperGreenStepInputRouteACore_of_trap_fixedSource
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ) (u := u)
    params.hu params.hlam params.basePaperSuper
    (paperStepFixedSourceExistsForSuperTrap_of_params params wit)
    hrest

/-- Route-A lower-raw producer core whose Green core is not carried directly:
it is assembled from the explicit per-step source-box parameter package. -/
structure PaperLowerRawStepProducerRouteAParamCore
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (u : ℝ → ℝ) : Type where
  B : ℝ
  sigma : ℝ
  aL : ℝ
  C_u : ℝ
  L_u : ℝ
  C_R : ℝ
  m_sigma : ℝ
  params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u
  witness : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap
  rest : PaperGreenStepInputRouteASuperRestProvider p c lam M κ Λ u
  lowerRawAux :
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
        rotheSeqOfPaper p c lam M κ Λ u
          (paperRotheStepProducer_of_routeA_greenCore
            (paperRouteAParamGreenCore params witness rest)) hκ hM k x) →
        ∃ C_chem La Lb,
          PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
            (rotheSeqOfPaper p c lam M κ Λ u
              (paperRotheStepProducer_of_routeA_greenCore
                (paperRouteAParamGreenCore params witness rest))
              hκ hM (k + 1))

/-- The Route-A Green core produced by the parameterized lower-raw core. -/
def paperLowerRawRouteAParamGreenCore
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    PaperGreenStepInputRouteACore p c lam M κ Λ u :=
  paperRouteAParamGreenCore h.params h.witness h.rest

/-- The paper Rothe producer induced by a parameterized Route-A lower-raw core. -/
def paperLowerRawRouteAParamProducer
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    PaperRotheStepProducer p c lam M κ Λ u :=
  paperRotheStepProducer_of_routeA_greenCore
    (paperLowerRawRouteAParamGreenCore h)

/-- Forget the explicit source-box parameter layer to the existing Route-A
lower-raw producer core. -/
def paperLowerRawStepProducerRouteACore_of_paramCore
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    PaperLowerRawStepProducerRouteACore p c lam M κ κtilde D Λ hκ hM u where
  green := paperLowerRawRouteAParamGreenCore h
  lowerRawAux := h.lowerRawAux

/-- Route-A paper Rothe parabolic floor whose per-step Green core is assembled
from explicit source-box parameter data, with the automatic `barLip` field
removed. -/
structure PaperLowerRawParabolicFloorRouteAParamCoreNoBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u
  greenLimitIdentificationFromDrift :
    PaperGreenRotheLimitIdentificationFromDriftOnTrap p c lam M κ Λ
      (fun u hu => paperLowerRawRouteAParamProducer (producer u hu)) hκ hM

/-- Forget the explicit source-box parameter layer at the per-profile producer
level.  The sequence-local tail is kept separately because it intentionally
does not imply the older globally quantified parabolic-floor tail. -/
def paperLowerRawStepProducerTrap_of_paramCoreNoBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u :=
  fun u hu => paperLowerRawStepProducer_of_routeA_core
    (paperLowerRawStepProducerRouteACore_of_paramCore (h.producer u hu))

/-- The total map used by Schauder, with the producer invoked only on its trap
domain and the upper barrier used outside it. -/
def paperLowerRawParamRotheSeqFromTrap
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  rotheSeqOfPaperFromTrap p c lam M κ Λ
    (fun u hu => paperLowerRawRouteAParamProducer (h.producer u hu)) hκ hM

/-- B1 χ≤0 Route-A wrapper after replacing the monolithic Route-A per-step
producer residual by the explicit source-box parameter layer. -/
theorem b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorRouteAParamCoreNoBar
        p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (paperLowerRawParamRotheSeqFromTrap hpar))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  let hprodTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheStepProducer p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamProducer (hpar.producer u hu)
  let zseq := paperLowerRawParamRotheSeqFromTrap hpar
  have hgraph :=
    (hpar.greenLimitIdentificationFromDrift.toLimitIdentification.compactClosedGraph
      hΛ0 hΛM hcond.upperBarrier_barLip).stepDependence_and_tailAlong
      hΛ0 hΛM hcond.upperBarrier_barLip
  have hdep : RotheContinuousDependence p c lam
      (InMonotoneWaveTrapSet κ M) zseq := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap] using
      paperRotheContinuousDependence_fromTrap_of_tailAlong
        p c lam M κ Λ hprodTrap hcond.hκ0.le hM0 hgraph.1 hgraph.2
  have hstep : RotheStepLowerInvariant κ M
      (lowerBarrierRaw κ κtilde D) zseq := by
    refine rotheStepLowerInvariant_lowerBarrierRaw_of_paperStepData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (κtilde := κtilde) (D := D) (Λ := Λ)
      hcond hD hD_ge_one ?_
    intro u hu k hprev
    let hp := hpar.producer u hu.bare
    have hzu : zseq u = rotheSeqOfPaper p c lam M κ Λ u
        (paperLowerRawRouteAParamProducer hp) hcond.hκ0.le hM0 := by
      simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap, hp] using
        rotheSeqOfPaperFromTrap_eq hprodTrap hcond.hκ0.le hM0 hu.bare
    rw [hzu] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := hp.lowerRawAux hu k hprev
    have hfacts := rotheSeqOfPaper_stepFacts
      (paperLowerRawRouteAParamProducer hp) hcond.hκ0.le hM0 k
    exact ⟨C_chem, La, Lb,
      (paperLowerRawRouteAParamProducer hp).hlam, hfacts.step_op, haux⟩
  have hlower : RotheOrbitLowerBound κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        have hzu : zseq u = rotheSeqOfPaper p c lam M κ Λ u
            (hprodTrap u hu.bare) hcond.hκ0.le hM0 := by
          simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap] using
            rotheSeqOfPaperFromTrap_eq hprodTrap hcond.hκ0.le hM0 hu.bare
        rw [hzu]
        exact rotheSeqOfPaper_lowerPinned_base (hprodTrap u hu.bare)
          hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap] using
      paperRotheOrbitData_fromTrap (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hprodTrap
        hcond.hκ0.le hM0 hΛ0 hΛM hcond.upperBarrier_barLip hu
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hExpM : Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq
      (upperBarrier_isBddFun hM0) hdep hdata hlower
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq
      (upperBarrier_isBddFun hM0) (helly_pointwise_selection M)
      hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hconv.stationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x := hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hconv.flat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (nhds 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

/-- B1 χ≥0 Route-A wrapper after replacing the monolithic Route-A per-step
producer residual by the explicit source-box parameter layer. -/
theorem b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorRouteAParamCoreNoBar
        p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (paperLowerRawParamRotheSeqFromTrap hpar))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  let hprodTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheStepProducer p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamProducer (hpar.producer u hu)
  let zseq := paperLowerRawParamRotheSeqFromTrap hpar
  have hgraph :=
    (hpar.greenLimitIdentificationFromDrift.toLimitIdentification.compactClosedGraph
      hΛ0 hΛM hcond.upperBarrier_barLip).stepDependence_and_tailAlong
      hΛ0 hΛM hcond.upperBarrier_barLip
  have hdep : RotheContinuousDependence p c lam
      (InMonotoneWaveTrapSet κ M) zseq := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap] using
      paperRotheContinuousDependence_fromTrap_of_tailAlong
        p c lam M κ Λ hprodTrap hcond.hκ0.le hM0 hgraph.1 hgraph.2
  have hstep : RotheStepLowerInvariant κ M
      (lowerBarrierRaw κ κtilde D) zseq := by
    refine rotheStepLowerInvariant_lowerBarrierRaw_of_positivePaperStepData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (κtilde := κtilde) (D := D) (Λ := Λ)
      hcond hD hD_ge_one ?_
    intro u hu k hprev
    let hp := hpar.producer u hu.bare
    have hzu : zseq u = rotheSeqOfPaper p c lam M κ Λ u
        (paperLowerRawRouteAParamProducer hp) hcond.hκ0.le hM0 := by
      simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap, hp] using
        rotheSeqOfPaperFromTrap_eq hprodTrap hcond.hκ0.le hM0 hu.bare
    rw [hzu] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := hp.lowerRawAux hu k hprev
    have hfacts := rotheSeqOfPaper_stepFacts
      (paperLowerRawRouteAParamProducer hp) hcond.hκ0.le hM0 k
    exact ⟨C_chem, La, Lb,
      (paperLowerRawRouteAParamProducer hp).hlam, hfacts.step_op, haux⟩
  have hlower : RotheOrbitLowerBound κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        have hzu : zseq u = rotheSeqOfPaper p c lam M κ Λ u
            (hprodTrap u hu.bare) hcond.hκ0.le hM0 := by
          simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap] using
            rotheSeqOfPaperFromTrap_eq hprodTrap hcond.hκ0.le hM0 hu.bare
        rw [hzu]
        exact rotheSeqOfPaper_lowerPinned_base (hprodTrap u hu.bare)
          hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hprodTrap] using
      paperRotheOrbitData_fromTrap (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hprodTrap
        hcond.hκ0.le hM0 hΛ0 hΛM hcond.upperBarrier_barLip hu
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hExpM : Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have Happrox : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq
      (upperBarrier_isBddFun hM0) hdep hdata hlower
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint_of_cubeApproxData p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq
      (upperBarrier_isBddFun hM0) (helly_pointwise_selection M)
      hdep hdata hlower Happrox
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hconv.stationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_positive_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x := hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hconv.flat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (nhds 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

section AxiomAudit

#print axioms paperRouteAParamGreenCore
#print axioms paperLowerRawStepProducerRouteACore_of_paramCore
#print axioms paperLowerRawStepProducerTrap_of_paramCoreNoBar
#print axioms paperLowerRawParamRotheSeqFromTrap
#print axioms b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData

end AxiomAudit

end ShenWork.Paper1
