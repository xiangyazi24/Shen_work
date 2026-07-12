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
    ∀ u, PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u
  greenLimitIdentification :
    PaperGreenRotheLimitIdentification p c lam M κ Λ
      (fun u => paperLowerRawRouteAParamProducer (producer u)) hκ hM

/-- Forget the explicit source-box parameter layer at the per-profile producer
level.  The sequence-local tail is kept separately because it intentionally
does not imply the older globally quantified parabolic-floor tail. -/
def paperLowerRawStepProducerAll_of_paramCoreNoBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u :=
  fun u => paperLowerRawStepProducer_of_routeA_core
    (paperLowerRawStepProducerRouteACore_of_paramCore (h.producer u))

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
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u => paperLowerRawRouteAParamProducer (hpar.producer u))))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  let hprodAll := paperLowerRawStepProducerAll_of_paramCoreNoBar hpar
  have hgraph :=
    (hpar.greenLimitIdentification.compactClosedGraph
      hΛ0 hΛM hcond.upperBarrier_barLip).stepDependence_and_tailAlong
      hΛ0 hΛM hcond.upperBarrier_barLip
  b1_chiNeg_existence_paper_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (fun u => (hprodAll u).producer) hcond.upperBarrier_barLip
    (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    (by
      simpa [hprodAll, paperLowerRawStepProducerAll_of_paramCoreNoBar,
        rotheSeqOfPaperFromCond] using
        paperRotheContinuousDependence_of_tailAlongConvergentSeq
          p c lam M κ Λ
          (fun u => paperLowerRawRouteAParamProducer (hpar.producer u))
          hcond.hκ0.le (le_trans zero_le_one hcond.hM) hgraph.1 hgraph.2)
    (hauxData_of_conditions hcond hD hD_ge_one hprodAll)
    (by
      simpa [hprodAll, paperLowerRawStepProducerAll_of_paramCoreNoBar] using
        hconv.stationary)
    hsmp
    (by
      simpa [hprodAll, paperLowerRawStepProducerAll_of_paramCoreNoBar] using
        hconv.flat)

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
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u => paperLowerRawRouteAParamProducer (hpar.producer u))))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  let hprodAll := paperLowerRawStepProducerAll_of_paramCoreNoBar hpar
  have hgraph :=
    (hpar.greenLimitIdentification.compactClosedGraph
      hΛ0 hΛM hcond.upperBarrier_barLip).stepDependence_and_tailAlong
      hΛ0 hΛM hcond.upperBarrier_barLip
  b1_chiPos_existence_paper_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM
    (fun u => (hprodAll u).producer) hcond.upperBarrier_barLip
    (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    (by
      simpa [hprodAll, paperLowerRawStepProducerAll_of_paramCoreNoBar,
        rotheSeqOfPaperFromPositiveCond] using
        paperRotheContinuousDependence_of_tailAlongConvergentSeq
          p c lam M κ Λ
          (fun u => paperLowerRawRouteAParamProducer (hpar.producer u))
          hcond.hκ0.le (le_trans zero_le_one hcond.hM) hgraph.1 hgraph.2)
    (hauxData_of_positive_conditions hcond hD hD_ge_one hprodAll)
    (by
      simpa [hprodAll, paperLowerRawStepProducerAll_of_paramCoreNoBar] using
        hconv.stationary)
    hsmp
    (by
      simpa [hprodAll, paperLowerRawStepProducerAll_of_paramCoreNoBar] using
        hconv.flat)

section AxiomAudit

#print axioms paperRouteAParamGreenCore
#print axioms paperLowerRawStepProducerRouteACore_of_paramCore
#print axioms paperLowerRawStepProducerAll_of_paramCoreNoBar
#print axioms b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData

end AxiomAudit

end ShenWork.Paper1
