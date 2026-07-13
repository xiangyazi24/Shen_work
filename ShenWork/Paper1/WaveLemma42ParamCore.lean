import ShenWork.Paper1.IntervalP1PerStepFixedSource
import ShenWork.Paper1.WaveLemma42G1Discharge
import ShenWork.Paper1.WavePaperAdaptiveSourceCompactness
import ShenWork.Paper1.WavePaperRouteARotheAnalytic
import ShenWork.Paper1.WaveLocalUniformClosedGraph
import ShenWork.Paper1.WaveUniformModulusTrap

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Build the Route-A Green core from the explicit source-box parameter layer.

This is the concrete source-box route from `IntervalP1PerStepFixedSource`, kept
as a reusable adapter so the B1 lower-raw floor can expose these smaller
residuals instead of a monolithic all-supertrap Green core. -/
def paperRouteAParamGreenCore
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap)
    (hrest : PaperGreenStepInputRouteARegularRestProvider
      p c lam M κ Λ u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
  paperGreenStepInputRouteAOrbitCore_of_regularFixedSource
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ) (u := u)
    params.hu params.hlam params.basePaperSuper
    (paperStepFixedSourceExistsForRegularSuperTrap_of_params params wit)
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
  witness : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap
  rest : PaperGreenStepInputRouteARegularRestProvider p c lam M κ Λ u
  lowerRawAux :
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
        rotheSeqOfPaperRouteA p c lam M κ Λ u
          (paperRouteAParamGreenCore params witness rest) hκ hM k x) →
        ∃ C_chem La Lb,
          PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
            (rotheSeqOfPaperRouteA p c lam M κ Λ u
              (paperRouteAParamGreenCore params witness rest)
              hκ hM (k + 1))

/-- The Route-A Green core produced by the parameterized lower-raw core. -/
def paperLowerRawRouteAParamGreenCore
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
  paperRouteAParamGreenCore h.params h.witness h.rest

/-- The orbit-faithful Green producer induced by the parameterized lower-raw
core. -/
def paperLowerRawRouteAParamProducer
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M} {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteAParamCore
      p c lam M κ κtilde D Λ hκ hM u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
  paperLowerRawRouteAParamGreenCore h

/-- The total analytic-preserving Rothe sequence induced by a trap-indexed
parameterized Route-A Green core. -/
def paperLowerRawParamRotheSeq
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (producer : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ
    (fun u hu => paperLowerRawRouteAParamGreenCore (producer u hu)) hκ hM

/-- The exact L10 residual after compactness: every local-uniform cluster of
Rothe limits along converging frozen profiles is the Rothe limit at the target
profile.  Compact range turns this closed-graph statement into full sequential
continuity below. -/
def PaperLowerRawParamRotheLimitClosedGraph
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (producer : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u) : Prop :=
  LocalUniformSequentialClosedGraphOn
    (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
    (fun u => rotheLimit (paperLowerRawParamRotheSeq producer u))

/-- The irreducible L10 identification statement after the off-diagonal Green
closed graph: a lower-pinned stationary cluster for the frozen profile `u` is
the particular upper-start Rothe limit selected at `u`.  The lower pin is
essential: on the bare trap the zero profile is always a self step. -/
def PaperLowerRawParamRotheStationaryIdentification
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (producer : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u) : Prop :=
  ∀ u W,
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) W →
    (∀ x, paperImplicitStepOp p c (1 / lam) u W x = W x) →
      W = rotheLimit (paperLowerRawParamRotheSeq producer u)

/-- Route-A paper Rothe parabolic floor after all mechanical compactness and
finite-cube fields have been removed.  `limitClosedGraph` is the single L10
double-limit identification still carried. -/
structure PaperLowerRawParabolicFloorRouteAParamCoreNoBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperLowerRawStepProducerRouteAParamCore
        p c lam M κ κtilde D Λ hκ hM u
  stationaryIdentification :
    PaperLowerRawParamRotheStationaryIdentification producer

/-- The total map used by Schauder, with the producer invoked only on its trap
domain and the upper barrier used outside it. -/
def paperLowerRawParamRotheSeqFromTrap
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  paperLowerRawParamRotheSeq h.producer

/-- The parameterized Route-A orbit supplies its moving Green-source cluster
from the analytic payload retained at every successor.  No source compactness
or family-uniform Rothe tail remains as a carried hypothesis. -/
theorem paperLowerRawParamGreenSourceCompactness
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (hMpos : 0 < M) (hΛ0 : 0 ≤ Λ) :
    PaperGreenRotheAdaptiveSourceCompactnessOnTrap p c lam M κ Λ
      (paperLowerRawParamRotheSeq h.producer) := by
  let hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (h.producer u hu)
  have hlam : 0 < lam :=
    (hinput (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hκ hM)).hlam
  apply paperGreenRotheAdaptiveSourceCompactness_of_stepAnalytic
    p c lam M κ Λ hMpos hΛ0 hlam (paperLowerRawParamRotheSeq h.producer)
  · intro u hu k
    change PaperStepAnalytic p c lam M κ Λ u
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u k)
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u (k + 1))
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_stepAnalytic (hinput u hu) hκ hM k
  · intro u hu k x
    change 0 ≤ rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_nonneg (hinput u hu) hκ hM (k + 1) x
  · intro u hu k x
    change rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x ≤ M
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_le_M (hinput u hu) hκ hM (k + 1) x

/-- The parameterized Route-A orbit supplies the stronger off-diagonal Green
closed graph needed for continuity of its long-time limit map. -/
theorem paperLowerRawParamOffDiagonalStepClosedGraph
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (hMpos : 0 < M) (hΛ0 : 0 ≤ Λ) :
    PaperGreenRotheAdaptiveOffDiagonalStepClosedGraphOnTrap p c lam M κ
      (paperLowerRawParamRotheSeq h.producer) := by
  let hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (h.producer u hu)
  have hlam : 0 < lam :=
    (hinput (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hκ hM)).hlam
  apply paperGreenRotheAdaptiveOffDiagonalStepClosedGraph_of_stepAnalytic
    p c lam M κ Λ hMpos hΛ0 hlam (paperLowerRawParamRotheSeq h.producer)
  · intro u hu k
    change PaperStepAnalytic p c lam M κ Λ u
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u k)
      (rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM u (k + 1))
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_stepAnalytic (hinput u hu) hκ hM k
  · intro u hu k x
    change 0 ≤ rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_nonneg (hinput u hu) hκ hM (k + 1) x
  · intro u hu k x
    change rotheSeqOfPaperRouteAFromTrap p c lam M κ Λ hinput hκ hM
      u (k + 1) x ≤ M
    rw [rotheSeqOfPaperRouteAFromTrap_eq hinput hκ hM hu]
    exact rotheSeqOfPaperRouteA_le_M (hinput u hu) hκ hM (k + 1) x

/-- Adaptive diagonal plus the off-diagonal Green closed graph reduce the full
map closed graph to the single stationary-cluster identification field. -/
theorem paperLowerRawParamRotheLimitClosedGraph
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (hMpos : 0 < M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperLowerRawParamRotheLimitClosedGraph h.producer := by
  let zseq := paperLowerRawParamRotheSeq h.producer
  let hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (h.producer u hu)
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeq, hinput] using
      paperRouteARotheOrbitData_fromTrap (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hinput
        hκ hM hΛ0 hΛM hbarLip hu
  have hoff : PaperGreenRotheAdaptiveOffDiagonalStepClosedGraphOnTrap
      p c lam M κ zseq := by
    simpa [zseq] using
      paperLowerRawParamOffDiagonalStepClosedGraph h hMpos hΛ0
  intro seq u W hseq hu hW houter hlimits
  let Z : ℕ → ℕ → ℝ → ℝ := fun n => zseq (seq n)
  let L : ℕ → ℝ → ℝ := fun n => rotheLimit (zseq (seq n))
  have horbit : ∀ n, LocallyUniformConverges (Z n) (L n) := by
    intro n
    simpa [Z, L] using (hdata (seq n) (hseq n).bare).locallyUniform hM
  obtain ⟨ks, hks, hold, hnew, _hgap⟩ :=
    exists_adaptiveMovingIndex_commonLimit horbit (by simpa [L] using hlimits)
  obtain ⟨hstep, _hWdiff, _hWderivDiff⟩ := hoff seq u W ks
    (fun n => (hseq n).bare) hu.bare hW.bare houter hks
    (by simpa [Z] using hold) (by simpa [Z] using hnew)
  exact h.stationaryIdentification u W hu hW hstep

/-- Compactness of the analytic-preserving Route-A orbit upgrades the single
L10 closed-graph residual to the `RotheContinuousDependence` interface used by
the Schauder construction. -/
theorem paperLowerRawParamRotheContinuousDependence
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hκ hM)
    (hlower : RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D)
      (paperLowerRawParamRotheSeq h.producer))
    (hMpos : 0 < M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    RotheContinuousDependence p c lam
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
      (paperLowerRawParamRotheSeq h.producer) := by
  let zseq := paperLowerRawParamRotheSeq h.producer
  let hinput : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (h.producer u hu)
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeq, hinput] using
      paperRouteARotheOrbitData_fromTrap (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hinput
        hκ hM hΛ0 hΛM hbarLip hu
  have hcompactBare : LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M)
      (fun u => rotheLimit (zseq u)) :=
    paperTmap_compactRange_of_uniformModulus
      p c lam M κ hM zseq hdata
  have hlimitLower : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ x, lowerBarrierRaw κ κtilde D x ≤ rotheLimit (zseq u) x :=
    Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower
  have hcompact : LocalUniformSequentiallyCompactRange
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
      (fun u => rotheLimit (zseq u)) := by
    intro seq hseq
    obtain ⟨subseq, hsubseq, U, hUbare, hconv⟩ :=
      hcompactBare seq (fun n => (hseq n).bare)
    refine ⟨subseq, hsubseq, U, ⟨hUbare, ?_⟩, hconv⟩
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hconv.tendsto_at x)
      (Filter.Eventually.of_forall fun n =>
        hlimitLower (seq (subseq n)) (hseq (subseq n)) x)
  have hclosed : LocalUniformSequentialClosedGraphOn
      (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D))
      (fun u => rotheLimit (zseq u)) := by
    simpa [zseq] using paperLowerRawParamRotheLimitClosedGraph
      h hMpos hΛ0 hΛM hbarLip
  have hcont := hcompact.continuousOn_of_closedGraph hclosed
  simpa [zseq] using hcont

/-- Only the left-flatness half of the legacy stationary/flat floor.  The
adaptive Green closed graph now supplies stationarity itself. -/
def PaperLowerPinnedFlatFloor
    (p : CMParams) (c κ M : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
    (∀ x, frozenWaveOperator p c U U x = 0) →
      FrozenStationaryFlatAtLeft p U

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
    (hflat : PaperLowerPinnedFlatFloor p c κ M
      (lowerBarrierRaw κ κtilde D)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  let hinputTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (hpar.producer u hu)
  let zseq := paperLowerRawParamRotheSeqFromTrap hpar
  have hstep : RotheStepLowerInvariant κ M
      (lowerBarrierRaw κ κtilde D) zseq := by
    refine rotheStepLowerInvariant_lowerBarrierRaw_of_paperStepData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (κtilde := κtilde) (D := D) (Λ := Λ)
      hcond hD hD_ge_one ?_
    intro u hu k hprev
    let hp := hpar.producer u hu.bare
    have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
        (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 := by
      simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap, hp] using
        rotheSeqOfPaperRouteAFromTrap_eq hinputTrap hcond.hκ0.le hM0 hu.bare
    rw [hzu] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := hp.lowerRawAux hu k hprev
    have hfacts := rotheSeqOfPaperRouteA_stepFacts
      (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 k
    exact ⟨C_chem, La, Lb,
      (paperLowerRawRouteAParamGreenCore hp).hlam, hfacts.step_op, haux⟩
  have hlower : RotheOrbitLowerBound κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
            (hinputTrap u hu.bare) hcond.hκ0.le hM0 := by
          simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
            rotheSeqOfPaperRouteAFromTrap_eq hinputTrap
              hcond.hκ0.le hM0 hu.bare
        rw [hzu]
        exact rotheSeqOfPaperRouteA_lowerPinned_base (hinputTrap u hu.bare)
          hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
      paperRouteARotheOrbitData_fromTrap (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hinputTrap
        hcond.hκ0.le hM0 hΛ0 hΛM hcond.upperBarrier_barLip hu
  have hlam : 0 < lam :=
    (hpar.producer (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hcond.hκ0.le hM0)).params.hlam
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have hcube : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq
      (upperBarrier_isBddFun hM0)
      (by
        simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
          paperLowerRawParamRotheContinuousDependence hpar hlower
            hMpos hΛ0 hΛM
            hcond.upperBarrier_barLip)
      hdata hlower
  have hgraph : PaperGreenRotheAdaptiveStepClosedGraphOnTrap
      p c lam M κ zseq := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
      paperGreenRotheAdaptiveStepClosedGraph_of_sourceCompactness
        p c lam M κ Λ hMpos hΛ0 hlam
        (paperLowerRawParamRotheSeq hpar.producer)
        (paperLowerRawParamGreenSourceCompactness hpar hMpos hΛ0)
  obtain ⟨U, hU, hstat, hUdiff, hUderivDiff⟩ :=
    paperLowerPinned_adaptiveStationary_of_cubeApproxData
      p c lam M κ (lowerBarrierRaw κ κtilde D) hM0 hlam zseq
      hdata hlower hcube hgraph
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    stationaryProfile_strictlyPositive_of_trap_regularity
      hMpos hU.bare hstat hUdiff hUderivDiff hnontriv
  have hlim_neg : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
      hcond.hκ0 hgap_pos hDpos hU.bare hU.lower (hflat U hU hstat) hstat
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
    (hflat : PaperLowerPinnedFlatFloor p c κ M
      (lowerBarrierRaw κ κtilde D)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  let hinputTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u :=
    fun u hu => paperLowerRawRouteAParamGreenCore (hpar.producer u hu)
  let zseq := paperLowerRawParamRotheSeqFromTrap hpar
  have hstep : RotheStepLowerInvariant κ M
      (lowerBarrierRaw κ κtilde D) zseq := by
    refine rotheStepLowerInvariant_lowerBarrierRaw_of_positivePaperStepData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (κtilde := κtilde) (D := D) (Λ := Λ)
      hcond hD hD_ge_one ?_
    intro u hu k hprev
    let hp := hpar.producer u hu.bare
    have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
        (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 := by
      simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap, hp] using
        rotheSeqOfPaperRouteAFromTrap_eq hinputTrap hcond.hκ0.le hM0 hu.bare
    rw [hzu] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := hp.lowerRawAux hu k hprev
    have hfacts := rotheSeqOfPaperRouteA_stepFacts
      (paperLowerRawRouteAParamGreenCore hp) hcond.hκ0.le hM0 k
    exact ⟨C_chem, La, Lb,
      (paperLowerRawRouteAParamGreenCore hp).hlam, hfacts.step_op, haux⟩
  have hlower : RotheOrbitLowerBound κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        have hzu : zseq u = rotheSeqOfPaperRouteA p c lam M κ Λ u
            (hinputTrap u hu.bare) hcond.hκ0.le hM0 := by
          simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
            rotheSeqOfPaperRouteAFromTrap_eq hinputTrap
              hcond.hκ0.le hM0 hu.bare
        rw [hzu]
        exact rotheSeqOfPaperRouteA_lowerPinned_base (hinputTrap u hu.bare)
          hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u hu
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap, hinputTrap] using
      paperRouteARotheOrbitData_fromTrap (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := u) hinputTrap
        hcond.hκ0.le hM0 hΛ0 hΛM hcond.upperBarrier_barLip hu
  have hlam : 0 < lam :=
    (hpar.producer (upperBarrier κ M)
      (upperBarrier_mem_InMonotoneWaveTrapSet hcond.hκ0.le hM0)).params.hlam
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hExpM :
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M :=
    lowerBarrierExpXPlus_le_one_of_one_le_D hcond.hκ0 hgap_pos
      hD_ge_one hcond.hM
  have hplat : InMonotoneWaveTrapSet κ M
      (lowerBarrierPlateau κ κtilde D) :=
    lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
      hcond.hκ0 hgap_pos hDpos hExpM
  have hcube : LowerPinnedWaveCubeApproxData κ M
      (lowerBarrierRaw κ κtilde D) zseq :=
    lowerPinnedRawWaveCubeApproxData p c lam M κ κtilde D hMpos
      hcond.hκ0 hgap_pos hDpos hplat zseq
      (upperBarrier_isBddFun hM0)
      (by
        simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
          paperLowerRawParamRotheContinuousDependence hpar hlower
            hMpos hΛ0 hΛM
            hcond.upperBarrier_barLip)
      hdata hlower
  have hgraph : PaperGreenRotheAdaptiveStepClosedGraphOnTrap
      p c lam M κ zseq := by
    simpa [zseq, paperLowerRawParamRotheSeqFromTrap] using
      paperGreenRotheAdaptiveStepClosedGraph_of_sourceCompactness
        p c lam M κ Λ hMpos hΛ0 hlam
        (paperLowerRawParamRotheSeq hpar.producer)
        (paperLowerRawParamGreenSourceCompactness hpar hMpos hΛ0)
  obtain ⟨U, hU, hstat, hUdiff, hUderivDiff⟩ :=
    paperLowerPinned_adaptiveStationary_of_cubeApproxData
      p c lam M κ (lowerBarrierRaw κ κtilde D) hM0 hlam zseq
      hdata hlower hcube hgraph
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_positive_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    stationaryProfile_strictlyPositive_of_trap_regularity
      hMpos hU.bare hstat hUdiff hUderivDiff hnontriv
  have hlim_neg : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
      hcond.hκ0 hgap_pos hDpos hU.bare hU.lower (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (nhds 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

/-- Clean negative-branch name after the finite-cube approximation and adaptive
Green source compactness have both become internal theorems. -/
theorem b1_chiNeg_existence_paper_routeA_paramCore_noBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM))
    (hflat : PaperLowerPinnedFlatFloor p c κ M
      (lowerBarrierRaw κ κtilde D)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM hpar hflat

/-- Clean positive-branch name after the finite-cube approximation and adaptive
Green source compactness have both become internal theorems. -/
theorem b1_chiPos_existence_paper_routeA_paramCore_noBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
      p c lam M κ κtilde D Λ hcond.hκ0.le
        (le_trans zero_le_one hcond.hM))
    (hflat : PaperLowerPinnedFlatFloor p c κ M
      (lowerBarrierRaw κ κtilde D)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    p c lam M κ κtilde D Λ hcond hD hD_ge_one hΛ0 hΛM hpar hflat

section AxiomAudit

#print axioms paperRouteAParamGreenCore
#print axioms paperLowerRawParamRotheSeq
#print axioms paperLowerRawParamRotheSeqFromTrap
#print axioms paperLowerRawParamGreenSourceCompactness
#print axioms paperLowerRawParamOffDiagonalStepClosedGraph
#print axioms paperLowerRawParamRotheLimitClosedGraph
#print axioms paperLowerRawParamRotheContinuousDependence
#print axioms PaperLowerPinnedFlatFloor
#print axioms b1_chiNeg_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
#print axioms b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
#print axioms b1_chiNeg_existence_paper_routeA_paramCore_noBar
#print axioms b1_chiPos_existence_paper_routeA_paramCore_noBar

end AxiomAudit

end ShenWork.Paper1
