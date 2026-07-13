import ShenWork.Paper1.WaveSharedRateOrbit
import ShenWork.Paper1.WaveControlledSchauder
import ShenWork.Paper1.WavePaperSingleOrbitClosedGraph

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Lower-barrier data attached to the genuine shared-rate orbit. -/
structure PaperSharedRateControlledLowerRawStepProducer
    (p : CMParams) (c lam M κ κtilde D Λ sigma aL C : ℝ)
    (u : ℝ → ℝ) where
  core : PaperGreenStepInputRouteASharedRateOrbitCore
    p c lam M κ Λ sigma aL C u
  lowerRawAux : ∀ k,
    (∀ x, lowerBarrierRaw κ κtilde D x ≤
      rotheSeqOfPaperSharedRate
        p c lam M κ Λ sigma aL C u core k x) →
      ∃ C_chem La Lb,
        PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
          (rotheSeqOfPaperSharedRate
            p c lam M κ Λ sigma aL C u core (k + 1))

/-- A floor only on the compact controlled parameter trap, with amplitude `M`,
spatial modulus `L`, and left-tail radius `C` kept independent. -/
structure PaperSharedRateControlledLowerRawFloor
    (p : CMParams) (c lam M κ κtilde D Λ L sigma aL C : ℝ) : Type where
  producer : ∀ u,
    InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) u →
    PaperSharedRateControlledLowerRawStepProducer
      p c lam M κ κtilde D Λ sigma aL C u

def paperSharedRateControlledRotheSeq
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => by
    classical
    exact if hu : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D) u then
      rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u
        (floor.producer u hu).core
    else fun _ => upperBarrier κ M

@[simp] theorem paperSharedRateControlledRotheSeq_eq
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    {u : ℝ → ℝ}
    (hu : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) u) :
    paperSharedRateControlledRotheSeq floor u =
      rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u
        (floor.producer u hu).core := by
  simp [paperSharedRateControlledRotheSeq, hu]

theorem paperSharedRateControlled_orbitData
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    {u : ℝ → ℝ}
    (hu : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) u) :
    PaperRotheOrbitDataWithModulus p c lam M κ L
      (paperSharedRateControlledRotheSeq floor u) := by
  simpa only [paperSharedRateControlledRotheSeq_eq floor hu] using
    paperSharedRate_orbitData (floor.producer u hu).core hΛ0 hΛL hbarLip

theorem paperSharedRateControlled_stepLowerInvariant
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
      (paperSharedRateControlledRotheSeq floor) := by
  intro u hu k hprev
  by_cases huC : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) u
  · let prod := floor.producer u huC
    rw [paperSharedRateControlledRotheSeq_eq floor huC] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := prod.lowerRawAux k hprev
    have hstep := rotheSeqOfPaperSharedRate_stepFacts prod.core k
    exact lowerBarrier_step_ge_of_paperData
      (paperLowerBarrierStepData_lowerBarrierRaw_of_paperStep
        (Λ := Λ) hcond hD hD_ge_one hu hprev prod.core.hlam
        hstep.step_op haux)
  · simp [paperSharedRateControlledRotheSeq, huC]
    exact fun x => le_trans (hu.lower x) (hu.bare.le_upperBarrier x)

theorem paperSharedRateControlled_orbitLowerBound
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    ∀ u, InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) u →
      ∀ k x, lowerBarrierRaw κ κtilde D x ≤
        paperSharedRateControlledRotheSeq floor u k x := by
  intro u hu
  apply rotheOrbitLowerBound_of_stepLowerInvariant
    (φ := lowerBarrierRaw κ κtilde D)
    (rotheSeq := paperSharedRateControlledRotheSeq floor) ?_
    (paperSharedRateControlled_stepLowerInvariant floor hcond hD hD_ge_one)
    u ⟨hu.bare, hu.lower⟩
  intro v hv x
  by_cases hvC : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) v
  · rw [paperSharedRateControlledRotheSeq_eq floor hvC,
      rotheSeqOfPaperSharedRate_zero]
    exact le_trans (hv.lower x) (hv.bare.le_upperBarrier x)
  · simp [paperSharedRateControlledRotheSeq, hvC]
    exact le_trans (hv.lower x) (hv.bare.le_upperBarrier x)

theorem paperSharedRateControlled_mapsTo
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|) :
    ∀ u, InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) u →
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D)
        (rotheLimit (paperSharedRateControlledRotheSeq floor u)) := by
  intro u hu
  let hdata := paperSharedRateControlled_orbitData
    floor hΛ0 hΛL hbarLip hu
  have hbare : InMonotoneWaveTrapSet κ M
      (rotheLimit (paperSharedRateControlledRotheSeq floor u)) :=
    rotheLimit_mem_trap (hdata.limit_continuous hL) hdata.bddBelow
      hdata.anti_x hdata.nonneg hdata.le_upperBarrier
      (upperBarrier_isBddFun hM)
  have hlower : ∀ x, lowerBarrierRaw κ κtilde D x ≤
      rotheLimit (paperSharedRateControlledRotheSeq floor u) x := by
    intro x
    exact rotheLimit_ge_of_ge
      (paperSharedRateControlled_orbitLowerBound
        floor hcond hD hD_ge_one u hu) x
  have hrate := paperSharedRate_rotheLimit_rate
    (floor.producer u hu).core hL hΛ0 hΛL hbarLip
  exact
    { uniformTrap := ⟨hbare, hdata.limitLip⟩
      lower := hlower
      leftRateData := by
        simpa only [paperSharedRateControlledRotheSeq_eq floor hu] using hrate }

theorem paperSharedRateControlled_compactRange
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hmap : ∀ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D) u →
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D)
        (rotheLimit (paperSharedRateControlledRotheSeq floor u))) :
    LocalUniformSequentiallyCompactRange
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D))
      (fun u => rotheLimit (paperSharedRateControlledRotheSeq floor u)) := by
  intro seq hseq
  simpa using
    (InControlledLowerPinnedMonotoneTrap.locallyUniform_sequentiallyCompact
      (κ := κ) (M := M) (L := L) (sigma := sigma) (aL := aL) (C := C)
      (φ := lowerBarrierRaw κ κtilde D) hM hL
      (fun n => rotheLimit (paperSharedRateControlledRotheSeq floor (seq n)))
      (fun n => hmap (seq n) (hseq n)))

/-- Exact L10 for the corrected shared-rate construction. -/
def PaperSharedRateControlledContinuousDependence
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C) : Prop :=
  LocalUniformContinuousOn
    (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D))
    (fun u => rotheLimit (paperSharedRateControlledRotheSeq floor u))

/-- Schauder--Tychonoff fixed point for the corrected map.  Finite-cube data,
compactness, invariance, and all source-box witnesses are internal. -/
theorem paperSharedRateControlled_exists_fixed
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    (hne : ∃ u, InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) u)
    (hdep : PaperSharedRateControlledContinuousDependence floor) :
    ∃ U, InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D) U ∧
      rotheLimit (paperSharedRateControlledRotheSeq floor U) = U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u =>
    rotheLimit (paperSharedRateControlledRotheSeq floor u)
  have hmap : ∀ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D) u →
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D) (Tmap u) :=
    paperSharedRateControlled_mapsTo floor hcond hD hD_ge_one
      hM hL hΛ0 hΛL hbarLip
  have hcompact : LocalUniformSequentiallyCompactRange
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
        (lowerBarrierRaw κ κtilde D)) Tmap :=
    paperSharedRateControlled_compactRange floor hM hL hmap
  have hfix :=
    (InControlledLowerPinnedMonotoneTrap.boundedConvexProfileTrapData hne).exists_fixed
      hmap hdep hcompact
  simpa [Tmap] using hfix

/-- Adaptive whole-line closed graph at a fixed point of the shared-rate map. -/
theorem paperSharedRateControlled_fixed_stationary
    {p : CMParams} {c lam M κ κtilde D Λ L sigma aL C : ℝ}
    (floor : PaperSharedRateControlledLowerRawFloor
      p c lam M κ κtilde D Λ L sigma aL C)
    (hM : 0 < M) (hL : 0 ≤ L)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    {U : ℝ → ℝ}
    (hU : InControlledLowerPinnedMonotoneTrap κ M L sigma aL C
      (lowerBarrierRaw κ κtilde D) U)
    (hfix : rotheLimit (paperSharedRateControlledRotheSeq floor U) = U) :
    (∀ x, frozenWaveOperator p c U U x = 0) ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  let prod := floor.producer U hU
  let z := rotheSeqOfPaperSharedRate
    p c lam M κ Λ sigma aL C U prod.core
  let hdata := paperSharedRate_orbitData prod.core hΛ0 hΛL hbarLip
  have hlimit : rotheLimit z = U := by
    simpa [z, paperSharedRateControlledRotheSeq_eq floor hU] using hfix
  have hLU : LocallyUniformConverges z U := by
    rw [← hlimit]
    exact hdata.locallyUniform hL
  have hLU_succ : LocallyUniformConverges (fun n => z (n + 1)) U :=
    hLU.comp_strictMono (strictMono_id.add_const 1)
  obtain ⟨hstep, hUdiff, hUderivDiff⟩ :=
    paperGreenSingleOrbitClosedGraph_of_stepAnalytic
      p c lam M κ Λ hM hΛ0 prod.core.hlam U hU.bare z
      (by
        intro k
        simpa [z] using rotheSeqOfPaperSharedRate_stepAnalytic prod.core k)
      (by
        intro k x
        simpa [z] using rotheSeqOfPaperSharedRate_nonneg prod.core (k + 1) x)
      (by
        intro k x
        simpa [z] using rotheSeqOfPaperSharedRate_le_M prod.core (k + 1) x)
      U hU.bare id tendsto_id hLU hLU_succ
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self
      p c lam U prod.core.hlam hU.bare.trap.cunif_bdd hU.bare.nonneg
      hUdiff
      (fun x => frozenElliptic_deriv_differentiableAt p
        hU.bare.trap.cunif_bdd hU.bare.nonneg x)
      (fun x => (hUdiff x).rpow_const (Or.inr p.hm)) hstep
  exact ⟨hstat, hUdiff, hUderivDiff⟩

section AxiomAudit

#print axioms paperSharedRateControlled_mapsTo
#print axioms paperSharedRateControlled_compactRange
#print axioms paperSharedRateControlled_exists_fixed
#print axioms paperSharedRateControlled_fixed_stationary

end AxiomAudit

end ShenWork.Paper1
