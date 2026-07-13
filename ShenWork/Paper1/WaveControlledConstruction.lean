import ShenWork.Paper1.WaveControlledRouteA
import ShenWork.Paper1.WaveControlledSchauder
import ShenWork.Paper1.WavePaperSingleOrbitClosedGraph

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Schauder fixed point of the corrected controlled Rothe map.  Source-box
existence, compactness, invariance, and the finite-dimensional
Schauder--Tychonoff construction are internal; the only map-level analytic
input is the explicitly named L10 continuous-dependence statement. -/
theorem paperControlledLowerRaw_exists_fixed
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hsigma : 0 < sigma)
    (hne : ∃ u, InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u)
    (hdep : PaperControlledLowerRawContinuousDependence floor) :
    ∃ U, InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) U ∧
      rotheLimit (paperControlledLowerRawRotheSeq floor U) = U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u =>
    rotheLimit (paperControlledLowerRawRotheSeq floor u)
  have hmap : ∀ u,
      InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) u →
      InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) (Tmap u) :=
    paperControlledLowerRaw_mapsTo floor hcond hD hD_ge_one
      hΛ0 hΛM hbarLip hsigma
  have hcompact : LocalUniformSequentiallyCompactRange
      (InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D)) Tmap :=
    paperControlledLowerRaw_compactRange floor hmap
  have hfix :=
    (InControlledLowerPinnedMonotoneTrap.boundedConvexProfileTrapData hne).exists_fixed
      hmap hdep hcompact
  simpa [Tmap] using hfix

/-- Adaptive whole-line Green closed graph at a fixed point of the controlled
long-time map.  No globally uniform Rothe tail is used. -/
theorem paperControlledLowerRaw_fixed_stationary
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hMpos : 0 < M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    {U : ℝ → ℝ}
    (hU : InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) U)
    (hfix : rotheLimit (paperControlledLowerRawRotheSeq floor U) = U) :
    (∀ x, frozenWaveOperator p c U U x = 0) ∧
      Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  let prod := floor.producer U hU
  let z := rotheSeqOfPaperRouteA p c lam M κ Λ U
    prod.core.toOrbitCore hκ hM
  have hdata := prod.core.orbitData hκ hM hΛ0 hΛM hbarLip
  have hlimit : rotheLimit z = U := by
    simpa [z, paperControlledLowerRawRotheSeq_eq floor hU] using hfix
  have hLU : LocallyUniformConverges z U := by
    rw [← hlimit]
    simpa [z] using hdata.locallyUniform hM
  have hLU_succ : LocallyUniformConverges (fun n => z (n + 1)) U :=
    hLU.comp_strictMono (strictMono_id.add_const 1)
  obtain ⟨hstep, hUdiff, hUderivDiff⟩ :=
    paperGreenSingleOrbitClosedGraph_of_stepAnalytic
      p c lam M κ Λ hMpos hΛ0 prod.core.hlam U hU.bare z
      (by
        intro k
        simpa [z] using rotheSeqOfPaperRouteA_stepAnalytic
          prod.core.toOrbitCore hκ hM k)
      (by
        intro k x
        simpa [z] using rotheSeqOfPaperRouteA_nonneg
          prod.core.toOrbitCore hκ hM (k + 1) x)
      (by
        intro k x
        simpa [z] using rotheSeqOfPaperRouteA_le_M
          prod.core.toOrbitCore hκ hM (k + 1) x)
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

#print axioms paperControlledLowerRaw_exists_fixed
#print axioms paperControlledLowerRaw_fixed_stationary

end AxiomAudit

end ShenWork.Paper1
