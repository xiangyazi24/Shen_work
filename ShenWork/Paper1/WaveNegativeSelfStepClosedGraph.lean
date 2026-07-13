import ShenWork.Paper1.WaveNegativeSelfStepSchauder
import ShenWork.Paper1.WavePaperSingleOrbitClosedGraph

open Filter Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-! ## Parameterized one-step Green closed graph

This is the whole-line, non-diagonal closed graph needed by the selected
self-step map.  Frozen profiles, old profiles, and new profiles may converge
independently.  No time-tail or family-uniform spatial tail is assumed.
-/

/-- Closed graph for a locally-uniformly convergent family of genuine
whole-line Green steps.  A common lower-pinned logarithmic-slope estimate is
retained in the limit; it is the input needed for same-right-hand-side
uniqueness. -/
theorem paperOneStep_closedGraph_of_stepAnalytic
    (p : CMParams) (c lam M κ Λ K : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    {us Zs Ws : ℕ → ℝ → ℝ} {u Z W : ℝ → ℝ}
    (husTrap : ∀ n, InMonotoneWaveTrapSet κ M (us n))
    (huTrap : InMonotoneWaveTrapSet κ M u)
    (hWTrap : InMonotoneWaveTrapSet κ M W)
    (A : ∀ n, PaperStepAnalytic p c lam M κ Λ (us n) (Zs n) (Ws n))
    (hWs0 : ∀ n x, 0 ≤ Ws n x)
    (hWsM : ∀ n x, Ws n x ≤ M)
    (hWslog : ∀ n x, |deriv (Ws n) x| ≤ K * Ws n x)
    (hus : LocallyUniformConverges us u)
    (hZs : LocallyUniformConverges Zs Z)
    (hWs : LocallyUniformConverges Ws W) :
    (∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x) ∧
      ContDiff ℝ 2 W ∧
      (∀ x, |deriv W x| ≤ K * W x) := by
  obtain ⟨hW1, hWderiv, sub, hsub, hWd⟩ :=
    contDiff_one_of_locallyUniform_paperStepAnalytic
      p c lam M κ Λ hM hΛ hlam A hWs0 hWsM hWs
  have hWsub : LocallyUniformConverges (fun n => Ws (sub n)) W :=
    hWs.comp_strictMono hsub
  have hWlog : ∀ x, |deriv W x| ≤ K * W x := by
    intro x
    have hleft : Tendsto (fun n => |deriv (Ws (sub n)) x|)
        atTop (𝓝 |deriv W x|) := (hWd.tendsto_at x).abs
    have hright : Tendsto (fun n => K * Ws (sub n) x)
        atTop (𝓝 (K * W x)) := (hWsub.tendsto_at x).const_mul K
    exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun n => hWslog (sub n) x)
  have hbddDerivW : LocallyBoundedOnCompacts (fun x => deriv W x) :=
    LocallyBoundedOnCompacts.of_global_bound hΛ hWderiv
  have hus' : LocallyUniformConverges (fun n => us (sub n)) u :=
    hus.comp_strictMono hsub
  have hZs' : LocallyUniformConverges (fun n => Zs (sub n)) Z :=
    hZs.comp_strictMono hsub
  have hWs' : LocallyUniformConverges (fun n => Ws (sub n)) W := hWsub
  have hsource : LocallyUniformConverges
      (fun n => paperStepSource p c lam (us (sub n))
        (Zs (sub n)) (Ws (sub n)))
      (paperStepSource p c lam u Z W) :=
    paperStepSource_locallyUniform_nonDiagonal p hM
      (fun n => husTrap (sub n)) huTrap
      (fun n x => hWs0 (sub n) x)
      (fun n x => hWsM (sub n) x)
      hWTrap.nonneg hWTrap.le_M hus' hZs' hWs' hWd hbddDerivW
  have hRlu : LocallyUniformConverges
      (fun n => (A (sub n)).R) (paperStepSource p c lam u Z W) := by
    have heq : (fun n => (A (sub n)).R) =
        fun n => paperStepSource p c lam (us (sub n))
          (Zs (sub n)) (Ws (sub n)) := by
      funext n
      exact (A (sub n)).source_eq
    simpa [heq] using hsource
  let B : ℝ := paperStepRBoundFromLambda c lam Λ
  have hRbound : ∀ x, |paperStepSource p c lam u Z W x| ≤ B := by
    intro x
    refine le_of_tendsto (hRlu.tendsto_at x).abs ?_
    exact Eventually.of_forall fun n =>
      paperStep_R_abs_le_from_lambda hlam (A (sub n)) x
  have hRcont : Continuous (paperStepSource p c lam u Z W) :=
    continuous_of_locallyUniform (fun n => (A (sub n)).R_cont) hRlu
  have hWgreen : W = fun x =>
      greenConv c lam (paperStepSource p c lam u Z W) x := by
    funext x
    have hseqGreen : Tendsto
        (fun n => greenConv c lam (A (sub n)).R x) atTop (𝓝 (W x)) := by
      have heq : (fun n => Ws (sub n) x) =
          fun n => greenConv c lam (A (sub n)).R x := by
        funext n
        exact congrFun (A (sub n)).green_repr x
      simpa [heq] using hWsub.tendsto_at x
    have hlimitGreen :=
      greenConv_tendsto_of_source_locallyUniform_of_uniform_bound
        (c := c) (lam := lam) hlam (fun n => (A (sub n)).R_cont)
        hRcont
        (fun n x => paperStep_R_abs_le_from_lambda hlam (A (sub n)) x)
        hRbound hRlu x
    exact tendsto_nhds_unique hseqGreen hlimitGreen
  have hRhi : ∀ x, MeasureTheory.IntegrableOn
      (gWeight (greenRootPlus c lam) (paperStepSource p c lam u Z W))
        (Set.Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hRbound x
  have hRlo : ∀ x, MeasureTheory.IntegrableOn
      (gWeight (greenRootMinus c lam) (paperStepSource p c lam u Z W))
        (Set.Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hRbound x
  have hW2 : ContDiff ℝ 2 W := by
    rw [hWgreen]
    exact greenConv_contDiff_two hRcont hRhi hRlo
  exact
    ⟨paperImplicitStepOp_of_greenConv_source hlam rfl hWgreen
      hRcont hRhi hRlo,
      hW2, hWlog⟩

/-! ## Closed graph and continuity of the selected negative self step -/

/-- The selected negative self-step map has a sequentially closed graph.
Green compactness gives a limiting step, and lower-pinned same-RHS uniqueness
identifies that limit with the selected solution at the limiting parameter. -/
theorem paperNegativePinnedSelfStepMap_closedGraph
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D) :
    LocalUniformSequentialClosedGraphOn
      (InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
        (paperNegativePinnedOrbitModulus s)
        (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D))
      (paperNegativePinnedSelfStepMap s) := by
  intro seq u V hseq hu hV hinput houtput
  let Ws : ℕ → ℝ → ℝ := fun n => paperNegativePinnedSelfStepMap s (seq n)
  let As : ∀ n, PaperStepAnalytic p c s.lam 1 (kappa c) s.Λ
      (seq n) (seq n) (Ws n) := fun n => by
    rw [show Ws n =
        (paperNegativePinnedSelfStepData s (hseq n)).fixed.W by
      exact paperNegativePinnedSelfStepMap_eq s (hseq n)]
    exact paperStepAnalytic_of_core s.hlam
      (paperNegativePinnedSelfStepData s (hseq n)).fixed.analyticCore
  let K : ℝ := paperLowerPinnedStepLogSlopeCoeff c s.lam (kappa c)
    (negativeBranchTailCap p c) D 1 s.B
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hK : 0 ≤ K :=
    paperLowerPinnedStepLogSlopeCoeff_nonneg
      s.hlam s.hrpκ s.hrmκ s.hκ (sub_pos.mpr hcond.hgap)
      hDpos zero_le_one s.hB
  have hmaps : ∀ n,
      InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
        (paperNegativePinnedOrbitModulus s)
        (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) (Ws n) :=
    fun n => paperNegativePinnedSelfStepMap_mapsTo
      hcond hD hD1 s (hseq n)
  have hWslog : ∀ n x, |deriv (Ws n) x| ≤ K * Ws n x := by
    intro n x
    have heq : Ws n =
        (paperNegativePinnedSelfStepData s (hseq n)).fixed.W :=
      paperNegativePinnedSelfStepMap_eq s (hseq n)
    rw [heq]
    exact (paperNegativePinnedSelfStepData s (hseq n)).deriv_abs_le_mul_self_of_lowerPinned
      s.hlam s.hrpκ s.hrmκ s.hκ (sub_pos.mpr hcond.hgap)
      hDpos zero_le_one s.hB (by
        simpa only [heq] using (hmaps n).toLowerPinned) x
  have hclosed := paperOneStep_closedGraph_of_stepAnalytic
    p c s.lam 1 (kappa c) s.Λ K one_pos s.hΛ0 s.hlam
    (fun n => (hseq n).bare) hu.bare hV.bare As
    (fun n x => (hmaps n).bare.nonneg x)
    (fun n x => (hmaps n).bare.le_M x) hWslog
    hinput hinput (by simpa [Ws] using houtput)
  let d := paperNegativePinnedSelfStepData s hu
  have hdlog : ∀ x, |deriv d.fixed.W x| ≤ K * d.fixed.W x :=
    d.deriv_abs_le_mul_self_of_lowerPinned
      s.hlam s.hrpκ s.hrmκ s.hκ (sub_pos.mpr hcond.hgap)
      hDpos zero_le_one s.hB
      (by
        rw [← paperNegativePinnedSelfStepMap_eq s hu]
        exact (paperNegativePinnedSelfStepMap_mapsTo
          hcond hD hD1 s hu).toLowerPinned)
  have hVrange : ∀ x, V x ∈ Set.Icc (0 : ℝ) 1 :=
    fun x => ⟨hV.bare.nonneg x, hV.bare.le_M x⟩
  have hdrange : ∀ x, d.fixed.W x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨(d.range x).1,
      (d.range x).2.trans (upperBarrier_le_M (kappa c) 1 x)⟩
  have huniq : V = d.fixed.W :=
    paperImplicitStep_unique_of_pinned_smooth
      s.hlam one_pos hu.bare
      (paperFrozenEllipticSourceBox_of_conditions hcond)
      s.barrier.hχ s.pinnedStep_small (by
        unfold paperPinnedStepCmono K
        exact le_rfl) hK
      hclosed.1 (d.step_op s.hlam) hclosed.2.1
      (d.contDiff_two s.hlam) hVrange hdrange hclosed.2.2 hdlog
  calc
    V = d.fixed.W := huniq
    _ = paperNegativePinnedSelfStepMap s u :=
      (paperNegativePinnedSelfStepMap_eq s hu).symm

/-- Compact range plus the preceding Green closed graph gives genuine
compact-open continuity of the selected self-step map. -/
theorem paperNegativePinnedSelfStepMap_continuousOn
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D) :
    LocalUniformContinuousOn
      (InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
        (paperNegativePinnedOrbitModulus s)
        (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D))
      (paperNegativePinnedSelfStepMap s) :=
  (paperNegativePinnedSelfStepMap_compactRange hcond hD hD1 s).continuousOn_of_closedGraph
    (paperNegativePinnedSelfStepMap_closedGraph hcond hD hD1 s)

section AxiomAudit

#print axioms paperOneStep_closedGraph_of_stepAnalytic
#print axioms paperNegativePinnedSelfStepMap_closedGraph
#print axioms paperNegativePinnedSelfStepMap_continuousOn

end AxiomAudit

end ShenWork.Paper1
