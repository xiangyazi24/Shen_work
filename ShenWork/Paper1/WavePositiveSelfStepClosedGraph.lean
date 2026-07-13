/- Parameterized whole-line Green closed graph for the positive self step. -/
import ShenWork.Paper1.WavePositiveSelfStepSchauder
import ShenWork.Paper1.WavePositiveFrozenEllipticDep

open Filter Set Topology Real

noncomputable section

namespace ShenWork.Paper1

theorem paperOneStep_closedGraph_of_stepAnalytic_inWaveTrap
    (p : CMParams) (c lam M κ Λ K : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    {us Zs Ws : ℕ → ℝ → ℝ} {u Z W : ℝ → ℝ}
    (husTrap : ∀ n, InWaveTrapSet κ M (us n))
    (huTrap : InWaveTrapSet κ M u) (hWTrap : InWaveTrapSet κ M W)
    (A : ∀ n, PaperStepAnalytic p c lam M κ Λ (us n) (Zs n) (Ws n))
    (hWs0 : ∀ n x, 0 ≤ Ws n x) (hWsM : ∀ n x, Ws n x ≤ M)
    (hWslog : ∀ n x, |deriv (Ws n) x| ≤ K * Ws n x)
    (hus : LocallyUniformConverges us u)
    (hZs : LocallyUniformConverges Zs Z)
    (hWs : LocallyUniformConverges Ws W) :
    (∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x) ∧
      ContDiff ℝ 2 W ∧ (∀ x, |deriv W x| ≤ K * W x) := by
  obtain ⟨_hW1, hWderiv, sub, hsub, hWd⟩ :=
    contDiff_one_of_locallyUniform_paperStepAnalytic
      p c lam M κ Λ hM hΛ hlam A hWs0 hWsM hWs
  have hWsub : LocallyUniformConverges (fun n => Ws (sub n)) W :=
    hWs.comp_strictMono hsub
  have hWlog : ∀ x, |deriv W x| ≤ K * W x := by
    intro x
    exact le_of_tendsto_of_tendsto (hWd.tendsto_at x).abs
      ((hWsub.tendsto_at x).const_mul K)
      (Eventually.of_forall fun n => hWslog (sub n) x)
  have hbddDerivW : LocallyBoundedOnCompacts (fun x => deriv W x) :=
    LocallyBoundedOnCompacts.of_global_bound hΛ hWderiv
  have hus' := hus.comp_strictMono hsub
  have hZs' := hZs.comp_strictMono hsub
  have hsource : LocallyUniformConverges
      (fun n => paperStepSource p c lam (us (sub n)) (Zs (sub n)) (Ws (sub n)))
      (paperStepSource p c lam u Z W) :=
    paperStepSource_locallyUniform_nonDiagonal_inWaveTrap p hM
      (fun n => husTrap (sub n)) huTrap
      (fun n x => hWs0 (sub n) x) (fun n x => hWsM (sub n) x)
      hWTrap.nonneg hWTrap.le_M hus' hZs' hWsub hWd hbddDerivW
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
    exact le_of_tendsto (hRlu.tendsto_at x).abs
      (Eventually.of_forall fun n =>
        paperStep_R_abs_le_from_lambda hlam (A (sub n)) x)
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
        (c := c) (lam := lam) hlam (fun n => (A (sub n)).R_cont) hRcont
        (fun n x => paperStep_R_abs_le_from_lambda hlam (A (sub n)) x)
        hRbound hRlu x
    exact tendsto_nhds_unique hseqGreen hlimitGreen
  have hRhi : ∀ x, MeasureTheory.IntegrableOn
      (gWeight (greenRootPlus c lam) (paperStepSource p c lam u Z W))
        (Set.Ioi x) := fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hRbound x
  have hRlo : ∀ x, MeasureTheory.IntegrableOn
      (gWeight (greenRootMinus c lam) (paperStepSource p c lam u Z W))
        (Set.Iic x) := fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hRbound x
  have hW2 : ContDiff ℝ 2 W := by
    rw [hWgreen]
    exact greenConv_contDiff_two hRcont hRhi hRlo
  exact ⟨paperImplicitStepOp_of_greenConv_source hlam rfl hWgreen
    hRcont hRhi hRlo, hW2, hWlog⟩

theorem paperPositiveSelfStepMap_closedGraph
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD : paperDMin p.χ (MChi p) (kappa c)
      (positiveBranchTailCap p c) p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p)
    (s : Paper1PositiveLocalStepScalarData p c D) :
    LocalUniformSequentialClosedGraphOn
      (InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
        (paperPositiveSelfStepModulus s)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D))
      (paperPositiveSelfStepMap hcond s) := by
  intro seq u V hseq hu hV hinput houtput
  let Ws : ℕ → ℝ → ℝ := fun n => paperPositiveSelfStepMap hcond s (seq n)
  let As : ∀ n, PaperStepAnalytic p c s.lam (MChi p) (kappa c) s.Λ
      (seq n) (seq n) (Ws n) := fun n => by
    rw [show Ws n = (paperPositiveSelfStepData hcond s (hseq n)).fixed.W by
      exact paperPositiveSelfStepMap_eq hcond s (hseq n)]
    exact paperStepAnalytic_of_core s.hlam
      (paperPositiveSelfStepData hcond s (hseq n)).fixed.analyticCore
  let K : ℝ := paperLowerPinnedStepLogSlopeCoeff c s.lam (kappa c)
    (positiveBranchTailCap p c) D (MChi p) s.B
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hMpos : 0 < MChi p := lt_of_lt_of_le zero_lt_one hcond.hM
  have hK : 0 ≤ K := paperLowerPinnedStepLogSlopeCoeff_nonneg
    s.hlam s.hrpκ s.hrmκ hcond.hκ0 (sub_pos.mpr hcond.hgap)
    hDpos hMpos.le s.hB
  have hmaps : ∀ n,
      InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
        (paperPositiveSelfStepModulus s)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) (Ws n) :=
    fun n => paperPositiveSelfStepMap_mapsTo hcond hD hD1 hplateau s (hseq n)
  have hWslog : ∀ n x, |deriv (Ws n) x| ≤ K * Ws n x := by
    intro n x
    have heq : Ws n = (paperPositiveSelfStepData hcond s (hseq n)).fixed.W :=
      paperPositiveSelfStepMap_eq hcond s (hseq n)
    rw [heq]
    exact (paperPositiveSelfStepData hcond s (hseq n)).deriv_abs_le_mul_self_of_lowerBound
      s.hlam s.hrpκ s.hrmκ hcond.hκ0 (sub_pos.mpr hcond.hgap)
      hDpos hMpos.le s.hB (by simpa only [heq] using (hmaps n).lower) x
  have hclosed := paperOneStep_closedGraph_of_stepAnalytic_inWaveTrap
    p c s.lam (MChi p) (kappa c) s.Λ K hMpos s.hΛ0 s.hlam
    (fun n => (hseq n).bare) hu.bare hV.bare As
    (fun n x => (hmaps n).bare.nonneg x)
    (fun n x => (hmaps n).bare.le_M x) hWslog
    hinput hinput (by simpa [Ws] using houtput)
  let d := paperPositiveSelfStepData hcond s hu
  have hdmap := paperPositiveSelfStepMap_mapsTo hcond hD hD1 hplateau s hu
  have hdlog : ∀ x, |deriv d.fixed.W x| ≤ K * d.fixed.W x :=
    d.deriv_abs_le_mul_self_of_lowerBound s.hlam s.hrpκ s.hrmκ
      hcond.hκ0 (sub_pos.mpr hcond.hgap) hDpos hMpos.le s.hB
      (by rw [← paperPositiveSelfStepMap_eq hcond s hu]; exact hdmap.lower)
  have hVrange : ∀ x, V x ∈ Set.Icc (0 : ℝ) (MChi p) :=
    fun x => ⟨hV.bare.nonneg x, hV.bare.le_M x⟩
  have hdrange : ∀ x, d.fixed.W x ∈ Set.Icc (0 : ℝ) (MChi p) :=
    fun x => ⟨(d.range x).1, (d.range x).2.trans (upperBarrier_le_M _ _ _)⟩
  have huniq : V = d.fixed.W :=
    paperImplicitStep_unique_positive_of_pinned_smooth
      s.hlam hMpos hu.bare (by simpa [K] using s.pinnedStep_small) hK
      hclosed.1 (d.step_op s.hlam) hclosed.2.1 (d.contDiff_two s.hlam)
      hVrange hdrange hclosed.2.2 hdlog
  calc
    V = d.fixed.W := huniq
    _ = paperPositiveSelfStepMap hcond s u :=
      (paperPositiveSelfStepMap_eq hcond s hu).symm

theorem paperPositiveSelfStepMap_continuousOn
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD : paperDMin p.χ (MChi p) (kappa c)
      (positiveBranchTailCap p c) p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p)
    (s : Paper1PositiveLocalStepScalarData p c D) :
    LocalUniformContinuousOn
      (InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
        (paperPositiveSelfStepModulus s)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D))
      (paperPositiveSelfStepMap hcond s) :=
  (paperPositiveSelfStepMap_compactRange hcond hD hD1 hplateau s).continuousOn_of_closedGraph
    (paperPositiveSelfStepMap_closedGraph hcond hD hD1 hplateau s)

/-- Schauder--Tychonoff produces a fixed point of the genuine positive
self-step.  At the diagonal the exact paper step is the stationary frozen
wave equation. -/
theorem paperPositive_fixed_stationary_of_selfStep
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD : paperDMin p.χ (MChi p) (kappa c)
      (positiveBranchTailCap p c) p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p)
    (s : Paper1PositiveLocalStepScalarData p c D) :
    ∃ U,
      InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
        (paperPositiveSelfStepModulus s)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U ∧
      paperPositiveSelfStepMap hcond s U = U ∧
      ∃ _A : PaperStepAnalytic p c s.lam (MChi p) (kappa c) s.Λ U U U,
        (∀ x, frozenWaveOperator p c U U x = 0) ∧ ContDiff ℝ 2 U := by
  let trap := InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
    (paperPositiveSelfStepModulus s)
    (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D)
  have hne : ∃ u, trap u :=
    paperPositiveC1UniformTrap_nonempty hcond hD hD1 hplateau s
  have hmap : ∀ u, trap u → trap (paperPositiveSelfStepMap hcond s u) :=
    fun _ hu => paperPositiveSelfStepMap_mapsTo hcond hD hD1 hplateau s hu
  obtain ⟨U, hU, hfix⟩ :=
    (InLowerPinnedC1UniformModulusWaveTrap.boundedConvexProfileTrapData hne).exists_fixed
      hmap (paperPositiveSelfStepMap_continuousOn hcond hD hD1 hplateau s)
      (paperPositiveSelfStepMap_compactRange hcond hD hD1 hplateau s)
  let d := paperPositiveSelfStepData hcond s hU
  have hdU : d.fixed.W = U := by
    calc
      d.fixed.W = paperPositiveSelfStepMap hcond s U :=
        (paperPositiveSelfStepMap_eq hcond s hU).symm
      _ = U := hfix
  have hA : PaperStepAnalytic p c s.lam (MChi p) (kappa c) s.Λ U U U := by
    simpa only [hdU] using paperStepAnalytic_of_core s.hlam d.fixed.analyticCore
  have hU2 : ContDiff ℝ 2 U := by simpa only [hdU] using d.contDiff_two s.hlam
  have hstep : ∀ x, paperImplicitStepOp p c (1 / s.lam) U U x = U x := by
    simpa only [hdU] using d.step_op s.hlam
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self
      p c s.lam U s.hlam hU.bare.cunif_bdd hU.bare.nonneg
      (hU2.differentiable (by norm_num))
      (fun x => frozenElliptic_deriv_differentiableAt p
        hU.bare.cunif_bdd hU.bare.nonneg x)
      (fun x => (hU2.differentiable (by norm_num) x).rpow_const
        (Or.inr p.hm)) hstep
  exact ⟨U, hU, hfix, hA, hstat, hU2⟩

section AxiomAudit

#print axioms paperOneStep_closedGraph_of_stepAnalytic_inWaveTrap
#print axioms paperPositiveSelfStepMap_closedGraph
#print axioms paperPositiveSelfStepMap_continuousOn
#print axioms paperPositive_fixed_stationary_of_selfStep

end AxiomAudit

end ShenWork.Paper1
