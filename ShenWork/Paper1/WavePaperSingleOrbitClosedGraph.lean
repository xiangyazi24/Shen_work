import ShenWork.Paper1.WavePaperAdaptiveSourceCompactness

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Whole-line Green closed graph for one frozen Rothe orbit.  This is the
single-orbit specialization actually needed after Schauder has produced a
fixed point of the long-time map. -/
theorem paperGreenSingleOrbitClosedGraph_of_stepAnalytic
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    (u : ℝ → ℝ) (hu : InMonotoneWaveTrapSet κ M u)
    (z : ℕ → ℝ → ℝ)
    (hanalytic : ∀ k,
      PaperStepAnalytic p c lam M κ Λ u (z k) (z (k + 1)))
    (hnew0 : ∀ k x, 0 ≤ z (k + 1) x)
    (hnewM : ∀ k x, z (k + 1) x ≤ M)
    (W : ℝ → ℝ) (hW : InMonotoneWaveTrapSet κ M W)
    (ks : ℕ → ℕ) (_hks : Tendsto ks atTop atTop)
    (hold : LocallyUniformConverges (fun n => z (ks n)) W)
    (hnew : LocallyUniformConverges (fun n => z (ks n + 1)) W)
    (hdiag : u = W) :
    (∀ x, paperImplicitStepOp p c (1 / lam) u W x = W x) ∧
      Differentiable ℝ W ∧ Differentiable ℝ (deriv W) ∧
      PaperGreenSourceTailData c lam W := by
  let Zs : ℕ → ℝ → ℝ := fun n => z (ks n)
  let Ws : ℕ → ℝ → ℝ := fun n => z (ks n + 1)
  let A : ∀ n, PaperStepAnalytic p c lam M κ Λ u (Zs n) (Ws n) :=
    fun n => hanalytic (ks n)
  let C2 : ℝ := paperStepC2Bound c lam M Λ
  let Q : ℝ := max Λ C2
  have hC2 : 0 ≤ C2 := paperStepC2Bound_nonneg hlam hM.le hΛ
  have hQ : 0 ≤ Q := by
    rcases le_total Λ C2 with h | h
    · simpa [Q, max_eq_right h] using hC2
    · simpa [Q, max_eq_left h] using hΛ
  have hderivLip : ∀ n x y,
      |deriv (Ws n) x - deriv (Ws n) y| ≤ Q * |x - y| := by
    intro n x y
    have hdiff : Differentiable ℝ (fun t => deriv (Ws n) t) :=
      fun t => (paperStep_hasDerivAt_deriv (A n) t).differentiableAt
    have hbound : ∀ t, |deriv (fun s => deriv (Ws n) s) t| ≤ C2 := by
      intro t
      rw [(paperStep_hasDerivAt_deriv (A n) t).deriv]
      exact paperStep_second_deriv_le hlam hM.le hΛ
        (fun y => by
          rw [abs_of_nonneg (hnew0 (ks n) y)]
          exact hnewM (ks n) y)
        (A n) t
    exact le_trans (abs_sub_le_of_deriv_abs_le_core hdiff hbound x y)
      (mul_le_mul_of_nonneg_right (le_max_right Λ C2) (abs_nonneg _))
  have hderivBdd : ∀ n x, |deriv (Ws n) x| ≤ Q := by
    intro n x
    exact le_trans (paperStep_deriv_le hlam (A n) x) (le_max_left Λ C2)
  obtain ⟨sub, hsub, D, hDpt, hDLip⟩ :=
    helly_pointwise_selection Q (fun n x => deriv (Ws n) x)
      hderivLip hderivBdd
  have hDLU : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) D :=
    locallyUniform_of_helly_pointwise hQ hDpt hderivLip hDLip
  have hWsub : LocallyUniformConverges (fun n => Ws (sub n)) W := by
    simpa [Ws] using hnew.comp_strictMono hsub
  have hWhas : ∀ x, HasDerivAt W (D x) x := by
    intro x
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := fun n => Ws (sub n)) (g := W)
      (f' := fun n x => deriv (Ws (sub n)) x) (g' := D)
      isOpen_univ hDLU.tendstoLocallyUniformlyOn_univ
      (Eventually.of_forall fun n y _hy =>
        paperStep_hasDerivAt_value (A (sub n)) y)
      (fun y _hy => hWsub.tendsto_at y) (Set.mem_univ x)
  have hD_eq : D = fun x => deriv W x := by
    funext x
    exact (hWhas x).deriv.symm
  have hWd : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) (fun x => deriv W x) := by
    simpa [hD_eq] using hDLU
  have hderivW : ∀ x, |deriv W x| ≤ Λ := by
    intro x
    rw [← congrFun hD_eq x]
    refine le_of_tendsto (hDpt x).abs ?_
    exact Eventually.of_forall fun n => paperStep_deriv_le hlam (A (sub n)) x
  have hbddDerivW : LocallyBoundedOnCompacts (fun x => deriv W x) :=
    LocallyBoundedOnCompacts.of_global_bound hΛ hderivW
  have hold' : LocallyUniformConverges (fun n => Zs (sub n)) W := by
    simpa [Zs] using hold.comp_strictMono hsub
  have hconst : LocallyUniformConverges (fun _ : ℕ => u) u :=
    LocallyUniformConverges.const u
  have hsource : LocallyUniformConverges
      (fun n => paperStepSource p c lam u (Zs (sub n)) (Ws (sub n)))
      (paperStepSource p c lam u W W) :=
    paperStepSource_locallyUniform_nonDiagonal p hM
      (fun _ => hu) hu
      (fun n x => hnew0 (ks (sub n)) x)
      (fun n x => hnewM (ks (sub n)) x)
      hW.nonneg hW.le_M hconst hold' hWsub hWd hbddDerivW
  have hRlu : LocallyUniformConverges
      (fun n => (A (sub n)).R) (paperStepSource p c lam u W W) := by
    have heq : (fun n => (A (sub n)).R) =
        fun n => paperStepSource p c lam u (Zs (sub n)) (Ws (sub n)) := by
      funext n
      exact (A (sub n)).source_eq
    simpa [heq] using hsource
  let B : ℝ := paperStepRBoundFromLambda c lam Λ
  have hRbound : ∀ x, |paperStepSource p c lam u W W x| ≤ B := by
    intro x
    refine le_of_tendsto (hRlu.tendsto_at x).abs ?_
    exact Eventually.of_forall fun n =>
      paperStep_R_abs_le_from_lambda hlam (A (sub n)) x
  have hRcont : Continuous (paperStepSource p c lam u W W) :=
    continuous_of_locallyUniform (fun n => (A (sub n)).R_cont) hRlu
  have hWgreen : W = fun x =>
      greenConv c lam (paperStepSource p c lam u W W) x := by
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
      (gWeight (greenRootPlus c lam) (paperStepSource p c lam u W W))
        (Set.Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hRbound x
  have hRlo : ∀ x, MeasureTheory.IntegrableOn
      (gWeight (greenRootMinus c lam) (paperStepSource p c lam u W W))
        (Set.Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hRbound x
  obtain ⟨hWdiff, hWderivDiff⟩ :=
    stationaryC2Regularity_of_greenRepresentation
      hRcont hRhi hRlo hWgreen
  have hWabs : ∀ x, |W x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hW.nonneg x)]
    exact hW.le_M x
  have hWgreenDiag : W = fun x =>
      greenConv c lam (paperStepSource p c lam W W W) x := by
    simpa only [hdiag] using hWgreen
  have hRcontDiag : Continuous (paperStepSource p c lam W W W) := by
    simpa only [hdiag] using hRcont
  have hRboundDiag : ∀ x, |paperStepSource p c lam W W W x| ≤ B := by
    simpa only [hdiag] using hRbound
  obtain ⟨hWhas, hWhas2, C1, C2, hC10, hC20, hC1, hC2⟩ :=
    greenLimit_derivative_data hlam hM.le hWgreenDiag hRcontDiag
      hRboundDiag hWabs
  have hbddAbove : BddAbove (Set.range W) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hW.le_M x
  have hbddBelow : BddBelow (Set.range W) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hW.nonneg x
  obtain ⟨⟨LW, hWlim⟩, _⟩ :=
    antitone_tendsto_atBot_atTop_of_bdd hW.antitone hbddAbove hbddBelow
  have hsecondBound : ∀ x, |deriv (deriv W) x| ≤ C2 := by
    intro x
    rw [(hWhas2 x).deriv]
    exact hC2 x
  have hD1 : Tendsto (fun x => deriv W x) atBot (nhds 0) :=
    antitone_deriv_tendsto_atBot_zero_of_tail_of_second_bound
      hW.antitone hWlim (fun x => (hWhas x).differentiableAt)
      (fun x => (hWhas2 x).differentiableAt) hC20 hsecondBound
  obtain ⟨LR, hcrossTail⟩ :=
    crossSource_tendsto_atBot_of_profile_tail_and_deriv_tail
      (p := p) (lam := lam) (M := M) hM hW
      (fun x => (hWhas x).differentiableAt) hWlim hD1
  have hdiagSource :
      paperStepSource p c lam W W W = crossSource p lam W W W :=
    paperStepSource_self_eq_crossSource
      hW.trap.cunif_bdd hW.nonneg hWhas
  have hRtail : Tendsto (paperStepSource p c lam W W W) atBot (nhds LR) := by
    rw [hdiagSource]
    exact hcrossTail
  have hsourceTail : PaperGreenSourceTailData c lam W :=
    ⟨paperStepSource p c lam W W W, B, LR, hRcontDiag, hRboundDiag,
      hRtail, hWgreenDiag⟩
  exact
    ⟨paperImplicitStepOp_of_greenConv_source hlam rfl hWgreen
      hRcont hRhi hRlo,
      hWdiff, hWderivDiff, hsourceTail⟩

section AxiomAudit

#print axioms paperGreenSingleOrbitClosedGraph_of_stepAnalytic

end AxiomAudit

end ShenWork.Paper1
