/-
  Whole-line Green closed graph for the adaptive Rothe diagonal.

  The compactness input below asks only for a locally-uniform cluster of the
  actual Green sources, with their common global bound.  All passage from that
  source cluster to the self implicit step is proved here.
-/
import ShenWork.Paper1.WavePaperRotheCompactness
import ShenWork.Paper1.WavePaperTermConvergence
import ShenWork.Paper1.WaveFrozenEllipticValueDep

open Filter Topology Set MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- A locally-uniform cluster of the genuine whole-line Green sources for a
moving family of single paper steps. -/
structure PaperGreenMovingStepSourceCluster
    (p : CMParams) (c lam M κ Λ : ℝ)
    (us Zs Ws : ℕ → ℝ → ℝ) where
  sub : ℕ → ℕ
  sub_strictMono : StrictMono sub
  analytic : ∀ n, PaperStepAnalytic p c lam M κ Λ
    (us (sub n)) (Zs (sub n)) (Ws (sub n))
  R : ℝ → ℝ
  R_cont : Continuous R
  B : ℝ
  source_bound : ∀ n x, |(analytic n).R x| ≤ B
  limit_bound : ∀ x, |R x| ≤ B
  source_locallyUniform :
    LocallyUniformConverges (fun n => (analytic n).R) R
  new_nonneg : ∀ n x, 0 ≤ Ws (sub n) x
  new_le_M : ∀ n x, Ws (sub n) x ≤ M

/-- The sole compactness payload left before the closed-graph passage: every
adaptive moving family of actual steps has a locally-uniform Green-source
cluster. -/
def PaperGreenRotheAdaptiveSourceCompactnessOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (U : ℝ → ℝ) (ks : ℕ → ℕ),
    (∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      InMonotoneWaveTrapSet κ M U →
      LocallyUniformConverges seq U →
      Tendsto ks atTop atTop →
      LocallyUniformConverges (fun n => rotheSeq (seq n) (ks n)) U →
      LocallyUniformConverges (fun n => rotheSeq (seq n) (ks n + 1)) U →
        Nonempty (PaperGreenMovingStepSourceCluster p c lam M κ Λ seq
          (fun n => rotheSeq (seq n) (ks n))
          (fun n => rotheSeq (seq n) (ks n + 1)))

/-- A bounded continuous whole-line Green representation gives first and
second derivative data and global bounds for its profile. -/
private theorem greenLimit_derivative_data
    {c lam M : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M)
    {U R : ℝ → ℝ} {B : ℝ}
    (hUgreen : U = fun x => greenConv c lam R x)
    (hRcont : Continuous R) (hRbound : ∀ x, |R x| ≤ B)
    (hUabs : ∀ x, |U x| ≤ M) :
    (∀ x, HasDerivAt U (deriv U x) x) ∧
      (∀ x, HasDerivAt (fun y => deriv U y) (iteratedDeriv 2 U x) x) ∧
      ∃ C1 C2, 0 ≤ C1 ∧ 0 ≤ C2 ∧
        (∀ x, |deriv U x| ≤ C1) ∧
        ∀ x, |iteratedDeriv 2 U x| ≤ C2 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (R 0)) (hRbound 0)
  have hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Set.Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hRbound x
  have hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Set.Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hRbound x
  have hUhas : ∀ x, HasDerivAt U (deriv U x) x := by
    intro x
    have hgc := greenConv_hasDerivAt
      (c := c) (lam := lam) hRcont hRhi hRlo x
    rw [hUgreen]
    simpa [hgc.deriv] using hgc
  have hUderivEq :
      (fun x => deriv U x) = fun x => greenConvDeriv c lam R x := by
    funext x
    have hgc := greenConv_hasDerivAt
      (c := c) (lam := lam) hRcont hRhi hRlo x
    have heq := congrArg (fun f : ℝ → ℝ => deriv f x) hUgreen
    exact heq.trans hgc.deriv
  have hUiterEq : ∀ x,
      iteratedDeriv 2 U x = greenConvDeriv2 c lam R x := by
    intro x
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
    change deriv (fun y => deriv U y) x = greenConvDeriv2 c lam R x
    rw [hUderivEq]
    exact (greenConvDeriv_hasDerivAt
      (c := c) (lam := lam) hRcont hRhi hRlo x).deriv
  have hUhas2 : ∀ x,
      HasDerivAt (fun y => deriv U y) (iteratedDeriv 2 U x) x := by
    intro x
    rw [hUderivEq, hUiterEq]
    exact greenConvDeriv_hasDerivAt
      (c := c) (lam := lam) hRcont hRhi hRlo x
  let C1 : ℝ := 2 * (greenDelta c lam)⁻¹ * B
  have hC10 : 0 ≤ C1 := by
    dsimp [C1]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_pos.mpr (greenDelta_pos (c := c) hlam)).le)
      hB0
  have hC1 : ∀ x, |deriv U x| ≤ C1 := by
    intro x
    have hbd := greenConvDeriv_abs_le
      (c := c) (lam := lam) hlam hRbound hRhi hRlo x
    simpa [C1, hUderivEq] using hbd
  have hUsecond : ∀ x,
      iteratedDeriv 2 U x = -R x - c * deriv U x + lam * U x := by
    intro x
    have hsolve :
        iteratedDeriv 2 U x + c * deriv U x - lam * U x = -R x := by
      rw [hUiterEq x, congrFun hUderivEq x, congrFun hUgreen x]
      exact greenConv_solves (c := c) (lam := lam) hlam (H := R) x
    linarith
  let C2 : ℝ := B + |c| * C1 + |lam| * M
  have hC20 : 0 ≤ C2 := by
    dsimp [C2]
    positivity
  have hC2 : ∀ x, |iteratedDeriv 2 U x| ≤ C2 := by
    intro x
    rw [hUsecond x]
    calc
      |-R x - c * deriv U x + lam * U x|
          ≤ |-R x - c * deriv U x| + |lam * U x| := abs_add_le _ _
      _ ≤ (|-R x| + |-(c * deriv U x)|) + |lam * U x| := by
        exact add_le_add (abs_add_le _ _) le_rfl
      _ = |R x| + |c| * |deriv U x| + |lam| * |U x| := by
        rw [abs_neg, abs_neg, abs_mul, abs_mul]
      _ ≤ C2 := by
        dsimp [C2]
        have hc := mul_le_mul_of_nonneg_left (hC1 x) (abs_nonneg c)
        have hl := mul_le_mul_of_nonneg_left (hUabs x) (abs_nonneg lam)
        linarith [hRbound x]
  exact ⟨hUhas, hUhas2, C1, C2, hC10, hC20, hC1, hC2⟩

/-- The whole-line Green source cluster closes the adaptive graph.  This is
the parameterized Green closed-graph passage: source DCT identifies the limit
Green representation, interpolation gives derivative convergence, and the
non-diagonal paper source passes to the self source. -/
theorem paperGreenRotheAdaptiveStepClosedGraph_of_sourceCompactness
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hcompact : PaperGreenRotheAdaptiveSourceCompactnessOnTrap
      p c lam M κ Λ rotheSeq) :
    PaperGreenRotheAdaptiveStepClosedGraphOnTrap p c lam M κ rotheSeq := by
  intro seq U ks hseq hU houter hks hold hnew
  let Zs : ℕ → ℝ → ℝ := fun n => rotheSeq (seq n) (ks n)
  let Ws : ℕ → ℝ → ℝ := fun n => rotheSeq (seq n) (ks n + 1)
  obtain ⟨cluster⟩ := hcompact seq U ks hseq hU houter hks hold hnew
  let sub := cluster.sub
  let A := cluster.analytic
  have hsub : StrictMono sub := cluster.sub_strictMono
  have houter' : LocallyUniformConverges (fun n => seq (sub n)) U :=
    houter.comp_strictMono hsub
  have hold' : LocallyUniformConverges (fun n => Zs (sub n)) U := by
    simpa [Zs] using hold.comp_strictMono hsub
  have hnew' : LocallyUniformConverges (fun n => Ws (sub n)) U := by
    simpa [Ws] using hnew.comp_strictMono hsub
  have hB0 : 0 ≤ cluster.B :=
    le_trans (abs_nonneg (cluster.R 0)) (cluster.limit_bound 0)
  have hUabs : ∀ x, |U x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hU.nonneg x)]
    exact hU.le_M x
  have hUgreen : U = fun x => greenConv c lam cluster.R x := by
    funext x
    have hWsGreen : Tendsto
        (fun n => greenConv c lam (A n).R x) atTop (𝓝 (U x)) := by
      have heq : (fun n => Ws (sub n) x) =
          fun n => greenConv c lam (A n).R x := by
        funext n
        exact congrFun (A n).green_repr x
      simpa [heq] using hnew'.tendsto_at x
    have hGreenR := greenConv_tendsto_of_source_locallyUniform_of_uniform_bound
      (c := c) (lam := lam) hlam (fun n => (A n).R_cont)
      cluster.R_cont cluster.source_bound cluster.limit_bound
      cluster.source_locallyUniform x
    exact tendsto_nhds_unique hWsGreen hGreenR
  obtain ⟨hUhas, hUhas2, C1, C2, hC10, hC20, hC1, hC2⟩ :=
    greenLimit_derivative_data hlam hM.le hUgreen cluster.R_cont
      cluster.limit_bound hUabs
  have hstepC2 : 0 ≤ paperStepC2Bound c lam M Λ :=
    paperStepC2Bound_nonneg hlam hM.le hΛ
  have hderivWsLip : UniformLipschitzOnCompacts
      (fun n x => deriv (Ws (sub n)) x) :=
    UniformLipschitzOnCompacts.of_hasDerivAt_bound hstepC2
      (fun n x => paperStep_hasDerivAt_deriv (A n) x)
      (fun n x => paperStep_second_deriv_le hlam hM.le hΛ
        (fun y => by
          rw [abs_of_nonneg (cluster.new_nonneg n y)]
          exact cluster.new_le_M n y)
        (A n) x)
  have hderivULip : LipschitzOnCompacts (fun x => deriv U x) :=
    LipschitzOnCompacts.of_hasDerivAt_bound hC20 hUhas2 hC2
  have hderivWs : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) (fun x => deriv U x) :=
    hnew'.deriv_of_hasDerivAt_of_residual_lipschitz
      (fun n x => paperStep_hasDerivAt_value (A n) x) hUhas
      (UniformResidualLipschitzOnCompacts.of_pair hderivWsLip hderivULip)
  have hV : LocallyUniformConverges
      (fun n => frozenElliptic p (seq (sub n))) (frozenElliptic p U) :=
    frozenEllipticDependence p hM.le (fun n => seq (sub n)) U
      (fun n => hseq (sub n)) hU houter'
  have hVd : LocallyUniformConverges
      (fun n x => deriv (frozenElliptic p (seq (sub n))) x)
      (fun x => deriv (frozenElliptic p U) x) :=
    frozenEllipticDerivDependence p hM.le (fun n => seq (sub n)) U
      (fun n => hseq (sub n)) hU houter'
  have hpowM : LocallyUniformConverges
      (fun n x => (Ws (sub n) x) ^ (p.m - 1))
      (fun x => (U x) ^ (p.m - 1)) :=
    hnew'.rpow_of_nonneg_le (by linarith [p.hm]) hM.le
      cluster.new_nonneg cluster.new_le_M hU.nonneg hU.le_M
  have hpowA : LocallyUniformConverges
      (fun n x => (Ws (sub n) x) ^ p.α) (fun x => (U x) ^ p.α) :=
    hnew'.rpow_of_nonneg_le (by linarith [p.hα]) hM.le
      cluster.new_nonneg cluster.new_le_M hU.nonneg hU.le_M
  have hpowMG : LocallyUniformConverges
      (fun n x => (Ws (sub n) x) ^ (p.m + p.γ - 1))
      (fun x => (U x) ^ (p.m + p.γ - 1)) :=
    hnew'.rpow_of_nonneg_le (by linarith [p.hm, p.hγ]) hM.le
      cluster.new_nonneg cluster.new_le_M hU.nonneg hU.le_M
  have hpowBound : LocallyBoundedOnCompacts
      (fun x => (U x) ^ (p.m - 1)) :=
    LocallyBoundedOnCompacts.of_global_bound
      (Real.rpow_nonneg hM.le (p.m - 1)) (fun x => by
        rw [abs_of_nonneg (Real.rpow_nonneg (hU.nonneg x) _)]
        exact Real.rpow_le_rpow (hU.nonneg x) (hU.le_M x)
          (by linarith [p.hm]))
  have hUbound : LocallyBoundedOnCompacts U :=
    LocallyBoundedOnCompacts.of_global_bound hM.le hUabs
  have hDUbound : LocallyBoundedOnCompacts (fun x => deriv U x) :=
    LocallyBoundedOnCompacts.of_global_bound hC10 hC1
  have hMγ0 : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM.le p.γ
  have hVbound : LocallyBoundedOnCompacts (frozenElliptic p U) := by
    refine LocallyBoundedOnCompacts.of_global_bound hMγ0 ?_
    intro x
    rw [abs_of_nonneg (frozenElliptic_nonneg p hU.nonneg x)]
    exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hU.trap x
  have hVdbound : LocallyBoundedOnCompacts
      (fun x => deriv (frozenElliptic p U) x) := by
    refine LocallyBoundedOnCompacts.of_global_bound hMγ0 ?_
    intro x
    exact le_trans (frozenElliptic_deriv_abs_le p
      hU.trap.cunif_bdd hU.nonneg x)
      (frozenElliptic_le_rpow_of_inWaveTrapSet p hM hU.trap x)
  have hpowVd := hpowM.mul hVd hpowBound hVdbound
  have hpowVdBound := hpowBound.mul hVdbound
  have hchemCore := hpowVd.mul hderivWs hpowVdBound hDUbound
  have hchemCore' : LocallyUniformConverges
      (fun n => paperWaveChemCore p (seq (sub n)) (Ws (sub n)))
      (paperWaveChemCore p U U) := by
    simpa [paperWaveChemCore, mul_assoc] using hchemCore
  have hchem : LocallyUniformConverges
      (fun n => paperWaveChemTerm p (seq (sub n)) (Ws (sub n)))
      (paperWaveChemTerm p U U) := by
    simpa [paperWaveChemTerm] using hchemCore'.const_mul (-p.χ * p.m)
  have hpowV := hpowM.mul hV hpowBound hVbound
  have hχpowV := hpowV.const_mul p.χ
  have hleft := hχpowV.const_sub 1
  have hright := hpowA.sub (hpowMG.const_mul p.χ)
  have hbracket : LocallyUniformConverges
      (fun n => paperWaveReactionBracket p (seq (sub n)) (Ws (sub n)))
      (paperWaveReactionBracket p U U) := by
    simpa [paperWaveReactionBracket, mul_assoc] using hleft.sub hright
  have hbracketBound : LocallyBoundedOnCompacts
      (paperWaveReactionBracket p U U) := by
    exact ((LocallyBoundedOnCompacts.const 1).sub
      (hpowBound.mul hVbound |>.const_mul p.χ)).sub
      ((LocallyBoundedOnCompacts.of_global_bound
          (Real.rpow_nonneg hM.le p.α) (fun x => by
            rw [abs_of_nonneg (Real.rpow_nonneg (hU.nonneg x) _)]
            exact Real.rpow_le_rpow (hU.nonneg x) (hU.le_M x)
              (le_trans zero_le_one p.hα)))
        |>.sub
          (LocallyBoundedOnCompacts.of_global_bound
            (Real.rpow_nonneg hM.le (p.m + p.γ - 1)) (fun x => by
              rw [abs_of_nonneg (Real.rpow_nonneg (hU.nonneg x) _)]
              exact Real.rpow_le_rpow (hU.nonneg x) (hU.le_M x)
                (by linarith [p.hm, p.hγ]))
            |>.const_mul p.χ))
  have hreaction : LocallyUniformConverges
      (fun n => paperWaveReactionTerm p (seq (sub n)) (Ws (sub n)))
      (paperWaveReactionTerm p U U) := by
    simpa [paperWaveReactionTerm] using
      hnew'.mul hbracket hUbound hbracketBound
  have hsource : LocallyUniformConverges
      (fun n => paperStepSource p c lam (seq (sub n))
        (Zs (sub n)) (Ws (sub n)))
      (paperStepSource p c lam U U U) := by
    have hnonlin := hchem.add hreaction
    have hlin := hold'.const_mul lam
    simpa [paperStepSource_eq_terms, add_assoc] using hnonlin.add hlin
  have hsourceEq : cluster.R = paperStepSource p c lam U U U := by
    funext x
    have hRlim := cluster.source_locallyUniform.tendsto_at x
    have hSlim := hsource.tendsto_at x
    have heq : (fun n => (A n).R x) = fun n =>
        paperStepSource p c lam (seq (sub n))
          (Zs (sub n)) (Ws (sub n)) x := by
      funext n
      exact congrFun (A n).source_eq x
    rw [heq] at hRlim
    exact tendsto_nhds_unique hRlim hSlim
  have hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) cluster.R) (Set.Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) cluster.R_cont
      cluster.limit_bound x
  have hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) cluster.R) (Set.Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) cluster.R_cont
      cluster.limit_bound x
  exact ⟨paperImplicitStepOp_of_greenConv_source hlam hsourceEq hUgreen
    cluster.R_cont hRhi hRlo, fun x => (hUhas x).differentiableAt⟩

section AxiomAudit

#print axioms paperGreenRotheAdaptiveStepClosedGraph_of_sourceCompactness

end AxiomAudit

end ShenWork.Paper1
