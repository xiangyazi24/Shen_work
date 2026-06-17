import ShenWork.Paper1.WavePaperTermConvergence
import ShenWork.Paper1.WaveRotheStationary
import Mathlib.Topology.Order.MonotoneConvergence

namespace ShenWork.Paper1

noncomputable section

open Filter Topology MeasureTheory Real Set

/-- The precise limit-passage floor needed to turn a paper Rothe fixed point
into a fixed point of the diagonal paper implicit step. -/
def PaperRotheLimitFixedStepIdentity
    (p : CMParams) (c lam κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
    rotheLimit (rotheSeq U) = U →
      paperImplicitStepOp p c (1 / lam) U U = U

/-- The actual operator-continuity estimate needed for the fixed-step route:
if `z k → U` locally uniformly, then the diagonal paper implicit residuals along
`z (k+1)` converge locally uniformly to the residual at `U`. -/
def PaperImplicitStepLimitPassage
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (z : ℕ → ℝ → ℝ) : Prop :=
  LocallyUniformConverges z U →
    LocallyUniformConverges
      (fun k => paperImplicitStepOp p c (1 / lam) U (z (k + 1)))
      (paperImplicitStepOp p c (1 / lam) U U)

/-- Profile-wise version of `PaperImplicitStepLimitPassage` for a pinned Rothe
map. -/
def PaperRotheStepLimitPassage
    (p : CMParams) (c lam κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
    LocallyUniformConverges (rotheSeq U) U →
      PaperImplicitStepLimitPassage p c lam U (rotheSeq U)

/-- The diagonal differentiability floor needed only for the identity
`paperWaveOperator = frozenWaveOperator` at `W = U`. -/
structure PaperDiagonalDifferentiabilityFloor
    (p : CMParams) (κ M : ℝ) (φ : ℝ → ℝ) : Prop where
  U_diff :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ U x
  V_diff :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p U)) x
  rpow_diff :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ (fun y => (U y) ^ p.m) x

theorem paperDiagonalDifferentiabilityFloor_of_c3BootstrapData
    {p : CMParams} {κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hc3 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        PaperC3BootstrapData U (rotheSeq U)) :
    PaperDiagonalDifferentiabilityFloor p κ M φ where
  U_diff := by
    intro U hU x
    exact ((hc3 U hU).limit_hasDeriv_value x).differentiableAt
  V_diff := by
    intro U hU x
    exact frozenElliptic_deriv_differentiableAt p
      hU.bare.trap.cunif_bdd hU.bare.nonneg x
  rpow_diff := by
    intro U hU x
    exact (((hc3 U hU).limit_hasDeriv_value x).differentiableAt).rpow_const
      (Or.inr p.hm)

theorem paperImplicitStep_fixed_paperWaveOperator_zero
    (p : CMParams) (c h : ℝ) (U : ℝ → ℝ)
    (hh : h ≠ 0)
    (hfix : paperImplicitStepOp p c h U U = U) :
    ∀ x, paperWaveOperator p c U U x = 0 := by
  intro x
  have hx := congrFun hfix x
  rw [paperImplicitStepOp_apply] at hx
  have hmul : h * paperWaveOperator p c U U x = 0 := by
    linarith
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact (hh hzero).elim
  · exact hzero

theorem paperImplicitStep_fixed_frozenWaveOperator_zero
    {p : CMParams} {c h κ M : ℝ} {φ U : ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hh : h ≠ 0)
    (hfix : paperImplicitStepOp p c h U U = U) :
    ∀ x, frozenWaveOperator p c U U x = 0 := by
  intro x
  have hpaper :
      paperWaveOperator p c U U x = 0 :=
    paperImplicitStep_fixed_paperWaveOperator_zero p c h U hh hfix x
  have hbare : InMonotoneWaveTrapSet κ M U := hU.bare
  have hUcb : IsCUnifBdd U := hbare.1.1
  have hUnonneg : ∀ x, 0 ≤ U x := fun y => (hbare.1.2 y).1
  have hdiag :
      paperWaveOperator p c U U x = frozenWaveOperator p c U U x :=
    paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x hUcb hUnonneg
      (hdiff.U_diff U hU x) (hdiff.V_diff U hU x)
      (hdiff.rpow_diff U hU x)
  simpa [hdiag] using hpaper

theorem paperLimit_fixedStepIdentity_of_stepLimitPassage
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hlim : rotheLimit z = U)
    (hLU : LocallyUniformConverges z (rotheLimit z))
    (hstep :
      ∀ k, paperImplicitStepOp p c (1 / lam) U (z (k + 1)) = z k)
    (hpass : PaperImplicitStepLimitPassage p c lam U z) :
    paperImplicitStepOp p c (1 / lam) U U = U := by
  have hLU_U : LocallyUniformConverges z U := by
    simpa [hlim] using hLU
  have hsame :
      ∀ᶠ k in Filter.atTop,
        z k = paperImplicitStepOp p c (1 / lam) U (z (k + 1)) :=
    Filter.Eventually.of_forall fun k => (hstep k).symm
  have hop_to_U :
      LocallyUniformConverges
        (fun k => paperImplicitStepOp p c (1 / lam) U (z (k + 1))) U :=
    LocallyUniformConverges.congr hsame hLU_U
  exact LocallyUniformConverges.unique (hpass hLU_U) hop_to_U

theorem paperRotheLimitFixedStepIdentity_of_stepLimitPassage
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hpass : PaperRotheStepLimitPassage p c lam κ M φ rotheSeq) :
    PaperRotheLimitFixedStepIdentity p c lam κ M φ rotheSeq := by
  intro U hU hlim
  have hLU_U : LocallyUniformConverges (rotheSeq U) U := by
    simpa [hlim] using hLU U hU
  exact paperLimit_fixedStepIdentity_of_stepLimitPassage hlim (hLU U hU)
    (hstep U hU) (hpass U hU hLU_U)

theorem PaperWaveOperatorTermConvergence.implicitStepLimitPassage
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hterms : PaperWaveOperatorTermConvergence p c U z) :
    PaperImplicitStepLimitPassage p c lam U z := by
  intro hLU
  have hshift :
      LocallyUniformConverges (fun k => z (k + 1)) U := by
    exact hLU.comp_strictMono
      (strictMono_nat_of_lt_succ fun n => Nat.lt_succ_self (n + 1))
  have hop := hterms.operator
  have hres :
      LocallyUniformConverges
        (fun k x => z (k + 1) x
          - (1 / lam) * paperWaveOperator p c U (z (k + 1)) x)
        (fun x => U x - (1 / lam) * paperWaveOperator p c U U x) :=
    hshift.sub (hop.const_mul (1 / lam))
  simpa [paperImplicitStepOp_apply] using hres

theorem paperRotheStepLimitPassage_of_termConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hterms :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperWaveOperatorTermConvergence p c U (rotheSeq U)) :
    PaperRotheStepLimitPassage p c lam κ M φ rotheSeq := by
  intro U hU hLU
  exact (hterms U hU hLU).implicitStepLimitPassage

theorem paperRotheStepLimitPassage_of_c2CompactConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hc2 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactConvergence p U (rotheSeq U)) :
    PaperRotheStepLimitPassage p c lam κ M φ rotheSeq :=
  paperRotheStepLimitPassage_of_termConvergence
    (fun U hU hLU => (hc2 U hU hLU).termConvergence)

theorem paperRotheStepLimitPassage_of_uniformBounds
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hbounds :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactUniformBounds p U (rotheSeq U)) :
    PaperRotheStepLimitPassage p c lam κ M φ rotheSeq :=
  paperRotheStepLimitPassage_of_c2CompactConvergence
    (fun U hU hLU =>
      paperC2CompactConvergence_of_uniformBounds hLU (hbounds U hU hLU))

theorem paperRotheLimitStepConsistency_of_termConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hterms :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperWaveOperatorTermConvergence p c U (rotheSeq U)) :
    PaperRotheLimitStepConsistency p c lam κ M φ rotheSeq := by
  intro U hU hlim x
  have hpass : PaperRotheStepLimitPassage p c lam κ M φ rotheSeq :=
    paperRotheStepLimitPassage_of_termConvergence hterms
  have hfixed : PaperRotheLimitFixedStepIdentity p c lam κ M φ rotheSeq :=
    paperRotheLimitFixedStepIdentity_of_stepLimitPassage hLU hstep hpass
  exact congrFun (hfixed U hU hlim) x

theorem paperRotheLimitStepConsistency_of_c2CompactConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hc2 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactConvergence p U (rotheSeq U)) :
    PaperRotheLimitStepConsistency p c lam κ M φ rotheSeq :=
  paperRotheLimitStepConsistency_of_termConvergence hLU hstep
    (fun U hU hLU_U => (hc2 U hU hLU_U).termConvergence)

theorem paperRotheLimitStepConsistency_of_uniformBounds
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hbounds :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactUniformBounds p U (rotheSeq U)) :
    PaperRotheLimitStepConsistency p c lam κ M φ rotheSeq :=
  paperRotheLimitStepConsistency_of_c2CompactConvergence hLU hstep
    (fun U hU hLU_U =>
      paperC2CompactConvergence_of_uniformBounds hLU_U (hbounds U hU hLU_U))

theorem paperLowerPinnedStationary_of_fixedStepIdentity
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hfixed : PaperRotheLimitFixedStepIdentity p c lam κ M φ rotheSeq)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 := by
  intro U hU hlim
  exact paperImplicitStep_fixed_frozenWaveOperator_zero hU hdiff
    (one_div_ne_zero (ne_of_gt hlam)) (hfixed U hU hlim)

/-- Explicit Green source-tail data for a stationary profile.  This is the
non-flat analytic datum needed by the convolution-tail argument. -/
def FrozenStationaryGreenSourceTail (c lam : ℝ) (U : ℝ → ℝ) : Prop :=
  ∃ R : ℝ → ℝ, ∃ B L : ℝ,
    Continuous R ∧ (∀ y, |R y| ≤ B) ∧ Tendsto R atBot (𝓝 L) ∧
      U = fun x => greenConv c lam R x

theorem frozenStationaryGreenSourceTail_of_crossImplicitMap_fixed
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ}
    (hlam : 0 < lam)
    (hdata : StationaryCrossGreenData p c lam U)
    (hR_cont : Continuous (crossSource p lam U U U))
    (hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B)
    (hR_tail : ∃ L : ℝ, Tendsto (crossSource p lam U U U) atBot (𝓝 L))
    (hcross : crossImplicitMap p c lam U U U = U) :
    FrozenStationaryGreenSourceTail c lam U := by
  rcases hR_bound with ⟨B, hB⟩
  rcases hR_tail with ⟨L, hL⟩
  refine ⟨crossSource p lam U U U, B, L, hR_cont, hB, hL, ?_⟩
  calc
    U = crossImplicitMap p c lam U U U := hcross.symm
    _ = fun x => greenConv c lam (crossSource p lam U U U) x :=
        StationaryCrossGreenData.crossImplicitMap_eq_greenConv_crossSource
          (p := p) (c := c) (lam := lam) (U := U) hlam hdata

theorem frozenStationaryGreenSourceTail_of_frozenWaveOperator_zero
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ}
    (hlam : 0 < lam)
    (hdata : StationaryCrossGreenData p c lam U)
    (hR_cont : Continuous (crossSource p lam U U U))
    (hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B)
    (hR_tail : ∃ L : ℝ, Tendsto (crossSource p lam U U U) atBot (𝓝 L))
    (hU_diff : Differentiable ℝ U)
    (hU'_diff : Differentiable ℝ (deriv U))
    (hU_bdd : ∃ M : ℝ, ∀ x, |U x| ≤ M)
    (hU'_bdd : ∃ M : ℝ, ∀ x, |deriv U x| ≤ M)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    FrozenStationaryGreenSourceTail c lam U := by
  rcases hR_bound with ⟨BR, hBR⟩
  have hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam U U U)) (Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR_cont hBR x
  have hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam U U U)) (Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR_cont hBR x
  have hcross : crossImplicitMap p c lam U U U = U :=
    frozenWaveOperator_zero_crossImplicitMap_fixed
      (p := p) (c := c) (lam := lam) (U := U) hlam hdata
      hR_cont ⟨BR, hBR⟩ hRhi hRlo hU_diff hU'_diff hU_bdd hU'_bdd
      hstat
  exact frozenStationaryGreenSourceTail_of_crossImplicitMap_fixed
    (p := p) (c := c) (lam := lam) (U := U)
    hlam hdata hR_cont ⟨BR, hBR⟩ hR_tail hcross

theorem lowerPinnedStationaryGreenSourceTail_of_frozenWaveOperator_zero
    {p : CMParams} {c lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z)
    (hdata : StationaryCrossGreenData p c lam U)
    (hR_cont : Continuous (crossSource p lam U U U))
    (hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B)
    (hR_tail : ∃ L : ℝ, Tendsto (crossSource p lam U U U) atBot (𝓝 L))
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    FrozenStationaryGreenSourceTail c lam U := by
  have hU_diff : Differentiable ℝ U := fun x =>
    (hc3.limit_hasDeriv_value x).differentiableAt
  have hU'_diff : Differentiable ℝ (deriv U) := fun x =>
    (hc3.limit_hasDeriv_deriv x).differentiableAt
  have hU_bdd : ∃ C : ℝ, ∀ x, |U x| ≤ C := by
    refine ⟨M, ?_⟩
    intro x
    rw [abs_of_nonneg (hU.bare.nonneg x)]
    exact hU.bare.le_M x
  obtain ⟨CU', _hCU'_nonneg, hCU'⟩ := hc3.limit_deriv_bound
  have hU'_bdd : ∃ C : ℝ, ∀ x, |deriv U x| ≤ C := ⟨CU', hCU'⟩
  exact frozenStationaryGreenSourceTail_of_frozenWaveOperator_zero
    (p := p) (c := c) (lam := lam) (U := U)
    hlam hdata hR_cont hR_bound hR_tail
    hU_diff hU'_diff hU_bdd hU'_bdd
    hstat

/-- A bounded antitone real profile has finite limits at both spatial tails. -/
theorem antitone_tendsto_atBot_atTop_of_bdd
    {U : ℝ → ℝ}
    (hanti : Antitone U)
    (hbddAbove : BddAbove (Set.range U))
    (hbddBelow : BddBelow (Set.range U)) :
    (∃ L, Tendsto U atBot (𝓝 L)) ∧
      (∃ L, Tendsto U atTop (𝓝 L)) := by
  exact ⟨⟨⨆ x, U x, tendsto_atBot_ciSup hanti hbddAbove⟩,
    ⟨⨅ x, U x, tendsto_atTop_ciInf hanti hbddBelow⟩⟩

/-- Every lower-pinned monotone trap profile has finite left and right tail
limits.  This is the trap-level part of the stationary Green source-tail
argument. -/
theorem inLowerPinnedMonotoneTrap_profile_tail_limits
    {κ M : ℝ} {φ U : ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    (∃ L, Tendsto U atBot (𝓝 L)) ∧
      (∃ L, Tendsto U atTop (𝓝 L)) := by
  have hbare : InMonotoneWaveTrapSet κ M U := hU.bare
  have hbddAbove : BddAbove (Set.range U) := by
    refine ⟨M, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hbare.le_M x
  have hbddBelow : BddBelow (Set.range U) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hbare.nonneg x
  exact antitone_tendsto_atBot_atTop_of_bdd
    hbare.antitone hbddAbove hbddBelow

/-- Barbalat-type one-sided tail lemma used for monotone trap profiles: an
antitone `C²` profile with a finite left limit and bounded second derivative has
first derivative tending to zero at `-∞`. -/
theorem antitone_deriv_tendsto_atBot_zero_of_tail_of_second_bound
    {U : ℝ → ℝ} {L C : ℝ}
    (hanti : Antitone U)
    (hlim : Tendsto U atBot (𝓝 L))
    (hU_diff : Differentiable ℝ U)
    (hU'_diff : Differentiable ℝ (deriv U))
    (hC_nonneg : 0 ≤ C)
    (hU''_bound : ∀ x, |deriv (deriv U) x| ≤ C) :
    Tendsto (fun x => deriv U x) atBot (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδ_def
  have hC1_pos : 0 < C + 1 := by linarith
  have hden_pos : 0 < 2 * (C + 1) := by positivity
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    exact div_pos hε hden_pos
  have hCδ_le : C * δ ≤ ε / 2 := by
    rw [hδ_def]
    have hden_ne : 2 * (C + 1) ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne]
    nlinarith [hC_nonneg, hε.le]
  set drop : ℝ := (ε / 2) * δ with hdrop_def
  have hdrop_pos : 0 < drop := by
    rw [hdrop_def]
    positivity
  set η : ℝ := drop / 4 with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    positivity
  have htail_event :
      ∀ᶠ x in atBot, dist (U x) L < η :=
    Metric.tendsto_nhds.mp hlim η hη_pos
  rcases Filter.eventually_atBot.mp htail_event with ⟨A, hA⟩
  rw [Filter.eventually_atBot]
  refine ⟨A - δ, ?_⟩
  intro x hx
  rw [Real.dist_eq, sub_zero]
  have hnonpos : deriv U x ≤ 0 := hanti.deriv_nonpos
  have hgt : -ε < deriv U x := by
    by_contra hnot
    have hxder : deriv U x ≤ -ε := le_of_not_gt hnot
    have hderiv_lip : ∀ y,
        |deriv U y - deriv U x| ≤ C * |y - x| := by
      intro y
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
        (s := Set.univ) (f := deriv U) (C := C)
        (fun z _hz => hU'_diff z)
        (fun z _hz => by
          simpa [Real.norm_eq_abs] using hU''_bound z)
        convex_univ (by simp : y ∈ (Set.univ : Set ℝ))
        (by simp : x ∈ (Set.univ : Set ℝ))
      have hmv' : |deriv U x - deriv U y| ≤ C * |x - y| := by
        simpa [Real.norm_eq_abs, dist_eq_norm] using hmv
      simpa [abs_sub_comm] using hmv'
    have hderiv_le : ∀ y, x ≤ y → y ≤ x + δ → deriv U y ≤ -(ε / 2) := by
      intro y hxy hyδ
      have hyabs : |y - x| ≤ δ := by
        rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
        linarith
      have hlip := hderiv_lip y
      have hdiff_le : deriv U y - deriv U x ≤ ε / 2 := by
        have hCabs : C * |y - x| ≤ C * δ :=
          mul_le_mul_of_nonneg_left hyabs hC_nonneg
        have hle_abs : deriv U y - deriv U x ≤ |deriv U y - deriv U x| :=
          le_abs_self _
        linarith
      linarith
    have hdrop_le : U (x + δ) - U x ≤ -drop := by
      have hseg := (convex_Icc x (x + δ)).image_sub_le_mul_sub_of_deriv_le
        hU_diff.continuous.continuousOn hU_diff.differentiableOn
        (C := -(ε / 2))
        (fun y hy => by
          have hyIoo : y ∈ Ioo x (x + δ) := by
            simpa [interior_Icc] using hy
          exact hderiv_le y hyIoo.1.le hyIoo.2.le)
        x (by simp [hδ_pos.le])
        (x + δ) (by simp [hδ_pos.le])
        (by linarith : x ≤ x + δ)
      have hsub : x + δ - x = δ := by ring
      rw [hsub] at hseg
      rw [hdrop_def]
      linarith
    have habs_ge : drop ≤ |U (x + δ) - U x| := by
      have hnonpos_drop : U (x + δ) - U x ≤ 0 := by linarith [hdrop_le, hdrop_pos]
      rw [abs_of_nonpos hnonpos_drop]
      linarith
    have hxA : x ≤ A := by linarith [hx, hδ_pos.le]
    have hxδA : x + δ ≤ A := by linarith [hx]
    have hx_tail : dist (U x) L < η := hA x hxA
    have hxδ_tail : dist (U (x + δ)) L < η := hA (x + δ) hxδA
    have hx_abs : |U x - L| < η := by
      simpa [Real.dist_eq] using hx_tail
    have hxδ_abs : |U (x + δ) - L| < η := by
      simpa [Real.dist_eq] using hxδ_tail
    have habs_lt : |U (x + δ) - U x| < drop := by
      calc
        |U (x + δ) - U x|
            = |(U (x + δ) - L) + (L - U x)| := by ring_nf
        _ ≤ |U (x + δ) - L| + |L - U x| := abs_add_le _ _
        _ = |U (x + δ) - L| + |U x - L| := by rw [abs_sub_comm L (U x)]
        _ < η + η := add_lt_add hxδ_abs hx_abs
        _ < drop := by
          rw [hη_def]
          linarith [hdrop_pos]
    exact (not_lt_of_ge habs_ge habs_lt).elim
  rw [abs_lt]
  exact ⟨hgt, lt_of_le_of_lt hnonpos hε⟩

theorem frozenElliptic_tendsto_atBot_of_profile_tendsto
    (p : CMParams) {U : ℝ → ℝ} {L : ℝ}
    (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_lim : Tendsto U atBot (𝓝 L)) :
    Tendsto (frozenElliptic p U) atBot (𝓝 (L ^ p.γ)) := by
  let f : ℝ → ℝ := fun y => (U y) ^ p.γ
  have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
  have hf_lim : Tendsto (fun x => (U x) ^ p.γ) atBot (𝓝 (L ^ p.γ)) :=
    hU_lim.rpow_const (Or.inr hγ_nonneg)
  have hf_lim' : Tendsto f atBot (𝓝 (L ^ p.γ)) := by
    simpa [f] using hf_lim
  have hf_cunif : IsCUnifBdd f := by
    simpa [f] using rpow_cunif_bdd_of_nonneg p hU hU_nonneg
  rcases hU.2 with ⟨M, hM⟩
  have hγ_pos : 0 < p.γ := by linarith [p.hγ]
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (U 0)) (hM 0)
  let B : ℝ := M ^ p.γ
  have hf_bound : ∀ y, f y ≤ B := by
    intro y
    dsimp [f, B]
    exact Real.rpow_le_rpow (hU_nonneg y)
      (le_trans (le_abs_self (U y)) (hM y)) hγ_pos.le
  let F : ℝ → ℝ → ℝ := fun x z =>
    (1 / 2 : ℝ) * (Real.exp (-|z|) * f (x + z))
  let G : ℝ → ℝ := fun z =>
    (1 / 2 : ℝ) * (Real.exp (-|z|) * (L ^ p.γ))
  let bound : ℝ → ℝ := fun z =>
    (1 / 2 : ℝ) * (Real.exp (-|z|) * B)
  have hbound_int : Integrable bound := by
    have hk0 :
        Integrable (fun z : ℝ => Real.exp (-1 * |0 - z|)) :=
      _root_.kernel_exp_neg_mul_abs_integrable (by norm_num : (0 : ℝ) < 1) 0
    have hk : Integrable (fun z : ℝ => Real.exp (-|z|)) := by
      convert hk0 using 1
      ext z
      rw [zero_sub, abs_neg]
      ring_nf
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      hk.const_mul ((1 / 2 : ℝ) * B)
  have hF_meas :
      ∀ᶠ x in atBot, AEStronglyMeasurable (F x) volume := by
    refine Eventually.of_forall ?_
    intro x
    have hcont_kernel : Continuous fun z : ℝ => Real.exp (-|z|) :=
      Real.continuous_exp.comp continuous_abs.neg
    have hcont_shift : Continuous fun z : ℝ => f (x + z) :=
      hf_cunif.1.comp (continuous_const.add continuous_id)
    exact (continuous_const.mul (hcont_kernel.mul hcont_shift)).aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in atBot, ∀ᵐ z ∂volume, ‖F x z‖ ≤ bound z := by
    refine Eventually.of_forall ?_
    intro x
    refine Eventually.of_forall ?_
    intro z
    have hf_nonneg : 0 ≤ f (x + z) := by
      dsimp [f]
      exact Real.rpow_nonneg (hU_nonneg (x + z)) p.γ
    have hprod_nonneg : 0 ≤ Real.exp (-|z|) * f (x + z) :=
      mul_nonneg (Real.exp_nonneg _) hf_nonneg
    have hprod_le :
        Real.exp (-|z|) * f (x + z) ≤ Real.exp (-|z|) * B :=
      mul_le_mul_of_nonneg_left (hf_bound (x + z)) (Real.exp_nonneg _)
    dsimp [F, bound]
    rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hprod_nonneg)]
    exact mul_le_mul_of_nonneg_left hprod_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h_lim :
      ∀ᵐ z ∂volume, Tendsto (fun x => F x z) atBot (𝓝 (G z)) := by
    refine Eventually.of_forall ?_
    intro z
    have hshift : Tendsto (fun x : ℝ => x + z) atBot atBot :=
      tendsto_atBot_add_const_right atBot z tendsto_id
    have hf_shift : Tendsto (fun x : ℝ => f (x + z)) atBot (𝓝 (L ^ p.γ)) :=
      hf_lim'.comp hshift
    have hconst :
        Tendsto (fun _x : ℝ => (1 / 2 : ℝ) * Real.exp (-|z|)) atBot
          (𝓝 ((1 / 2 : ℝ) * Real.exp (-|z|))) :=
      tendsto_const_nhds
    simpa [F, G, mul_assoc] using hconst.mul hf_shift
  have hInt_tendsto :
      Tendsto (fun x => ∫ z, F x z) atBot (𝓝 (∫ z, G z)) := by
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atBot) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  have hrepr : ∀ x, frozenElliptic p U x = ∫ z, F x z := by
    intro x
    have hchange :
        (∫ y : ℝ, Real.exp (-1 * |x - y|) * f y) =
          ∫ z : ℝ, Real.exp (-|z|) * f (x + z) := by
      let g : ℝ → ℝ := fun y => Real.exp (-1 * |x - y|) * f y
      have htrans := integral_add_right_eq_self (μ := (volume : Measure ℝ)) g x
      calc
        (∫ y : ℝ, Real.exp (-1 * |x - y|) * f y) = ∫ y : ℝ, g y := rfl
        _ = ∫ z : ℝ, g (z + x) := htrans.symm
        _ = ∫ z : ℝ, Real.exp (-|z|) * f (x + z) := by
          apply integral_congr_ae
          refine Eventually.of_forall ?_
          intro z
          dsimp [g]
          rw [show x - (z + x) = -z by ring, abs_neg]
          ring_nf
    unfold frozenElliptic Psi
    simp only [Real.sqrt_one, mul_one]
    rw [hchange]
    dsimp [F]
    change (1 / 2 : ℝ) * (∫ z : ℝ, Real.exp (-|z|) * f (x + z)) =
      ∫ z : ℝ, (1 / 2 : ℝ) * (Real.exp (-|z|) * f (x + z))
    rw [MeasureTheory.integral_const_mul]
  have hG_integral : (∫ z, G z) = L ^ p.γ := by
    have hL_nonneg : 0 ≤ L := by
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hU_lim
        (Eventually.of_forall hU_nonneg)
    have hpsi := Psi_const (c := L ^ p.γ) (Real.rpow_nonneg hL_nonneg p.γ) 0
    unfold Psi at hpsi
    simp only [Real.sqrt_one, mul_one] at hpsi
    have hkernel :
        (∫ y : ℝ, Real.exp (-1 * |0 - y|) * (L ^ p.γ)) =
          ∫ z : ℝ, Real.exp (-|z|) * (L ^ p.γ) := by
      apply integral_congr_ae
      refine Eventually.of_forall ?_
      intro z
      simp only [neg_one_mul, zero_sub, abs_neg]
    dsimp [G]
    rw [MeasureTheory.integral_const_mul]
    rw [← hkernel]
    simpa using hpsi
  rw [← hG_integral]
  exact hInt_tendsto.congr' (Eventually.of_forall fun x => (hrepr x).symm)

/-- The frozen elliptic signal of a lower-pinned monotone trap profile also has
a finite left tail limit. -/
theorem inLowerPinnedMonotoneTrap_frozenElliptic_tail_atBot
    (p : CMParams) {κ M : ℝ} {φ U : ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ∃ L, Tendsto (frozenElliptic p U) atBot (𝓝 L) := by
  rcases (inLowerPinnedMonotoneTrap_profile_tail_limits hU).1 with
    ⟨LU, hUlim⟩
  exact ⟨LU ^ p.γ,
    frozenElliptic_tendsto_atBot_of_profile_tendsto p
      hU.bare.trap.cunif_bdd hU.bare.nonneg hUlim⟩

theorem frozenChemFlux_deriv_tendsto_atBot_zero_of_profile_tails
    {p : CMParams} {κ M : ℝ} {φ U : ℝ → ℝ} {L : ℝ}
    (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hUlim : Tendsto U atBot (𝓝 L))
    (hVlim : Tendsto (frozenElliptic p U) atBot (𝓝 (L ^ p.γ)))
    (hD1 : Tendsto (fun x => deriv U x) atBot (𝓝 0)) :
    Tendsto
      (fun x => deriv
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
      atBot (𝓝 0) := by
  have hbare : InMonotoneWaveTrapSet κ M U := hU.bare
  have hUcb : IsCUnifBdd U := hbare.trap.cunif_bdd
  have hUnonneg : ∀ x, 0 ≤ U x := hbare.nonneg
  have hVdiff : ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p U)) x :=
    fun x => frozenElliptic_deriv_differentiableAt p hUcb hUnonneg x
  have hVderiv_bound : ∀ x, |deriv (frozenElliptic p U) x| ≤ M ^ p.γ := by
    intro x
    calc
      |deriv (frozenElliptic p U) x| ≤ frozenElliptic p U x :=
        frozenElliptic_deriv_abs_le p hUcb hUnonneg x
      _ ≤ M ^ p.γ :=
        frozenElliptic_le_rpow_of_inWaveTrapSet p hM hbare.trap x
  have hMγ_nonneg : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM.le p.γ
  have hD1V :
      Tendsto
        (fun x => deriv U x * deriv (frozenElliptic p U) x)
        atBot (𝓝 0) :=
    tendsto_zero_mul_of_bounded_right_atBot hMγ_nonneg hVderiv_bound hD1
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hpow_m1 :
      Tendsto (fun x => (U x) ^ (p.m - 1)) atBot
        (𝓝 (L ^ (p.m - 1))) :=
    hUlim.rpow_const (Or.inr hm1_nonneg)
  have hterm1 :
      Tendsto
        (fun x =>
          deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x)
        atBot (𝓝 0) := by
    have hbase :
        Tendsto
          (fun x =>
            (deriv U x * deriv (frozenElliptic p U) x) *
              (U x) ^ (p.m - 1))
          atBot (𝓝 0) := by
      simpa using hD1V.mul hpow_m1
    have hscaled := hbase.const_mul p.m
    convert hscaled using 1
    · ext x; ring
    · ring
  have hpow_m :
      Tendsto (fun x => (U x) ^ p.m) atBot (𝓝 (L ^ p.m)) :=
    hUlim.rpow_const (Or.inr (le_trans zero_le_one p.hm))
  have hpow_γ :
      Tendsto (fun x => (U x) ^ p.γ) atBot (𝓝 (L ^ p.γ)) :=
    hUlim.rpow_const (Or.inr (le_trans zero_le_one p.hγ))
  have hdiffV :
      Tendsto
        (fun x => frozenElliptic p U x - (U x) ^ p.γ)
        atBot (𝓝 0) := by
    simpa using hVlim.sub hpow_γ
  have hterm2 :
      Tendsto
        (fun x => (U x) ^ p.m *
          (frozenElliptic p U x - (U x) ^ p.γ))
        atBot (𝓝 0) := by
    simpa using hpow_m.mul hdiffV
  have hflux_eq :
      (fun x => deriv
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
      =
      fun x =>
        deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x +
          (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ) := by
    funext x
    have hU_pow_deriv : HasDerivAt (fun y => (U y) ^ p.m)
        (deriv U x * p.m * (U x) ^ (p.m - 1)) x :=
      (hdiff.U_diff U hU x).hasDerivAt.rpow_const (Or.inr p.hm)
    have hV'' := frozenElliptic_deriv_deriv_eq p hUcb hUnonneg x
    have hV_deriv : HasDerivAt (deriv (frozenElliptic p U))
        (frozenElliptic p U x - (U x) ^ p.γ) x := by
      convert (hVdiff x).hasDerivAt using 1
      exact hV''.symm
    have hprod := hU_pow_deriv.mul hV_deriv
    have hfun_eq :
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) =
        (fun y => (U y) ^ p.m) * deriv (frozenElliptic p U) := by
      ext y
      simp [Pi.mul_apply]
    rw [hfun_eq, hprod.deriv]
  simpa [hflux_eq] using hterm1.add hterm2

theorem crossSource_tendsto_atBot_of_profile_tail_and_deriv_tail
    {p : CMParams} {lam κ M : ℝ} {φ U : ℝ → ℝ} {L : ℝ}
    (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hUlim : Tendsto U atBot (𝓝 L))
    (hD1 : Tendsto (fun x => deriv U x) atBot (𝓝 0)) :
    ∃ LR, Tendsto (crossSource p lam U U U) atBot (𝓝 LR) := by
  have hbare : InMonotoneWaveTrapSet κ M U := hU.bare
  have hVlim :
      Tendsto (frozenElliptic p U) atBot (𝓝 (L ^ p.γ)) :=
    frozenElliptic_tendsto_atBot_of_profile_tendsto p
      hbare.trap.cunif_bdd hbare.nonneg hUlim
  have hflux :
      Tendsto
        (fun x => deriv
          (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
        atBot (𝓝 0) :=
    frozenChemFlux_deriv_tendsto_atBot_zero_of_profile_tails
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) (L := L)
      hM hU hdiff hUlim hVlim hD1
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hpow :
      Tendsto (fun x => (U x) ^ p.α) atBot (𝓝 (L ^ p.α)) :=
    hUlim.rpow_const (Or.inr hα_nonneg)
  have hreact :
      Tendsto (fun x => reactionFun p.α (U x)) atBot
        (𝓝 (reactionFun p.α L)) := by
    unfold reactionFun
    exact hUlim.mul (tendsto_const_nhds.sub hpow)
  refine ⟨reactionFun p.α L + lam * L, ?_⟩
  have hmain :
      Tendsto
        (fun x =>
          reactionFun p.α (U x) + lam * U x
            - p.χ *
              deriv
                (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
        atBot (𝓝 (reactionFun p.α L + lam * L)) := by
    have hflux_scaled :
        Tendsto
          (fun x =>
            p.χ *
              deriv
                (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
          atBot (𝓝 0) := by
      simpa using hflux.const_mul p.χ
    simpa using (hreact.add (hUlim.const_mul lam)).sub hflux_scaled
  simpa [crossSource] using hmain

theorem lowerPinned_crossSource_tendsto_atBot_of_c3
    {p : CMParams} {lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ) :
    ∃ LR, Tendsto (crossSource p lam U U U) atBot (𝓝 LR) := by
  rcases (inLowerPinnedMonotoneTrap_profile_tail_limits hU).1 with
    ⟨LU, hUlim⟩
  have hU_diff : Differentiable ℝ U := fun x =>
    (hc3.limit_hasDeriv_value x).differentiableAt
  have hU'_diff : Differentiable ℝ (deriv U) := fun x =>
    (hc3.limit_hasDeriv_deriv x).differentiableAt
  obtain ⟨C2, hC2_nonneg, hC2⟩ := hc3.limit_second_bound
  have hsecond_bound : ∀ x, |deriv (deriv U) x| ≤ C2 := by
    intro x
    rw [(hc3.limit_hasDeriv_deriv x).deriv]
    exact hC2 x
  have hD1 :
      Tendsto (fun x => deriv U x) atBot (𝓝 0) :=
    antitone_deriv_tendsto_atBot_zero_of_tail_of_second_bound
      hU.bare.antitone hUlim hU_diff hU'_diff hC2_nonneg hsecond_bound
  exact crossSource_tendsto_atBot_of_profile_tail_and_deriv_tail
    (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ) (U := U)
    (L := LU) hM hU hdiff hUlim hD1

theorem lowerPinned_crossSource_continuous_of_c3
    {p : CMParams} {lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z) :
    Continuous (crossSource p lam U U U) := by
  have hU_cont : Continuous U :=
    continuous_iff_continuousAt.2 fun x =>
      (hc3.limit_hasDeriv_value x).continuousAt
  have hDU_cont : Continuous (fun x => deriv U x) :=
    continuous_iff_continuousAt.2 fun x =>
      (hc3.limit_hasDeriv_deriv x).continuousAt
  have hV_cont : Continuous (frozenElliptic p U) :=
    frozenElliptic_continuous p hU.bare.trap.cunif_bdd hU.bare.nonneg
  have hDV_cont : Continuous (fun x => deriv (frozenElliptic p U) x) :=
    continuous_iff_continuousAt.2 fun x =>
      (frozenElliptic_deriv_differentiableAt p
        hU.bare.trap.cunif_bdd hU.bare.nonneg x).continuousAt
  have hflux_eq :
      (fun x => deriv
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
      =
      fun x =>
        deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x +
          (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ) := by
    funext x
    have hU_pow_deriv : HasDerivAt (fun y => (U y) ^ p.m)
        (deriv U x * p.m * (U x) ^ (p.m - 1)) x :=
      (hc3.limit_hasDeriv_value x).rpow_const (Or.inr p.hm)
    have hV'' := frozenElliptic_deriv_deriv_eq p
      hU.bare.trap.cunif_bdd hU.bare.nonneg x
    have hV_deriv : HasDerivAt (deriv (frozenElliptic p U))
        (frozenElliptic p U x - (U x) ^ p.γ) x := by
      convert (frozenElliptic_deriv_differentiableAt p
        hU.bare.trap.cunif_bdd hU.bare.nonneg x).hasDerivAt using 1
      exact hV''.symm
    have hprod := hU_pow_deriv.mul hV_deriv
    have hfun_eq :
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) =
        (fun y => (U y) ^ p.m) * deriv (frozenElliptic p U) := by
      ext y
      simp [Pi.mul_apply]
    rw [hfun_eq, hprod.deriv]
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ_nonneg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hflux_cont :
      Continuous
        (fun x =>
          deriv
            (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x) := by
    have hterm1 :
        Continuous
          (fun x =>
            deriv U x * p.m * (U x) ^ (p.m - 1) *
              deriv (frozenElliptic p U) x) :=
      (((hDU_cont.mul continuous_const).mul
        ((Real.continuous_rpow_const hm1_nonneg).comp hU_cont)).mul hDV_cont)
    have hterm2 :
        Continuous
          (fun x => (U x) ^ p.m *
            (frozenElliptic p U x - (U x) ^ p.γ)) :=
      ((Real.continuous_rpow_const hm_nonneg).comp hU_cont).mul
        (hV_cont.sub ((Real.continuous_rpow_const hγ_nonneg).comp hU_cont))
    simpa [hflux_eq] using hterm1.add hterm2
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  simpa [crossSource] using
    ((continuous_reactionFun hα_nonneg).comp hU_cont).add
      (continuous_const.mul hU_cont) |>.sub
        (continuous_const.mul hflux_cont)

theorem lowerPinnedStationaryGreenSourceTail_of_frozenWaveOperator_zero_from_c3
    {p : CMParams} {c lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hdata : StationaryCrossGreenData p c lam U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    FrozenStationaryGreenSourceTail c lam U := by
  have hR_cont : Continuous (crossSource p lam U U U) :=
    lowerPinned_crossSource_continuous_of_c3
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ)
      (U := U) (z := z) hU hc3
  have hR_tail :
      ∃ L : ℝ, Tendsto (crossSource p lam U U U) atBot (𝓝 L) :=
    lowerPinned_crossSource_tendsto_atBot_of_c3
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ) (U := U)
      (z := z) hM hU hc3 hdiff
  have hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B := by
    obtain ⟨C1, _hC1_nonneg, hC1⟩ := hc3.limit_deriv_bound
    obtain ⟨C2, _hC2_nonneg, hC2⟩ := hc3.limit_second_bound
    refine ⟨|lam| * M + (C2 + |c| * C1), ?_⟩
    intro y
    have hU_abs : |U y| ≤ M := by
      rw [abs_of_nonneg (hU.bare.nonneg y)]
      exact hU.bare.le_M y
    have hsrc := crossSource_eq_linear_of_frozenWaveOperator_zero
      p c lam U hstat y
    rw [hsrc]
    have hlamU : |lam * U y| ≤ |lam| * M := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hU_abs (abs_nonneg lam)
    have hcDU : |c * deriv U y| ≤ |c| * C1 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC1 y) (abs_nonneg c)
    have hlin :
        |iteratedDeriv 2 U y + c * deriv U y| ≤ C2 + |c| * C1 := by
      calc
        |iteratedDeriv 2 U y + c * deriv U y|
            ≤ |iteratedDeriv 2 U y| + |c * deriv U y| := abs_add_le _ _
        _ ≤ C2 + |c| * C1 := add_le_add (hC2 y) hcDU
    calc
      |lam * U y - (iteratedDeriv 2 U y + c * deriv U y)|
          ≤ |lam * U y| + |iteratedDeriv 2 U y + c * deriv U y| := abs_sub _ _
      _ ≤ |lam| * M + (C2 + |c| * C1) := add_le_add hlamU hlin
  have hU_diff : Differentiable ℝ U := fun x =>
    (hc3.limit_hasDeriv_value x).differentiableAt
  have hU'_diff : Differentiable ℝ (deriv U) := fun x =>
    (hc3.limit_hasDeriv_deriv x).differentiableAt
  have hU_bdd : ∃ C : ℝ, ∀ x, |U x| ≤ C := by
    refine ⟨M, ?_⟩
    intro x
    rw [abs_of_nonneg (hU.bare.nonneg x)]
    exact hU.bare.le_M x
  obtain ⟨CU', _hCU'_nonneg, hCU'⟩ := hc3.limit_deriv_bound
  have hU'_bdd : ∃ C : ℝ, ∀ x, |deriv U x| ≤ C := ⟨CU', hCU'⟩
  exact frozenStationaryGreenSourceTail_of_frozenWaveOperator_zero
    (p := p) (c := c) (lam := lam) (U := U)
    hlam hdata hR_cont hR_bound hR_tail
    hU_diff hU'_diff hU_bdd hU'_bdd hstat

theorem frozenStationaryFlatAtLeft_of_green_source_tail
    {p : CMParams} {c lam κ M : ℝ} {φ U : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hsource : FrozenStationaryGreenSourceTail c lam U) :
    FrozenStationaryFlatAtLeft p U := by
  rcases hsource with ⟨R, B, LR, hRcont, hRbound, hRlim, hgreen⟩
  rcases greenConv_profile_deriv_tails_atBot_of_source_tendsto
      (c := c) (lam := lam) hlam hRcont hRbound hRlim hgreen with
    ⟨hD1, hD2⟩
  have hbare : InMonotoneWaveTrapSet κ M U := hU.bare
  have hUlim_green :
      Tendsto (greenConv c lam R) atBot (𝓝 (LR * lam⁻¹)) :=
    greenConv_tendsto_atBot_of_source_tendsto
      (c := c) (lam := lam) hlam hRcont hRbound hRlim
  have hUlim : Tendsto U atBot (𝓝 (LR * lam⁻¹)) := by
    simpa [hgreen] using hUlim_green
  have hVlim :
      Tendsto (frozenElliptic p U) atBot (𝓝 ((LR * lam⁻¹) ^ p.γ)) :=
    frozenElliptic_tendsto_atBot_of_profile_tendsto p
      hbare.trap.cunif_bdd hbare.nonneg hUlim
  exact
    ⟨hD2, hD1,
      frozenChemFlux_deriv_tendsto_atBot_zero_of_profile_tails
        (p := p) (κ := κ) (M := M) (φ := φ) (U := U)
        (L := LR * lam⁻¹)
        hM hU hdiff hUlim hVlim hD1⟩

theorem paperLowerPinnedStationaryFlatFloor_of_fixedStepIdentity
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hfixed : PaperRotheLimitFixedStepIdentity p c lam κ M φ rotheSeq)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hflat : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    PaperLowerPinnedStationaryFlatFloor p c κ M φ rotheSeq where
  stationary := paperLowerPinnedStationary_of_fixedStepIdentity
    hlam hfixed hdiff
  flat := hflat

theorem paperLowerPinnedStationary_of_termConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hterms :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperWaveOperatorTermConvergence p c U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 := by
  have hpass : PaperRotheStepLimitPassage p c lam κ M φ rotheSeq :=
    paperRotheStepLimitPassage_of_termConvergence hterms
  have hfixed : PaperRotheLimitFixedStepIdentity p c lam κ M φ rotheSeq :=
    paperRotheLimitFixedStepIdentity_of_stepLimitPassage hLU hstep hpass
  exact paperLowerPinnedStationary_of_fixedStepIdentity hlam hfixed hdiff

theorem paperLowerPinnedStationary_of_c2CompactConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hc2 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactConvergence p U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 :=
  paperLowerPinnedStationary_of_termConvergence hlam hLU hstep
    (fun U hU hLU_U => (hc2 U hU hLU_U).termConvergence) hdiff

theorem paperLowerPinnedStationary_of_uniformBounds
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hbounds :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactUniformBounds p U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 :=
  paperLowerPinnedStationary_of_c2CompactConvergence hlam hLU hstep
    (fun U hU hLU_U =>
      paperC2CompactConvergence_of_uniformBounds hLU_U (hbounds U hU hLU_U))
    hdiff

theorem paperLowerPinnedStationary_of_greenStep
    {p : CMParams} {c lam κ M Λ : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hz_nonneg :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k x, 0 ≤ rotheSeq U k x)
    (hz_le_M :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k x, rotheSeq U k x ≤ M)
    (hgreen :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, PaperStepAnalytic p c lam M κ Λ U
          (rotheSeq U k) (rotheSeq U (k + 1)))
    (hc3 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        PaperC3BootstrapData U (rotheSeq U)) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 :=
  paperLowerPinnedStationary_of_uniformBounds
    (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (φ := φ)
    (rotheSeq := rotheSeq) hlam hLU hstep
    (fun U hU hLU_U =>
      paperC2CompactUniformBounds_of_greenStep
        (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (Λ := Λ)
        (φ := φ) (U := U) (z := rotheSeq U)
        hlam hM hΛ hU hLU_U (hz_nonneg U hU) (hz_le_M U hU)
        (hgreen U hU) (hc3 U hU))
    (paperDiagonalDifferentiabilityFloor_of_c3BootstrapData
      (p := p) (κ := κ) (M := M) (φ := φ) (rotheSeq := rotheSeq) hc3)

theorem paperLowerPinnedStationaryFlatFloor_of_termConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hterms :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperWaveOperatorTermConvergence p c U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hflat : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    PaperLowerPinnedStationaryFlatFloor p c κ M φ rotheSeq where
  stationary := paperLowerPinnedStationary_of_termConvergence
    hlam hLU hstep hterms hdiff
  flat := hflat

theorem paperLowerPinnedStationaryFlatFloor_of_c2CompactConvergence
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hc2 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactConvergence p U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hflat : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    PaperLowerPinnedStationaryFlatFloor p c κ M φ rotheSeq :=
  paperLowerPinnedStationaryFlatFloor_of_termConvergence hlam hLU hstep
    (fun U hU hLU_U => (hc2 U hU hLU_U).termConvergence) hdiff hflat

theorem paperLowerPinnedStationaryFlatFloor_of_uniformBounds
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hbounds :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) U →
          PaperC2CompactUniformBounds p U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hflat : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    PaperLowerPinnedStationaryFlatFloor p c κ M φ rotheSeq :=
  paperLowerPinnedStationaryFlatFloor_of_c2CompactConvergence hlam hLU hstep
    (fun U hU hLU_U =>
      paperC2CompactConvergence_of_uniformBounds hLU_U (hbounds U hU hLU_U))
    hdiff hflat

theorem paperLowerPinnedStationaryFlatFloor_of_greenStep
    {p : CMParams} {c lam κ M Λ : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)))
    (hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (rotheSeq U (k + 1)) =
          rotheSeq U k)
    (hz_nonneg :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k x, 0 ≤ rotheSeq U k x)
    (hz_le_M :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k x, rotheSeq U k x ≤ M)
    (hgreen :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, PaperStepAnalytic p c lam M κ Λ U
          (rotheSeq U k) (rotheSeq U (k + 1)))
    (hc3 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        PaperC3BootstrapData U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ)
    (hdata : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      StationaryCrossGreenData p c lam U) :
    PaperLowerPinnedStationaryFlatFloor p c κ M φ rotheSeq :=
  paperLowerPinnedStationaryFlatFloor_of_uniformBounds
    (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (φ := φ)
    (rotheSeq := rotheSeq) hlam hLU hstep
    (fun U hU hLU_U =>
      paperC2CompactUniformBounds_of_greenStep
        (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (Λ := Λ)
        (φ := φ) (U := U) (z := rotheSeq U)
        hlam hM hΛ hU hLU_U (hz_nonneg U hU) (hz_le_M U hU)
        (hgreen U hU) (hc3 U hU))
    hdiff
    (fun U hU hstat =>
      frozenStationaryFlatAtLeft_of_green_source_tail
        (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (φ := φ)
        (U := U) hlam hM hU hdiff
        (lowerPinnedStationaryGreenSourceTail_of_frozenWaveOperator_zero_from_c3
          (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
          (φ := φ) (U := U) (z := rotheSeq U)
          hlam hM hU (hc3 U hU) hdiff (hdata U hU)
          hstat))

#print axioms paperImplicitStep_fixed_paperWaveOperator_zero
#print axioms paperImplicitStep_fixed_frozenWaveOperator_zero
#print axioms paperDiagonalDifferentiabilityFloor_of_c3BootstrapData
#print axioms paperLimit_fixedStepIdentity_of_stepLimitPassage
#print axioms paperRotheLimitFixedStepIdentity_of_stepLimitPassage
#print axioms PaperWaveOperatorTermConvergence.implicitStepLimitPassage
#print axioms paperRotheStepLimitPassage_of_termConvergence
#print axioms paperRotheStepLimitPassage_of_c2CompactConvergence
#print axioms paperRotheLimitStepConsistency_of_termConvergence
#print axioms paperRotheLimitStepConsistency_of_c2CompactConvergence
#print axioms paperLowerPinnedStationary_of_fixedStepIdentity
#print axioms paperLowerPinnedStationaryFlatFloor_of_fixedStepIdentity
#print axioms paperLowerPinnedStationary_of_termConvergence
#print axioms paperLowerPinnedStationary_of_c2CompactConvergence
#print axioms paperLowerPinnedStationaryFlatFloor_of_termConvergence
#print axioms paperLowerPinnedStationaryFlatFloor_of_c2CompactConvergence
#print axioms paperC2CompactConvergence_of_uniformBounds
#print axioms paperRotheStepLimitPassage_of_uniformBounds
#print axioms paperRotheLimitStepConsistency_of_uniformBounds
#print axioms paperLowerPinnedStationary_of_uniformBounds
#print axioms paperLowerPinnedStationary_of_greenStep
#print axioms paperLowerPinnedStationaryFlatFloor_of_uniformBounds
#print axioms paperLowerPinnedStationaryFlatFloor_of_greenStep

end

end ShenWork.Paper1
