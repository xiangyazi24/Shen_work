import ShenWork.Paper1.WavePaperTermConvergence
import ShenWork.Paper1.WaveTrapProps
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

/-- A `C²` compact convergence certificate gives `C²` regularity of its limit by
passing derivatives through locally uniform convergence.  This is the vertical
Rothe-limit route, not the stationary limit's own Green representation. -/
theorem stationaryC2Regularity_of_c2CompactConvergence
    {p : CMParams} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hc2 : PaperC2CompactConvergence p U z) :
    Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  have hU_deriv : ∀ x, HasDerivAt U (deriv U x) x := by
    intro x
    have hderiv :
        TendstoLocallyUniformlyOn
          (fun k x => deriv (z (k + 1)) x)
          (fun x => deriv U x) atTop (Set.univ : Set ℝ) :=
      hc2.deriv1.tendstoLocallyUniformlyOn_univ
    have hstep :
        ∀ᶠ k : ℕ in atTop,
          ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
            HasDerivAt (z (k + 1)) (deriv (z (k + 1)) y) y := by
      exact Eventually.of_forall fun k y _hy => hc2.step_hasDeriv_value k y
    have hpoint :
        ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
          Tendsto (fun k : ℕ => z (k + 1) y) atTop (𝓝 (U y)) := by
      intro y _hy
      exact hc2.value.tendsto_at y
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := fun k : ℕ => z (k + 1)) (g := U)
      (f' := fun k x => deriv (z (k + 1)) x)
      (g' := fun x => deriv U x) isOpen_univ hderiv hstep hpoint
      (Set.mem_univ x)
  have hderivU_deriv :
      ∀ x, HasDerivAt (fun y => deriv U y) (iteratedDeriv 2 U x) x := by
    intro x
    have hderiv2 :
        TendstoLocallyUniformlyOn
          (fun k x => iteratedDeriv 2 (z (k + 1)) x)
          (fun x => iteratedDeriv 2 U x) atTop (Set.univ : Set ℝ) :=
      hc2.deriv2.tendstoLocallyUniformlyOn_univ
    have hstep :
        ∀ᶠ k : ℕ in atTop,
          ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
            HasDerivAt (fun t => deriv (z (k + 1)) t)
              (iteratedDeriv 2 (z (k + 1)) y) y := by
      exact Eventually.of_forall fun k y _hy => hc2.step_hasDeriv_deriv k y
    have hpoint :
        ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
          Tendsto (fun k : ℕ => deriv (z (k + 1)) y) atTop
            (𝓝 (deriv U y)) := by
      intro y _hy
      exact hc2.deriv1.tendsto_at y
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := fun k : ℕ => fun y => deriv (z (k + 1)) y)
      (g := fun y => deriv U y)
      (f' := fun k x => iteratedDeriv 2 (z (k + 1)) x)
      (g' := fun x => iteratedDeriv 2 U x) isOpen_univ hderiv2 hstep
      hpoint (Set.mem_univ x)
  exact ⟨fun x => (hU_deriv x).differentiableAt,
    fun x => (hderivU_deriv x).differentiableAt⟩

/-- Discharge the stationary `C²` regularity frontier from a profile-wise
`C²` compact convergence floor for the Rothe iterates. -/
theorem stationaryC2RegularityFromEquation_of_c2CompactConvergence
    {p : CMParams} {c κ M : ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hc2 :
      ∀ U, InMonotoneWaveTrapSet κ M U →
        (∀ x, frozenWaveOperator p c U U x = 0) →
          PaperC2CompactConvergence p U (rotheSeq U)) :
    StationaryC2RegularityFromEquation p c κ M := by
  intro U hU hstat
  exact stationaryC2Regularity_of_c2CompactConvergence (hc2 U hU hstat)

/-- The same regularity frontier when the compact convergence certificate is
produced from uniform Green/ODE bounds. -/
theorem stationaryC2RegularityFromEquation_of_c2CompactUniformBounds
    {p : CMParams} {c κ M : ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hLU :
      ∀ U, InMonotoneWaveTrapSet κ M U →
        (∀ x, frozenWaveOperator p c U U x = 0) →
          LocallyUniformConverges (rotheSeq U) U)
    (hbounds :
      ∀ U, InMonotoneWaveTrapSet κ M U →
        (∀ x, frozenWaveOperator p c U U x = 0) →
          PaperC2CompactUniformBounds p U (rotheSeq U)) :
    StationaryC2RegularityFromEquation p c κ M :=
  stationaryC2RegularityFromEquation_of_c2CompactConvergence
    (fun U hU hstat =>
      paperC2CompactConvergence_of_uniformBounds
        (hLU U hU hstat) (hbounds U hU hstat))

/-- Strong maximum principle closed from the vertical `C²` compact convergence
floor, avoiding the stationary profile's self-Green representation and the
traveling-wave ODE route. -/
theorem stationaryStrongMaxPrinciple_of_c2CompactConvergence
    {p : CMParams} {c κ M : ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hM : 0 < M)
    (hc2 :
      ∀ U, InMonotoneWaveTrapSet κ M U →
        (∀ x, frozenWaveOperator p c U U x = 0) →
          PaperC2CompactConvergence p U (rotheSeq U)) :
    StationaryStrongMaxPrinciple p c κ M :=
  stationaryStrongMaxPrinciple_of_trap_regularity hM
    (stationaryC2RegularityFromEquation_of_c2CompactConvergence hc2)

theorem stationaryStrongMaxPrinciple_of_c2CompactUniformBounds
    {p : CMParams} {c κ M : ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hM : 0 < M)
    (hLU :
      ∀ U, InMonotoneWaveTrapSet κ M U →
        (∀ x, frozenWaveOperator p c U U x = 0) →
          LocallyUniformConverges (rotheSeq U) U)
    (hbounds :
      ∀ U, InMonotoneWaveTrapSet κ M U →
        (∀ x, frozenWaveOperator p c U U x = 0) →
          PaperC2CompactUniformBounds p U (rotheSeq U)) :
    StationaryStrongMaxPrinciple p c κ M :=
  stationaryStrongMaxPrinciple_of_trap_regularity hM
    (stationaryC2RegularityFromEquation_of_c2CompactUniformBounds hLU hbounds)

/-- Construction-site data for threading the stationary Green representation
from a Rothe orbit: the shifted iterates are Green convolutions of sources
`Rseq k`, the sources converge to the stationary diagonal cross source, and the
stationary cross-map Green bookkeeping is available. -/
structure StationaryGreenRepresentationThreadData
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (z Rseq : ℕ → ℝ → ℝ) : Prop where
  cross_data : StationaryCrossGreenData p c lam U
  step_green : ∀ k, z (k + 1) = fun x => greenConv c lam (Rseq k) x
  source_cont : ∀ k, Continuous (Rseq k)
  source_limit_cont : Continuous (crossSource p lam U U U)
  source_bound : ∃ B : ℝ,
    (∀ k y, |Rseq k y| ≤ B) ∧
      ∀ y, |crossSource p lam U U U y| ≤ B
  source_limit : LocallyUniformConverges Rseq (crossSource p lam U U U)

/-- Build the Green-thread data from the actual per-step analytic package and
`C²` compact convergence of the Rothe iterates.  The source convergence is the
expanded paper source convergence, transported across
`paperStepSource_self_eq_crossSource` on the diagonal. -/
theorem stationaryGreenRepresentationThreadData_of_c2_greenStep
    {p : CMParams} {c lam κ M Λ : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hLU : LocallyUniformConverges z U)
    (hstep : ∀ k, PaperStepAnalytic p c lam M κ Λ U (z k) (z (k + 1)))
    (hc2 : PaperC2CompactConvergence p U z)
    (hcross : StationaryCrossGreenData p c lam U)
    (hR_cont : Continuous (crossSource p lam U U U))
    (hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B) :
    StationaryGreenRepresentationThreadData p c lam U z
      (fun k => (hstep k).R) := by
  obtain ⟨BR, hBR⟩ := hR_bound
  have hdiag :
      paperStepSource p c lam U U U = crossSource p lam U U U :=
    paperStepSource_self_eq_crossSource
      (p := p) (c := c) (lam := lam) (U := U)
      hU.trap.cunif_bdd hU.nonneg hc2.limit_hasDeriv_value
  have hsource_paper :
      LocallyUniformConverges
        (fun k => paperStepSource p c lam U (z k) (z (k + 1)))
        (crossSource p lam U U U) := by
    simpa [hdiag] using
      hc2.paperStepSource_locallyUniform (c := c) (lam := lam) hLU
  have hsource_eq :
      ∀ᶠ k : ℕ in atTop,
        paperStepSource p c lam U (z k) (z (k + 1)) = (hstep k).R :=
    Eventually.of_forall fun k => (hstep k).source_eq.symm
  refine
    { cross_data := hcross
      step_green := ?_
      source_cont := ?_
      source_limit_cont := hR_cont
      source_bound := ?_
      source_limit := ?_ }
  · intro k
    exact (hstep k).green_repr
  · intro k
    exact (hstep k).R_cont
  · refine ⟨max (paperStepRBoundFromLambda c lam Λ) BR, ?_, ?_⟩
    · intro k y
      exact le_trans
        (paperStep_R_abs_le_from_lambda
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
          hlam (hstep k) y)
        (le_max_left _ _)
    · intro y
      exact le_trans (hBR y) (le_max_right _ _)
  · exact LocallyUniformConverges.congr hsource_eq hsource_paper

/-- Build the Green-thread data directly from the per-step Green package and
the independently threaded source convergence.  This is the non-circular route:
`R_k -> crossSource` is an input, not recovered from `C²` term convergence. -/
theorem stationaryGreenRepresentationThreadData_of_greenStep
    {p : CMParams} {c lam κ M Λ : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hstep : ∀ k, PaperStepAnalytic p c lam M κ Λ U (z k) (z (k + 1)))
    (hcross : StationaryCrossGreenData p c lam U)
    (hR_cont : Continuous (crossSource p lam U U U))
    (hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B)
    (hR_limit :
      LocallyUniformConverges (fun k => (hstep k).R)
        (crossSource p lam U U U)) :
    StationaryGreenRepresentationThreadData p c lam U z
      (fun k => (hstep k).R) := by
  obtain ⟨BR, hBR⟩ := hR_bound
  refine
    { cross_data := hcross
      step_green := ?_
      source_cont := ?_
      source_limit_cont := hR_cont
      source_bound := ?_
      source_limit := hR_limit }
  · intro k
    exact (hstep k).green_repr
  · intro k
    exact (hstep k).R_cont
  · refine ⟨max (paperStepRBoundFromLambda c lam Λ) BR, ?_, ?_⟩
    · intro k y
      exact le_trans
        (paperStep_R_abs_le_from_lambda
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
          hlam (hstep k) y)
        (le_max_left _ _)
    · intro y
      exact le_trans (hBR y) (le_max_right _ _)

theorem paperC2CompactUniformBounds_of_greenStep_thread
    {p : CMParams} {c lam κ M Λ : ℝ} {φ U : ℝ → ℝ}
    {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hLU : LocallyUniformConverges z U)
    (hz_nonneg : ∀ k x, 0 ≤ z k x)
    (hz_le_M : ∀ k x, z k x ≤ M)
    (hstep :
      ∀ k, PaperStepAnalytic p c lam M κ Λ U (z k) (z (k + 1)))
    (hthread :
      StationaryGreenRepresentationThreadData p c lam U z
        (fun k => (hstep k).R)) :
    PaperC2CompactUniformBounds p U z :=
  paperC2CompactUniformBounds_of_greenStep
    (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (Λ := Λ)
    (φ := φ) (U := U) (z := z) (R := crossSource p lam U U U)
    hlam hM hΛ hU hLU hz_nonneg hz_le_M hstep
    hthread.source_limit_cont hthread.source_bound hthread.source_limit

/-- Single-profile Rothe-limit threading of the stationary Green
representation.  The proof uses the per-step Green representations and DCT
continuity of `greenConv`; it does not invert the stationary differential
equation for an abstract `U`. -/
theorem stationaryGreenRepresentation_profile_of_rotheLimit
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ} {z Rseq : ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hlim : rotheLimit z = U)
    (hLU : LocallyUniformConverges z (rotheLimit z))
    (hthread : StationaryGreenRepresentationThreadData p c lam U z Rseq) :
    StationaryCrossGreenData p c lam U ∧
      Continuous (crossSource p lam U U U) ∧
      (∀ x,
        IntegrableOn
          (gWeight (greenRootPlus c lam) (crossSource p lam U U U))
          (Ioi x)) ∧
      (∀ x,
        IntegrableOn
          (gWeight (greenRootMinus c lam) (crossSource p lam U U U))
          (Iic x)) ∧
      crossImplicitMap p c lam U U U = U := by
  let R : ℝ → ℝ := crossSource p lam U U U
  obtain ⟨B, hBseq, hBR⟩ := hthread.source_bound
  have hR_cont : Continuous R := by
    simpa [R] using hthread.source_limit_cont
  have hR_bound : ∀ y, |R y| ≤ B := by
    simpa [R] using hBR
  have hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR_cont hR_bound x
  have hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR_cont hR_bound x
  have hLU_U : LocallyUniformConverges z U := by
    simpa [hlim] using hLU
  have hLU_shift : LocallyUniformConverges (fun k => z (k + 1)) U :=
    hLU_U.comp_strictMono
      (strictMono_nat_of_lt_succ fun n => Nat.lt_succ_self (n + 1))
  have hU_green : U = fun x => greenConv c lam R x := by
    funext x
    have hz_tendsto :
        Tendsto (fun k : ℕ => z (k + 1) x) atTop (𝓝 (U x)) :=
      hLU_shift.tendsto_at x
    have hgreen_tendsto :
        Tendsto (fun k : ℕ => greenConv c lam (Rseq k) x) atTop
          (𝓝 (greenConv c lam R x)) :=
      greenConv_tendsto_of_source_locallyUniform_of_uniform_bound
        (c := c) (lam := lam) hlam
        (R := R) (B := B)
        hthread.source_cont hR_cont hBseq hR_bound
        (by simpa [R] using hthread.source_limit) x
    have hsame :
        (fun k : ℕ => z (k + 1) x)
          = fun k : ℕ => greenConv c lam (Rseq k) x := by
      funext k
      exact congrFun (hthread.step_green k) x
    have hz_green_tendsto :
        Tendsto (fun k : ℕ => z (k + 1) x) atTop
          (𝓝 (greenConv c lam R x)) := by
      simpa [hsame] using hgreen_tendsto
    exact tendsto_nhds_unique hz_tendsto hz_green_tendsto
  have hcross_green :
      crossImplicitMap p c lam U U U = fun x => greenConv c lam R x := by
    simpa [R] using
      StationaryCrossGreenData.crossImplicitMap_eq_greenConv_crossSource
        (p := p) (c := c) (lam := lam) (U := U) hlam hthread.cross_data
  have hcross : crossImplicitMap p c lam U U U = U := by
    calc
      crossImplicitMap p c lam U U U = fun x => greenConv c lam R x := hcross_green
      _ = U := hU_green.symm
  exact ⟨hthread.cross_data, by simpa [R] using hR_cont,
    by simpa [R] using hRhi, by simpa [R] using hRlo, hcross⟩

/-- Profile-wise construction data sufficient to discharge
`StationaryGreenRepresentationFromEquation`: every stationary trapped profile
is the locally uniform Rothe limit of its construction orbit, and that orbit
carries the per-step Green-source thread. -/
def StationaryGreenRepresentationFromRotheLimitData
    (p : CMParams) (c lam κ M : ℝ)
    (rotheSeq Rseq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ U, InMonotoneWaveTrapSet κ M U →
    (∀ x, frozenWaveOperator p c U U x = 0) →
      rotheLimit (rotheSeq U) = U ∧
        LocallyUniformConverges (rotheSeq U) (rotheLimit (rotheSeq U)) ∧
        StationaryGreenRepresentationThreadData p c lam U (rotheSeq U) (Rseq U)

theorem stationaryGreenRepresentationFromEquation_of_rotheLimit
    {p : CMParams} {c lam κ M : ℝ}
    {rotheSeq Rseq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hthread :
      StationaryGreenRepresentationFromRotheLimitData
        p c lam κ M rotheSeq Rseq) :
    StationaryGreenRepresentationFromEquation p c lam κ M := by
  intro U hU hstat
  rcases hthread U hU hstat with ⟨hlim, hLU, hdata⟩
  exact stationaryGreenRepresentation_profile_of_rotheLimit
    (p := p) (c := c) (lam := lam) (U := U)
    (z := rotheSeq U) (Rseq := Rseq U) hlam hlim hLU hdata

theorem stationaryStrongMaxPrinciple_of_rotheLimit_greenRepresentation
    {p : CMParams} {c lam κ M : ℝ}
    {rotheSeq Rseq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hM : 0 < M) (hlam : 0 < lam)
    (hthread :
      StationaryGreenRepresentationFromRotheLimitData
        p c lam κ M rotheSeq Rseq) :
    StationaryStrongMaxPrinciple p c κ M :=
  stationaryStrongMaxPrinciple_of_trap hM hlam
    (stationaryGreenRepresentationFromEquation_of_rotheLimit
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
      (rotheSeq := rotheSeq) (Rseq := Rseq) hlam hthread)

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

theorem paperRotheLimitFixedStepIdentity_of_stepConsistency
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hcons : PaperRotheLimitStepConsistency p c lam κ M φ rotheSeq) :
    PaperRotheLimitFixedStepIdentity p c lam κ M φ rotheSeq := by
  intro U hU hlim
  exact funext (hcons U hU hlim)

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

theorem paperLowerPinnedStationary_of_stepConsistency
    {p : CMParams} {c lam κ M : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hlam : 0 < lam)
    (hcons : PaperRotheLimitStepConsistency p c lam κ M φ rotheSeq)
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 :=
  paperLowerPinnedStationary_of_fixedStepIdentity hlam
    (paperRotheLimitFixedStepIdentity_of_stepConsistency hcons) hdiff

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
      have hsub : x + δ - x = δ := by ring_nf
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
          rw [show x - (z + x) = -z by ring_nf, abs_neg]
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
    {p : CMParams} {κ M : ℝ} {U : ℝ → ℝ} {L : ℝ}
    (hM : 0 < M)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hU_diff : Differentiable ℝ U)
    (hUlim : Tendsto U atBot (𝓝 L))
    (hVlim : Tendsto (frozenElliptic p U) atBot (𝓝 (L ^ p.γ)))
    (hD1 : Tendsto (fun x => deriv U x) atBot (𝓝 0)) :
    Tendsto
      (fun x => deriv
        (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x)
      atBot (𝓝 0) := by
  have hbare : InMonotoneWaveTrapSet κ M U := hU
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
    · ext x; ring_nf
    · ring_nf
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
      (hU_diff x).hasDerivAt.rpow_const (Or.inr p.hm)
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
    {p : CMParams} {lam κ M : ℝ} {U : ℝ → ℝ} {L : ℝ}
    (hM : 0 < M)
    (hU : InMonotoneWaveTrapSet κ M U)
    (hU_diff : Differentiable ℝ U)
    (hUlim : Tendsto U atBot (𝓝 L))
    (hD1 : Tendsto (fun x => deriv U x) atBot (𝓝 0)) :
    ∃ LR, Tendsto (crossSource p lam U U U) atBot (𝓝 LR) := by
  have hbare : InMonotoneWaveTrapSet κ M U := hU
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
      (p := p) (κ := κ) (M := M) (U := U) (L := L)
      hM hU hU_diff hUlim hVlim hD1
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
    (hc3 : PaperC3BootstrapData U z) :
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
    (p := p) (lam := lam) (κ := κ) (M := M) (U := U)
    (L := LU) hM hU.bare hU_diff hUlim hD1

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

/-- The non-flux source part `reaction(U)+λU` is continuous for a C³ trapped
stationary profile. -/
theorem lowerPinned_source0_continuous_of_c3
    {p : CMParams} {lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (_hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z) :
    Continuous (fun y => reactionFun p.α (U y) + lam * U y) := by
  have hU_cont : Continuous U :=
    continuous_iff_continuousAt.2 fun x =>
      (hc3.limit_hasDeriv_value x).continuousAt
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  exact ((continuous_reactionFun hα_nonneg).comp hU_cont).add
    (continuous_const.mul hU_cont)

/-- Pointwise bound for the smooth source part on the trap interval. -/
theorem lowerPinned_source0_bound
    {p : CMParams} {lam κ M : ℝ} {φ U : ℝ → ℝ}
    (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ∀ y, |reactionFun p.α (U y) + lam * U y|
      ≤ M * (1 + M ^ p.α) + |lam| * M := by
  have hM0 : 0 ≤ M := hM.le
  have hαnn : 0 ≤ p.α := le_trans zero_le_one p.hα
  intro y
  have hUy0 : 0 ≤ U y := hU.bare.nonneg y
  have hUyM : U y ≤ M := hU.bare.le_M y
  have hUα_nonneg : 0 ≤ (U y) ^ p.α := Real.rpow_nonneg hUy0 _
  have hUα_le : (U y) ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hUy0 hUyM hαnn
  have hMα_nonneg : 0 ≤ M ^ p.α := Real.rpow_nonneg hM0 _
  have hreact : |reactionFun p.α (U y)| ≤ M * (1 + M ^ p.α) := by
    unfold reactionFun
    rw [abs_mul]
    have h1 : |U y| ≤ M := by
      rw [abs_of_nonneg hUy0]
      exact hUyM
    have h2 : |1 - (U y) ^ p.α| ≤ 1 + M ^ p.α := by
      rw [abs_le]
      constructor
      · nlinarith [hUα_nonneg, hUα_le, hMα_nonneg]
      · nlinarith [hUα_nonneg, hUα_le, hMα_nonneg]
    exact mul_le_mul h1 h2 (abs_nonneg _) hM0
  have hlin : |lam * U y| ≤ |lam| * M := by
    rw [abs_mul, abs_of_nonneg hUy0]
    exact mul_le_mul_of_nonneg_left hUyM (abs_nonneg lam)
  calc
    |reactionFun p.α (U y) + lam * U y|
        ≤ |reactionFun p.α (U y)| + |lam * U y| := abs_add_le _ _
    _ ≤ M * (1 + M ^ p.α) + |lam| * M := add_le_add hreact hlin

/-- Stationarity rewrites the diagonal cross source as the bounded linear
resolvent source. -/
theorem lowerPinned_crossSource_bound_of_stat_c3
    {p : CMParams} {c lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B := by
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

/-- The diagonal flux source `-χ·(stepFlux)'` is continuous, because it is the
difference between the smooth source part and the continuous diagonal cross
source. -/
theorem lowerPinned_fluxSource_continuous_of_c3
    {p : CMParams} {lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z) :
    Continuous (fun y => -p.χ * deriv (stepFlux p U U) y) := by
  have hsource0 : Continuous (fun y => reactionFun p.α (U y) + lam * U y) :=
    lowerPinned_source0_continuous_of_c3
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ)
      (U := U) (z := z) hU hc3
  have hcross : Continuous (crossSource p lam U U U) :=
    lowerPinned_crossSource_continuous_of_c3
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ)
      (U := U) (z := z) hU hc3
  have heq :
      (fun y => -p.χ * deriv (stepFlux p U U) y)
        =
      fun y => crossSource p lam U U U y
        - (reactionFun p.α (U y) + lam * U y) := by
    funext y
    unfold crossSource stepFlux
    ring_nf
  rw [heq]
  exact hcross.sub hsource0

/-- Bound for the folded flux source, obtained without dividing by `χ`. -/
theorem lowerPinned_fluxSource_bound_of_stat_c3
    {p : CMParams} {c lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    ∃ B : ℝ, ∀ y, |-p.χ * deriv (stepFlux p U U) y| ≤ B := by
  let B0 : ℝ := M * (1 + M ^ p.α) + |lam| * M
  obtain ⟨BR, hBR⟩ :=
    lowerPinned_crossSource_bound_of_stat_c3
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
      (φ := φ) (U := U) (z := z) hU hc3 hstat
  refine ⟨B0 + BR, ?_⟩
  intro y
  have h0 : |reactionFun p.α (U y) + lam * U y| ≤ B0 :=
    lowerPinned_source0_bound
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ)
      (U := U) hM hU y
  have heq :
      -p.χ * deriv (stepFlux p U U) y
        =
      crossSource p lam U U U y
        - (reactionFun p.α (U y) + lam * U y) := by
    unfold crossSource stepFlux
    ring_nf
  rw [heq]
  calc
    |crossSource p lam U U U y - (reactionFun p.α (U y) + lam * U y)|
        ≤ |crossSource p lam U U U y|
          + |reactionFun p.α (U y) + lam * U y| := abs_sub _ _
    _ ≤ B0 + BR := by linarith [h0, hBR y]

/-- Product-rule formula for the diagonal cross flux derivative. -/
theorem lowerPinned_stepFlux_deriv_eq_of_c3
    {p : CMParams} {κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z) :
    (fun x => deriv (stepFlux p U U) x)
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
      stepFlux p U U =
      (fun y => (U y) ^ p.m) * deriv (frozenElliptic p U) := by
    ext y
    simp [stepFlux, Pi.mul_apply]
  rw [hfun_eq, hprod.deriv]

/-- The diagonal cross flux is C¹ under the C³ bootstrap data. -/
theorem lowerPinned_stepFlux_C1_of_c3
    {p : CMParams} {κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z) :
    ∀ y, HasDerivAt (stepFlux p U U) (deriv (stepFlux p U U) y) y := by
  intro x
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
      stepFlux p U U =
      (fun y => (U y) ^ p.m) * deriv (frozenElliptic p U) := by
    ext y
    simp [stepFlux, Pi.mul_apply]
  have hstep :
      HasDerivAt (stepFlux p U U)
        (deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x +
          (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ)) x := by
    rw [hfun_eq]
    exact hprod
  have hform := congrFun
    (lowerPinned_stepFlux_deriv_eq_of_c3
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) (z := z) hU hc3) x
  simpa [hform] using hstep

/-- The derivative of the diagonal cross flux is continuous under the C³
bootstrap data. -/
theorem lowerPinned_stepFlux_deriv_continuous_of_c3
    {p : CMParams} {κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z) :
    Continuous (fun x => deriv (stepFlux p U U) x) := by
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
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ_nonneg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
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
  have hform :=
    lowerPinned_stepFlux_deriv_eq_of_c3
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) (z := z) hU hc3
  simpa [hform] using hterm1.add hterm2

/-- The diagonal cross flux itself is bounded on a trapped profile. -/
theorem lowerPinned_stepFlux_bound_of_trap
    {p : CMParams} {κ M : ℝ} {φ U : ℝ → ℝ}
    (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U) :
    ∀ y, |stepFlux p U U y| ≤ M ^ p.m * M ^ p.γ := by
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hM0 : 0 ≤ M := hM.le
  intro y
  have hUy0 : 0 ≤ U y := hU.bare.nonneg y
  have hUyM : U y ≤ M := hU.bare.le_M y
  have hUpow : |(U y) ^ p.m| ≤ M ^ p.m := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUy0 _)]
    exact Real.rpow_le_rpow hUy0 hUyM hm_nonneg
  have hV' : |deriv (frozenElliptic p U) y| ≤ M ^ p.γ := by
    calc
      |deriv (frozenElliptic p U) y| ≤ frozenElliptic p U y :=
        frozenElliptic_deriv_abs_le p hU.bare.trap.cunif_bdd hU.bare.nonneg y
      _ ≤ M ^ p.γ :=
        frozenElliptic_le_rpow_of_inWaveTrapSet p hM hU.bare.trap y
  have hMm_nonneg : 0 ≤ M ^ p.m := Real.rpow_nonneg hM0 _
  rw [stepFlux, abs_mul]
  exact mul_le_mul hUpow hV' (abs_nonneg _) hMm_nonneg

/-- The derivative of the diagonal cross flux is bounded under the C³ bootstrap
data. -/
theorem lowerPinned_stepFlux_deriv_bound_of_c3
    {p : CMParams} {κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z) :
    ∃ B : ℝ, ∀ y, |deriv (stepFlux p U U) y| ≤ B := by
  obtain ⟨C1, hC1_nonneg, hC1⟩ := hc3.limit_deriv_bound
  let B1 : ℝ := C1 * |p.m| * M ^ (p.m - 1) * M ^ p.γ
  let B2 : ℝ := M ^ p.m * (M ^ p.γ + M ^ p.γ)
  refine ⟨B1 + B2, ?_⟩
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ_nonneg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hM0 : 0 ≤ M := hM.le
  have hMm_nonneg : 0 ≤ M ^ p.m := Real.rpow_nonneg hM0 _
  have hMm1_nonneg : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM0 _
  have hMγ_nonneg : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM0 _
  intro y
  have hUy0 : 0 ≤ U y := hU.bare.nonneg y
  have hUyM : U y ≤ M := hU.bare.le_M y
  have hUm1_abs : |(U y) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUy0 _)]
    exact Real.rpow_le_rpow hUy0 hUyM hm1_nonneg
  have hUm_abs : |(U y) ^ p.m| ≤ M ^ p.m := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUy0 _)]
    exact Real.rpow_le_rpow hUy0 hUyM hm_nonneg
  have hUγ_abs : |(U y) ^ p.γ| ≤ M ^ p.γ := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUy0 _)]
    exact Real.rpow_le_rpow hUy0 hUyM hγ_nonneg
  have hV'_abs : |deriv (frozenElliptic p U) y| ≤ M ^ p.γ := by
    calc
      |deriv (frozenElliptic p U) y| ≤ frozenElliptic p U y :=
        frozenElliptic_deriv_abs_le p hU.bare.trap.cunif_bdd hU.bare.nonneg y
      _ ≤ M ^ p.γ :=
        frozenElliptic_le_rpow_of_inWaveTrapSet p hM hU.bare.trap y
  have hV_abs : |frozenElliptic p U y| ≤ M ^ p.γ := by
    rw [abs_of_nonneg (frozenElliptic_nonneg p hU.bare.nonneg y)]
    exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hU.bare.trap y
  have hterm1 :
      |deriv U y * p.m * (U y) ^ (p.m - 1) *
          deriv (frozenElliptic p U) y| ≤ B1 := by
    dsimp [B1]
    rw [abs_mul, abs_mul, abs_mul]
    have hA :
        |deriv U y| * |p.m| ≤ C1 * |p.m| :=
      mul_le_mul_of_nonneg_right (hC1 y) (abs_nonneg p.m)
    have hA_nonneg : 0 ≤ |deriv U y| * |p.m| := by positivity
    have hB_nonneg : 0 ≤ C1 * |p.m| := by positivity
    have hB :
        |deriv U y| * |p.m| * |(U y) ^ (p.m - 1)|
          ≤ C1 * |p.m| * M ^ (p.m - 1) :=
      mul_le_mul hA hUm1_abs (abs_nonneg _) hB_nonneg
    have hB_left_nonneg :
        0 ≤ |deriv U y| * |p.m| * |(U y) ^ (p.m - 1)| := by positivity
    have hB_right_nonneg :
        0 ≤ C1 * |p.m| * M ^ (p.m - 1) := by positivity
    exact mul_le_mul hB hV'_abs (abs_nonneg _) hB_right_nonneg
  have hterm2 :
      |(U y) ^ p.m * (frozenElliptic p U y - (U y) ^ p.γ)| ≤ B2 := by
    dsimp [B2]
    rw [abs_mul]
    have hdiff :
        |frozenElliptic p U y - (U y) ^ p.γ|
          ≤ M ^ p.γ + M ^ p.γ := by
      calc
        |frozenElliptic p U y - (U y) ^ p.γ|
            ≤ |frozenElliptic p U y| + |(U y) ^ p.γ| := abs_sub _ _
        _ ≤ M ^ p.γ + M ^ p.γ := add_le_add hV_abs hUγ_abs
    exact mul_le_mul hUm_abs hdiff (abs_nonneg _) hMm_nonneg
  have hform := congrFun
    (lowerPinned_stepFlux_deriv_eq_of_c3
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) (z := z) hU hc3) y
  rw [hform]
  calc
    |deriv U y * p.m * (U y) ^ (p.m - 1) *
          deriv (frozenElliptic p U) y +
        (U y) ^ p.m * (frozenElliptic p U y - (U y) ^ p.γ)|
        ≤ |deriv U y * p.m * (U y) ^ (p.m - 1) *
            deriv (frozenElliptic p U) y|
          + |(U y) ^ p.m * (frozenElliptic p U y - (U y) ^ p.γ)| :=
            abs_add_le _ _
    _ ≤ B1 + B2 := add_le_add hterm1 hterm2

/-- A bounded continuous source remains integrable after multiplication by the
translated Green kernel, on either side of the base point. -/
theorem greenKernel_const_sub_mul_integrableOn_Ioi_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    IntegrableOn (fun y => greenKernel c lam (x - y) * H y) (Ioi x) :=
  (greenKernel_comp_const_sub_mul_integrable_of_bounded
    (c := c) (lam := lam) hlam hH hB x).integrableOn

theorem greenKernel_const_sub_mul_integrableOn_Iic_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    IntegrableOn (fun y => greenKernel c lam (x - y) * H y) (Iic x) :=
  (greenKernel_comp_const_sub_mul_integrable_of_bounded
    (c := c) (lam := lam) hlam hH hB x).integrableOn

theorem neg_greenKernelDeriv_const_sub_mul_integrableOn_Ioi_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    IntegrableOn (((fun y => -greenKernelDeriv c lam (x - y)) * H)) (Ioi x) := by
  have hbase_on :
      IntegrableOn (fun y => greenKernelDeriv c lam (x - y) * H y) (Ioi x) :=
    (greenKernelDeriv_comp_const_sub_mul_integrable_of_bounded
      (c := c) (lam := lam) hlam hH hB x).integrableOn
  have hneg_on :
      IntegrableOn (fun y => -(greenKernelDeriv c lam (x - y) * H y)) (Ioi x) :=
    hbase_on.neg
  refine IntegrableOn.congr_fun hneg_on ?_ measurableSet_Ioi
  intro y _hy
  simp [Pi.mul_apply]

theorem neg_greenKernelDeriv_const_sub_mul_integrableOn_Iic_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    IntegrableOn (((fun y => -greenKernelDeriv c lam (x - y)) * H)) (Iic x) := by
  have hbase_on :
      IntegrableOn (fun y => greenKernelDeriv c lam (x - y) * H y) (Iic x) :=
    (greenKernelDeriv_comp_const_sub_mul_integrable_of_bounded
      (c := c) (lam := lam) hlam hH hB x).integrableOn
  have hneg_on :
      IntegrableOn (fun y => -(greenKernelDeriv c lam (x - y) * H y)) (Iic x) :=
    hbase_on.neg
  refine IntegrableOn.congr_fun hneg_on ?_ measurableSet_Iic
  intro y _hy
  simp [Pi.mul_apply]

/-- At the right tail, a bounded factor times a factor tending to zero tends to
zero.  This is the atTop counterpart of the existing atBot helper. -/
theorem tendsto_zero_mul_of_bounded_right_atTop
    {f g : ℝ → ℝ} {C : ℝ}
    (_hC0 : 0 ≤ C) (hg : ∀ x, |g x| ≤ C)
    (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun x => f x * g x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hfabs : Tendsto (fun x => |f x|) atTop (𝓝 0) := by
    simpa using hf.abs
  refine squeeze_zero
    (f := fun x => ‖f x * g x‖)
    (g := fun x => C * |f x|)
    (fun x => norm_nonneg (f x * g x)) ?_ ?_
  · intro x
    change ‖f x * g x‖ ≤ C * |f x|
    rw [Real.norm_eq_abs, abs_mul]
    have hmul := mul_le_mul_of_nonneg_left (hg x) (abs_nonneg (f x))
    nlinarith [hmul]
  · simpa [mul_comm] using hfabs.const_mul C

theorem greenKernel_const_sub_tendsto_atTop_zero
    {c lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Tendsto (fun y => greenKernel c lam (x - y)) atTop (𝓝 0) := by
  have hrp : 0 < greenRootPlus c lam := greenRootPlus_pos (c := c) hlam
  have hsub : Tendsto (fun y : ℝ => x - y) atTop atBot := by
    have htop : Tendsto (fun y : ℝ => y + (-x)) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop (-x) tendsto_id
    have hneg : Tendsto (fun y : ℝ => -(y + (-x))) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp htop
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  have hlin : Tendsto (fun y : ℝ => greenRootPlus c lam * (x - y)) atTop atBot :=
    hsub.const_mul_atBot hrp
  have hexp :
      Tendsto (fun y : ℝ => Real.exp (greenRootPlus c lam * (x - y)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hbranch :
      (fun y => greenKernel c lam (x - y))
        =ᶠ[atTop]
      fun y => (greenDelta c lam)⁻¹ *
        Real.exp (greenRootPlus c lam * (x - y)) := by
    filter_upwards [Filter.eventually_ge_atTop x] with y hy
    have hxy : x - y ≤ 0 := by linarith
    simp [greenKernel, hxy]
  have htail :
      Tendsto
        (fun y => (greenDelta c lam)⁻¹ *
          Real.exp (greenRootPlus c lam * (x - y)))
        atTop (𝓝 ((greenDelta c lam)⁻¹ * 0)) :=
    tendsto_const_nhds.mul hexp
  simpa using htail.congr' hbranch.symm

theorem greenKernel_const_sub_tendsto_atBot_zero
    {c lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Tendsto (fun y => greenKernel c lam (x - y)) atBot (𝓝 0) := by
  have hrm : greenRootMinus c lam < 0 := greenRootMinus_neg (c := c) hlam
  have hsub : Tendsto (fun y : ℝ => x - y) atBot atTop := by
    have hneg : Tendsto (fun y : ℝ => -y) atBot atTop :=
      Filter.tendsto_neg_atBot_atTop
    have htop : Tendsto (fun y : ℝ => -y + x) atBot atTop :=
      Filter.tendsto_atTop_add_const_right atBot x hneg
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htop
  have hlin :
      Tendsto (fun y : ℝ => greenRootMinus c lam * (x - y)) atBot atBot :=
    hsub.const_mul_atTop_of_neg hrm
  have hexp :
      Tendsto (fun y : ℝ => Real.exp (greenRootMinus c lam * (x - y)))
        atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hbranch :
      (fun y => greenKernel c lam (x - y))
        =ᶠ[atBot]
      fun y => (greenDelta c lam)⁻¹ *
        Real.exp (greenRootMinus c lam * (x - y)) := by
    filter_upwards [Filter.eventually_le_atBot (x - 1)] with y hy
    have hxy : 0 < x - y := by linarith
    simp [greenKernel, not_le.mpr hxy]
  have htail :
      Tendsto
        (fun y => (greenDelta c lam)⁻¹ *
          Real.exp (greenRootMinus c lam * (x - y)))
        atBot (𝓝 ((greenDelta c lam)⁻¹ * 0)) :=
    tendsto_const_nhds.mul hexp
  simpa using htail.congr' hbranch.symm

theorem greenKernel_const_sub_mul_bounded_tendsto_atTop_zero
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    Tendsto (((fun y => greenKernel c lam (x - y)) * H)) atTop (𝓝 0) := by
  have hK := greenKernel_const_sub_tendsto_atTop_zero
    (c := c) (lam := lam) hlam x
  have h := tendsto_zero_mul_of_bounded_right_atTop hB0 hB hK
  simpa [Pi.mul_apply] using h

theorem greenKernel_const_sub_mul_bounded_tendsto_atBot_zero
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    Tendsto (((fun y => greenKernel c lam (x - y)) * H)) atBot (𝓝 0) := by
  have hK := greenKernel_const_sub_tendsto_atBot_zero
    (c := c) (lam := lam) hlam x
  have h := tendsto_zero_mul_of_bounded_right_atBot hB0 hB hK
  simpa [Pi.mul_apply] using h

/-- Trap + stationarity + C³ regularity discharge the full stationary
cross-Green data package used by the diagonal Green representation. -/
theorem stationaryCrossGreenData_of_trap
    {p : CMParams} {c lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    StationaryCrossGreenData p c lam U := by
  have hS_cont : Continuous (fun y => reactionFun p.α (U y) + lam * U y) :=
    lowerPinned_source0_continuous_of_c3
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ)
      (U := U) (z := z) hU hc3
  have hS_bound : ∀ y,
      |reactionFun p.α (U y) + lam * U y|
        ≤ M * (1 + M ^ p.α) + |lam| * M :=
    lowerPinned_source0_bound
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ)
      (U := U) hM hU
  have hFl_cont : Continuous (fun y => -p.χ * deriv (stepFlux p U U) y) :=
    lowerPinned_fluxSource_continuous_of_c3
      (p := p) (lam := lam) (κ := κ) (M := M) (φ := φ)
      (U := U) (z := z) hU hc3
  obtain ⟨BFl, hBFl⟩ :=
    lowerPinned_fluxSource_bound_of_stat_c3
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
      (φ := φ) (U := U) (z := z) hM hU hc3 hstat
  have hG_C1 :
      ∀ y, HasDerivAt (stepFlux p U U) (deriv (stepFlux p U U) y) y :=
    lowerPinned_stepFlux_C1_of_c3
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) (z := z) hU hc3
  have hG'_cont : Continuous (fun y => deriv (stepFlux p U U) y) :=
    lowerPinned_stepFlux_deriv_continuous_of_c3
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) (z := z) hU hc3
  obtain ⟨BG', hBG'⟩ :=
    lowerPinned_stepFlux_deriv_bound_of_c3
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) (z := z)
      hM hU hc3
  have hG_cont : Continuous (stepFlux p U U) :=
    continuous_iff_continuousAt.2 fun y => (hG_C1 y).continuousAt
  have hG_bound : ∀ y, |stepFlux p U U y| ≤ M ^ p.m * M ^ p.γ :=
    lowerPinned_stepFlux_bound_of_trap
      (p := p) (κ := κ) (M := M) (φ := φ) (U := U) hM hU
  have hSBound_nonneg : 0 ≤ M * (1 + M ^ p.α) + |lam| * M := by
    have hM0 : 0 ≤ M := hM.le
    have hMα : 0 ≤ M ^ p.α := Real.rpow_nonneg hM0 _
    positivity
  have hBFl_nonneg : 0 ≤ BFl := le_trans (abs_nonneg _) (hBFl 0)
  have hBG'_nonneg : 0 ≤ BG' := le_trans (abs_nonneg _) (hBG' 0)
  have hG_bound_nonneg : 0 ≤ M ^ p.m * M ^ p.γ := by positivity
  refine
    { hSmIic := ?_
      hSmIoi := ?_
      hFlIic := ?_
      hFlIoi := ?_
      hG_C1 := hG_C1
      hKv'_Ioi := ?_
      hKv'_Iic := ?_
      hK'v_Ioi := ?_
      hK'v_Iic := ?_
      hKG_Iic := ?_
      hKG_Ioi := ?_
      hdecay_top := ?_
      hdecay_bot := ?_ }
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Iic_of_bounded
      (c := c) (lam := lam) hlam hS_cont hS_bound x
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Ioi_of_bounded
      (c := c) (lam := lam) hlam hS_cont hS_bound x
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Iic_of_bounded
      (c := c) (lam := lam) hlam hFl_cont hBFl x
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Ioi_of_bounded
      (c := c) (lam := lam) hlam hFl_cont hBFl x
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Ioi_of_bounded
      (c := c) (lam := lam) hlam hG'_cont hBG' x
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Iic_of_bounded
      (c := c) (lam := lam) hlam hG'_cont hBG' x
  · intro x
    exact neg_greenKernelDeriv_const_sub_mul_integrableOn_Ioi_of_bounded
      (c := c) (lam := lam) hlam hG_cont hG_bound x
  · intro x
    exact neg_greenKernelDeriv_const_sub_mul_integrableOn_Iic_of_bounded
      (c := c) (lam := lam) hlam hG_cont hG_bound x
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Iic_of_bounded
      (c := c) (lam := lam) hlam hFl_cont hBFl x
  · intro x
    exact greenKernel_const_sub_mul_integrableOn_Ioi_of_bounded
      (c := c) (lam := lam) hlam hFl_cont hBFl x
  · intro x
    exact greenKernel_const_sub_mul_bounded_tendsto_atTop_zero
      (c := c) (lam := lam) hlam hG_bound_nonneg hG_bound x
  · intro x
    exact greenKernel_const_sub_mul_bounded_tendsto_atBot_zero
      (c := c) (lam := lam) hlam hG_bound_nonneg hG_bound x

/-- Lower-pinned construction-site Green representation: the stationary
profile is the Rothe limit, each step has the committed Green representation,
and the step sources converge through the independently threaded Green source
limit. -/
theorem lowerPinned_stationaryGreenRepresentation_profile_of_greenStep_rotheLimit
    {p : CMParams} {c lam κ M Λ : ℝ} {φ U : ℝ → ℝ}
    {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hlim : rotheLimit z = U)
    (hLU : LocallyUniformConverges z (rotheLimit z))
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hstep : ∀ k, PaperStepAnalytic p c lam M κ Λ U (z k) (z (k + 1)))
    (hc3 : PaperC3BootstrapData U z)
    (hR_limit :
      LocallyUniformConverges (fun k => (hstep k).R)
        (crossSource p lam U U U))
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    StationaryCrossGreenData p c lam U ∧
      Continuous (crossSource p lam U U U) ∧
      (∀ x,
        IntegrableOn
          (gWeight (greenRootPlus c lam) (crossSource p lam U U U))
          (Ioi x)) ∧
      (∀ x,
        IntegrableOn
          (gWeight (greenRootMinus c lam) (crossSource p lam U U U))
          (Iic x)) ∧
      crossImplicitMap p c lam U U U = U := by
  have hLU_U : LocallyUniformConverges z U := by
    simpa [hlim] using hLU
  have hcross : StationaryCrossGreenData p c lam U :=
    stationaryCrossGreenData_of_trap
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
      (φ := φ) (U := U) (z := z) hlam hM hU hc3 hstat
  have hR_cont : Continuous (crossSource p lam U U U) :=
    lowerPinned_crossSource_continuous_of_c3
      (p := p) (lam := lam) (κ := κ) (M := M)
      (φ := φ) (U := U) (z := z) hU hc3
  have hR_bound : ∃ B : ℝ, ∀ y, |crossSource p lam U U U y| ≤ B :=
    lowerPinned_crossSource_bound_of_stat_c3
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
      (φ := φ) (U := U) (z := z) hU hc3 hstat
  have hthread :
      StationaryGreenRepresentationThreadData p c lam U z
        (fun k => (hstep k).R) :=
    stationaryGreenRepresentationThreadData_of_greenStep
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (Λ := Λ)
      (U := U) (z := z) hlam hstep hcross hR_cont hR_bound hR_limit
  exact stationaryGreenRepresentation_profile_of_rotheLimit
    (p := p) (c := c) (lam := lam) (U := U)
    (z := z) (Rseq := fun k => (hstep k).R) hlam hlim hLU hthread

theorem lowerPinnedStationaryGreenSourceTail_of_frozenWaveOperator_zero_from_c3
    {p : CMParams} {c lam κ M : ℝ} {φ U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hc3 : PaperC3BootstrapData U z)
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
      (z := z) hM hU hc3
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
    (hU_diff : Differentiable ℝ U)
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
        (p := p) (κ := κ) (M := M) (U := U)
        (L := LR * lam⁻¹)
        hM hU.bare hU_diff hUlim hVlim hD1⟩

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
  paperLowerPinnedStationary_of_stepConsistency hlam
    (paperRotheLimitStepConsistency_of_uniformBounds hLU hstep hbounds)
    hdiff

theorem paperLowerPinnedStationary_of_greenStep
    {p : CMParams} {c lam κ M Λ : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (Rlim : (ℝ → ℝ) → ℝ → ℝ)
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
    (hR_cont :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        Continuous (Rlim U))
    (hR_bound :
      ∀ U, (hU : InLowerPinnedMonotoneTrap κ M φ U) →
        ∃ B : ℝ,
          (∀ k y, |((hgreen U hU) k).R y| ≤ B) ∧
            ∀ y, |Rlim U y| ≤ B)
    (hR_limit :
      ∀ U, (hU : InLowerPinnedMonotoneTrap κ M φ U) →
        LocallyUniformConverges (fun k => ((hgreen U hU) k).R) (Rlim U))
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
        (φ := φ) (U := U) (z := rotheSeq U) (R := Rlim U)
        hlam hM hΛ hU hLU_U (hz_nonneg U hU) (hz_le_M U hU)
        (hgreen U hU) (hR_cont U hU) (hR_bound U hU) (hR_limit U hU))
    (paperDiagonalDifferentiabilityFloor_of_c3BootstrapData
      (p := p) (κ := κ) (M := M) (φ := φ) (rotheSeq := rotheSeq) hc3)

theorem paperRotheLimit_stationary_of_producer
    {p : CMParams} {c lam κ M Λ : ℝ} {φ : ℝ → ℝ}
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hbounds :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges
          (rotheSeqOfPaper p c lam M κ Λ U (hprodAll U) hκ hM) U →
          PaperC2CompactUniformBounds p U
            (rotheSeqOfPaper p c lam M κ Λ U (hprodAll U) hκ hM)) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit
          (rotheSeqOfPaper p c lam M κ Λ U (hprodAll U) hκ hM) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 := by
  let zseq : (ℝ → ℝ) → ℕ → ℝ → ℝ :=
    fun U => rotheSeqOfPaper p c lam M κ Λ U (hprodAll U) hκ hM
  have hLU :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (zseq U) (rotheLimit (zseq U)) := by
    intro U _hU
    have hdata : PaperRotheOrbitData p c lam M κ zseq U := by
      simpa [zseq] using
        paperRotheOrbitData (p := p) (c := c) (lam := lam)
          (M := M) (κ := κ) (Λ := Λ) (u := U)
          hprodAll hκ hM hΛ0 hΛM hbarLip
    exact hdata.locallyUniform hM
  have hstep :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        ∀ k, paperImplicitStepOp p c (1 / lam) U (zseq U (k + 1)) =
          zseq U k := by
    intro U _hU k
    funext x
    simpa [zseq] using
      (rotheSeqOfPaper_stepFacts (p := p) (c := c) (lam := lam)
        (M := M) (κ := κ) (Λ := Λ) (u := U)
        (hprod := hprodAll U) hκ hM k).step_op x
  have hbounds_z :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        LocallyUniformConverges (zseq U) U →
          PaperC2CompactUniformBounds p U (zseq U) := by
    intro U hU hLU_U
    simpa [zseq] using
      hbounds U hU (by simpa [zseq] using hLU_U)
  have hcons : PaperRotheLimitStepConsistency p c lam κ M φ zseq :=
    paperRotheLimitStepConsistency_of_uniformBounds hLU hstep hbounds_z
  have hfixed :
      PaperRotheLimitFixedStepIdentity p c lam κ M φ zseq :=
    paperRotheLimitFixedStepIdentity_of_stepConsistency hcons
  intro U hU hlim x
  have hlim_z : rotheLimit (zseq U) = U := by
    simpa [zseq] using hlim
  have hLU_U : LocallyUniformConverges (zseq U) U := by
    simpa [hlim_z] using hLU U hU
  have hboundsU : PaperC2CompactUniformBounds p U (zseq U) :=
    hbounds_z U hU hLU_U
  have hlam : 0 < lam := (hprodAll U).hlam
  have hpaper : paperWaveOperator p c U U x = 0 :=
    paperImplicitStep_fixed_paperWaveOperator_zero p c (1 / lam) U
      (one_div_ne_zero (ne_of_gt hlam)) (hfixed U hU hlim_z) x
  have hbare : InMonotoneWaveTrapSet κ M U := hU.bare
  have hdiag :
      paperWaveOperator p c U U x = frozenWaveOperator p c U U x :=
    paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x
      hbare.trap.cunif_bdd hbare.nonneg
      ((hboundsU.hasDeriv_U x).differentiableAt)
      (frozenElliptic_deriv_differentiableAt p
        hbare.trap.cunif_bdd hbare.nonneg x)
      (((hboundsU.hasDeriv_U x).differentiableAt).rpow_const
        (Or.inr p.hm))
  simpa [hdiag] using hpaper

theorem paperRotheLimit_stationary_of_producer_fromCond
    {p : CMParams} {c lam κ M κtilde D Λ : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hbounds :
      ∀ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        LocallyUniformConverges
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll U) U →
          PaperC2CompactUniformBounds p U
            (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll U)) :
    ∀ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 := by
  let hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hstat :=
    paperRotheLimit_stationary_of_producer
      (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
      (Λ := Λ) (φ := lowerBarrierRaw κ κtilde D)
      hprodAll hcond.hκ0.le hM0 hΛ0 hΛM hbarLip
      (fun U hU hLU_U => by
        simpa [rotheSeqOfPaperFromCond, hM0] using
          hbounds U hU (by
            simpa [rotheSeqOfPaperFromCond, hM0] using hLU_U))
  intro U hU hlim
  exact hstat U hU (by
    simpa [rotheSeqOfPaperFromCond, hM0] using hlim)

theorem paperRotheLimit_stationary_of_lowerRawProducer_fromCond
    {p : CMParams} {c lam κ M κtilde D Λ : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hprodAll : ∀ u,
      PaperLowerRawStepProducer p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hbounds :
      ∀ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        LocallyUniformConverges
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) U →
          PaperC2CompactUniformBounds p U
            (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
              (fun u => (hprodAll u).producer) U)) :
    ∀ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 :=
  paperRotheLimit_stationary_of_producer_fromCond
    (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
    (κtilde := κtilde) (D := D) (Λ := Λ)
    hcond (fun u => (hprodAll u).producer) hΛ0 hΛM hbarLip hbounds

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
    (Rlim : (ℝ → ℝ) → ℝ → ℝ)
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
    (hR_cont :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        Continuous (Rlim U))
    (hR_bound :
      ∀ U, (hU : InLowerPinnedMonotoneTrap κ M φ U) →
        ∃ B : ℝ,
          (∀ k y, |((hgreen U hU) k).R y| ≤ B) ∧
            ∀ y, |Rlim U y| ≤ B)
    (hR_limit :
      ∀ U, (hU : InLowerPinnedMonotoneTrap κ M φ U) →
        LocallyUniformConverges (fun k => ((hgreen U hU) k).R) (Rlim U))
    (hc3 :
      ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
        PaperC3BootstrapData U (rotheSeq U))
    (hdiff : PaperDiagonalDifferentiabilityFloor p κ M φ) :
    PaperLowerPinnedStationaryFlatFloor p c κ M φ rotheSeq :=
  paperLowerPinnedStationaryFlatFloor_of_uniformBounds
    (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (φ := φ)
    (rotheSeq := rotheSeq) hlam hLU hstep
    (fun U hU hLU_U =>
      paperC2CompactUniformBounds_of_greenStep
        (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (Λ := Λ)
        (φ := φ) (U := U) (z := rotheSeq U) (R := Rlim U)
        hlam hM hΛ hU hLU_U (hz_nonneg U hU) (hz_le_M U hU)
        (hgreen U hU) (hR_cont U hU) (hR_bound U hU) (hR_limit U hU))
    hdiff
    (fun U hU hstat =>
      frozenStationaryFlatAtLeft_of_green_source_tail
        (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (φ := φ)
        (U := U) hlam hM hU (hdiff.U_diff U hU)
        (lowerPinnedStationaryGreenSourceTail_of_frozenWaveOperator_zero_from_c3
          (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
          (φ := φ) (U := U) (z := rotheSeq U)
          hlam hM hU (hc3 U hU)
          (stationaryCrossGreenData_of_trap
            (p := p) (c := c) (lam := lam) (κ := κ) (M := M)
            (φ := φ) (U := U) (z := rotheSeq U)
            hlam hM hU (hc3 U hU) hstat)
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
#print axioms paperRotheLimitFixedStepIdentity_of_stepConsistency
#print axioms paperLowerPinnedStationary_of_stepConsistency
#print axioms paperLowerPinnedStationary_of_uniformBounds
#print axioms paperLowerPinnedStationary_of_greenStep
#print axioms paperRotheLimit_stationary_of_producer
#print axioms paperRotheLimit_stationary_of_producer_fromCond
#print axioms paperRotheLimit_stationary_of_lowerRawProducer_fromCond
#print axioms paperLowerPinnedStationaryFlatFloor_of_uniformBounds
#print axioms paperLowerPinnedStationaryFlatFloor_of_greenStep

end

end ShenWork.Paper1
