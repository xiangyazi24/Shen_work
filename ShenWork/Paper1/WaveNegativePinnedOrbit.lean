import ShenWork.Paper1.WaveInitialKinkStep
import ShenWork.Paper1.WaveNegativeRotheParameters

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Assemble the ordinary Rothe facts from a genuine local source step and its
two order facts. -/
def PaperLocalFixedStepData.toRotheStepFacts
    {p : CMParams} {c lam M κ Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z)
    (rest : PaperLocalFixedStepRestData p c lam M κ Λ B u Z d) :
    PaperRotheStepFacts p c lam M κ Λ u Z d.fixed.W := by
  have hW2 : ContDiff ℝ 2 d.fixed.W := d.contDiff_two hlam
  exact
    { step_op := d.step_op hlam
      cont := hW2.continuous
      diff := hW2.differentiable (by norm_num)
      contDiff2 := hW2
      deriv_le := d.deriv_le hlam
      nonneg := fun x => (d.range x).1
      le_barrier := fun x => (d.range x).2
      le_old := rest.le_old
      anti := rest.anti
      paperSuper := paperWaveOperator_nonpos_of_implicitStep_le
        (p := p) (c := c) (lam := lam) hlam (d.step_op hlam) rest.le_old }

/-- The exact local data selected by the source-box Schauder theorem. -/
noncomputable def paperNegativePinnedLocalStep
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D)
    {u Z : ℝ → ℝ}
    (hu : InMonotoneWaveTrapSet (kappa c) 1 u)
    (hZ : PaperIterateBase p c (kappa c) 1 u Z) :
    PaperLocalFixedStepData p c s.lam 1 (kappa c) s.Λ s.B u Z := by
  let holderKernel :=
    paperFixedSourceMap_holder_kernel
      (p := p) (c := c) (lam := s.lam) (M := 1) (κ := kappa c)
      (B := s.B) (u := u) (Z := Z)
      s.hlam s.hrpκ s.hrmκ s.hκ.le one_pos s.hB hu.trap hZ
  let H : ℝ := Classical.choose holderKernel
  exact Classical.choose
    (paperLocalFixedStepData_exists_of_trap
      p (c := c) (lam := s.lam) (M := 1) (κ := kappa c) (Λ := s.Λ)
      (B := s.B) (H := H) (u := u) (Z := Z)
      s.hlam s.hrpκ s.hrmκ s.hκ one_pos s.hB hu hZ
      s.sourceScalar le_rfl s.barrier s.hΛ)

/-- One positive-index state of the actual lower-pinned Rothe orbit.  Keeping
the preceding local source record is what makes the successor log-slope bound
available without a globally quantified tail assumption. -/
structure PaperNegativePinnedStepState
    (p : CMParams) (c D : ℝ)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ) : Type where
  old : ℝ → ℝ
  data : PaperLocalFixedStepData
    p c s.lam 1 (kappa c) s.Λ s.B u old
  facts : PaperRotheStepFacts
    p c s.lam 1 (kappa c) s.Λ u old data.fixed.W
  pinned : InLowerPinnedMonotoneTrap (kappa c) 1
    (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D)
    data.fixed.W

/-- A local-step fact package gives the bare monotone trap membership of its
new profile. -/
theorem PaperLocalFixedStepData.monotoneTrap_of_rest
    {p : CMParams} {c lam κ Λ B : ℝ} {u Z : ℝ → ℝ}
    (d : PaperLocalFixedStepData p c lam 1 κ Λ B u Z)
    (rest : PaperLocalFixedStepRestData p c lam 1 κ Λ B u Z d)
    (hcont : Continuous d.fixed.W) :
    InMonotoneWaveTrapSet κ 1 d.fixed.W := by
  refine ⟨⟨⟨hcont, ⟨1, ?_⟩⟩, fun x => d.range x⟩, rest.anti⟩
  intro x
  rw [abs_of_nonneg (d.range x).1]
  exact (d.range x).2.trans (upperBarrier_le_M κ 1 x)

/-- The genuine lower-pinned orbit state.  The kink-aware theorem closes the
first step; `rest_of_lowerPinned_old` closes every subsequent step. -/
noncomputable def paperNegativePinnedStepState
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ)
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    ℕ → PaperNegativePinnedStepState p c D s u
  | 0 => by
      let Z := upperBarrier (kappa c) 1
      let hZ : PaperIterateBase p c (kappa c) 1 u Z :=
        upperBarrier_paperIterateBase hcond.hκ0.le zero_le_one
          (paperUpperBarrier_super_of_scalar s.hκ s.barrier hu.bare)
      let d := paperNegativePinnedLocalStep s hu.bare hZ
      have hrouteCmono :
          paperCmono p (-p.χ) 1 (1 ^ p.γ) (2 * 1 ^ p.γ) ≤ s.Cmono := by
        rw [s.Cmono_eq]
        simp only [Real.one_rpow, mul_one]
        exact le_rfl
      have hanti : Antitone d.fixed.W :=
        d.antitone_of_upperBarrier_one s.hlam s.hκ hu.bare
          (paperFrozenEllipticSourceBox_of_conditions hcond)
          s.barrier.hχ s.Cmono_small hrouteCmono
      let rest : PaperLocalFixedStepRestData
          p c s.lam 1 (kappa c) s.Λ s.B u Z d :=
        { le_old := fun x => (d.range x).2
          anti := hanti }
      let facts := d.toRotheStepFacts s.hlam rest
      have hlower : ∀ x,
          lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D x ≤
            d.fixed.W x :=
        d.lowerRaw_of_old_lowerRaw hcond hD hD1 hu
          (fun x => (hu.lower x).trans (hu.bare.le_upperBarrier x))
          s.hlam s.lowerRaw_small
      have hbare : InMonotoneWaveTrapSet (kappa c) 1 d.fixed.W :=
        d.monotoneTrap_of_rest rest facts.cont
      exact
        { old := Z
          data := d
          facts := facts
          pinned := ⟨hbare, hlower⟩ }
  | n + 1 => by
      let prev := paperNegativePinnedStepState hcond hD hD1 s u hu n
      let d := paperNegativePinnedLocalStep s hu.bare prev.facts.toBase
      have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
      have hrouteCmono :
          paperCmono p (-p.χ) 1 (1 ^ p.γ) (2 * 1 ^ p.γ) ≤ s.Cmono := by
        rw [s.Cmono_eq]
        simp only [Real.one_rpow, mul_one]
        exact le_rfl
      let rest := PaperLocalFixedStepData.rest_of_lowerPinned_old
        (p := p) (c := c) (lam := s.lam) (M := 1)
        (κ := kappa c) (κtilde := negativeBranchTailCap p c)
        (D := D) (Λ := s.Λ) (B := s.B) (Cmono := s.Cmono)
        (u := u) (Z₀ := prev.old)
        s.hlam s.hrpκ s.hrmκ s.hκ
        (sub_pos.mpr hcond.hgap) hDpos one_pos s.hB hu.bare
        (paperFrozenEllipticSourceBox_of_conditions hcond)
        s.barrier.hχ s.pinnedStep_small s.Cmono_small hrouteCmono
        prev.data prev.pinned prev.facts.paperSuper d
      let facts := d.toRotheStepFacts s.hlam rest
      have hlower : ∀ x,
          lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D x ≤
            d.fixed.W x :=
        d.lowerRaw_of_old_lowerRaw hcond hD hD1 hu prev.pinned.lower
          s.hlam s.lowerRaw_small
      have hbare : InMonotoneWaveTrapSet (kappa c) 1 d.fixed.W :=
        d.monotoneTrap_of_rest rest facts.cont
      exact
        { old := prev.data.fixed.W
          data := d
          facts := facts
          pinned := ⟨hbare, hlower⟩ }

/-- The actual orbit, with the kinked upper barrier at time zero. -/
noncomputable def paperNegativePinnedRotheSeq
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ)
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    ℕ → ℝ → ℝ
  | 0 => upperBarrier (kappa c) 1
  | n + 1 => (paperNegativePinnedStepState hcond hD hD1 s u hu n).data.fixed.W

theorem paperNegativePinnedRotheSeq_stepFacts
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ)
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u)
    (n : ℕ) :
    PaperRotheStepFacts p c s.lam 1 (kappa c) s.Λ u
      (paperNegativePinnedRotheSeq hcond hD hD1 s u hu n)
      (paperNegativePinnedRotheSeq hcond hD hD1 s u hu (n + 1)) := by
  cases n with
  | zero =>
      exact (paperNegativePinnedStepState hcond hD hD1 s u hu 0).facts
  | succ n =>
      exact (paperNegativePinnedStepState hcond hD hD1 s u hu (n + 1)).facts

/-- Every positive-index state of the genuine orbit carries the same
logarithmic-slope bound.  This is a local Green-source estimate, not a
family-uniform spatial-tail assumption. -/
theorem paperNegativePinnedRotheSeq_succ_logSlope
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    (u : ℝ → ℝ)
    (hu : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    ∀ n x,
      |deriv (paperNegativePinnedRotheSeq hcond hD hD1 s u hu (n + 1)) x| ≤
        paperLowerPinnedStepLogSlopeCoeff c s.lam (kappa c)
            (negativeBranchTailCap p c) D 1 s.B *
          paperNegativePinnedRotheSeq hcond hD hD1 s u hu (n + 1) x := by
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  intro n x
  cases n with
  | zero =>
      let st := paperNegativePinnedStepState hcond hD hD1 s u hu 0
      simpa [paperNegativePinnedRotheSeq, st] using
        st.data.deriv_abs_le_mul_self_of_lowerPinned
          s.hlam s.hrpκ s.hrmκ s.hκ (sub_pos.mpr hcond.hgap)
          hDpos zero_le_one s.hB st.pinned x
  | succ n =>
      let st := paperNegativePinnedStepState hcond hD hD1 s u hu (n + 1)
      simpa [paperNegativePinnedRotheSeq, st] using
        st.data.deriv_abs_le_mul_self_of_lowerPinned
          s.hlam s.hrpκ s.hrmκ s.hκ (sub_pos.mpr hcond.hgap)
          hDpos zero_le_one s.hB st.pinned x

section AxiomAudit

#print axioms PaperLocalFixedStepData.toRotheStepFacts
#print axioms paperNegativePinnedLocalStep
#print axioms paperNegativePinnedStepState
#print axioms paperNegativePinnedRotheSeq_stepFacts
#print axioms paperNegativePinnedRotheSeq_succ_logSlope

end AxiomAudit

end ShenWork.Paper1
