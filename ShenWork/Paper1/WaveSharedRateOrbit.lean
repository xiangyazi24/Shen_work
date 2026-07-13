import ShenWork.Paper1.WaveControlledRouteA
import ShenWork.Paper1.WaveControlledStepWitness

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- The actual invariant required by the weighted whole-line source box.  In
contrast to `PaperIterateBase.left_rate`, the constants `sigma`, `aL`, and `C`
are shared by the whole orbit. -/
structure PaperSharedRateIterateBase
    (p : CMParams) (c κ M sigma aL C : ℝ)
    (u Z : ℝ → ℝ) : Prop where
  base : PaperIterateBase p c κ M u Z
  rate : ∃ ell : ℝ, ExpLeftRate sigma aL C Z ell

/-- Route-A data needed only along the shared-rate recursion.  This is the
orbit-faithful replacement for a provider quantified over every regular
profile, whose arbitrary existential rate cannot be changed to prescribed
constants. -/
def PaperGreenStepInputRouteASharedRateRestProvider
    (p : CMParams) (c lam M κ Λ sigma aL C : ℝ)
    (u : ℝ → ℝ) : Type :=
  ∀ Z : ℝ → ℝ,
    (hZ : PaperSharedRateIterateBase p c κ M sigma aL C u Z) →
    (fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z) →
      PaperStepOutputRouteAFixedRestData p c lam M κ Λ u Z fixed

/-- A Route-A orbit core whose producer is restricted to the quantitative
invariant that its own outputs preserve. -/
structure PaperGreenStepInputRouteASharedRateOrbitCore
    (p : CMParams) (c lam M κ Λ sigma aL C : ℝ)
    (u : ℝ → ℝ) where
  hlam : 0 < lam
  hsigma : 0 < sigma
  initial : PaperSharedRateIterateBase
    p c κ M sigma aL C u (upperBarrier κ M)
  produce : ∀ Z : ℝ → ℝ,
    PaperSharedRateIterateBase p c κ M sigma aL C u Z →
      Σ' W : ℝ → ℝ,
        PaperStepOutputRouteAQuantitativeCore
          p c lam M κ Λ sigma aL C u Z W

/-- Assemble the genuine shared-rate Green core from the source-box scalar
bundle.  All `PerStepBoxZWitness` fields are now internal.  The two displayed
radius inequalities say precisely that the common two-radius constant absorbs
the upper-barrier seed and every Green successor. -/
noncomputable def paperSharedRateRouteACore_of_params
    {p : CMParams}
    {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params :
      PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (hreact : (1 / lam) * reactionLip p.α M < 1)
    (hseed : 2 * M ≤ paperFixedSourceMapTwoRadiusCZ m_sigma C_R)
    (hstep : paperControlledStepRateConst c lam sigma B M C_R ≤
      paperFixedSourceMapTwoRadiusCZ m_sigma C_R)
    (hrest : PaperGreenStepInputRouteASharedRateRestProvider
      p c lam M κ Λ sigma aL
        (paperFixedSourceMapTwoRadiusCZ m_sigma C_R) u) :
    PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL
        (paperFixedSourceMapTwoRadiusCZ m_sigma C_R) u where
  hlam := params.hlam
  hsigma := params.hsigma
  initial := by
    refine
      { base := upperBarrier_paperIterateBase params.hκ.le params.hM.le
          params.basePaperSuper
        rate := ?_ }
    refine ⟨M, ExpLeftRate.mono_C hseed ?_⟩
    exact upperBarrier_expLeftRate_of_left_plateau
      params.hsigma params.hκ.le params.hM.le params.hUleft
  produce := by
    intro Z hZ
    let wit := perStepBoxZWitness_of_quantitative_rate
      params hZ.base hZ.rate hreact
    let q := paperStepFixedSourceQuantitativeCore_of_params params wit
    let out := hrest Z hZ q.fixed
    exact
      ⟨q.fixed.W,
        { output := out.toOutputRouteACore.2
          ell := q.ell
          rate := ExpLeftRate.mono_C hstep q.W_rate }⟩

/-- The ordinary paper-step facts extracted from a quantitative Route-A
output.  Unlike the legacy extractor, this needs no fictitious producer on all
`PaperIterateBase`s. -/
def paperRotheStepFacts_of_sharedRate_output
    {p : CMParams} {c lam M κ Λ sigma aL C : ℝ}
    {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hsigma : 0 < sigma)
    (hout : PaperStepOutputRouteAQuantitativeCore
      p c lam M κ Λ sigma aL C u Z W) :
    PaperRotheStepFacts p c lam M κ Λ u Z W := by
  have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
    smooth_paperStep_step_op_of_core hlam hout.output.analytic
  have hbasic :
      Continuous W ∧ Differentiable ℝ W ∧ ∀ x, |deriv W x| ≤ Λ :=
    smooth_paperStep_basic_regular_of_core hlam hout.output.analytic
  have hnonneg : ∀ x, 0 ≤ W x := by
    have hle := paperStep_ge_lower
      (c := c) (lam := lam) hlam hstep hout.output.lowerZero
    exact fun x => hle x
  have hle_old : ∀ x, W x ≤ Z x :=
    paperStep_le_upper (c := c) (lam := lam) hlam hstep hout.output.upperOld
  have hle_barrier : ∀ x, W x ≤ upperBarrier κ M x :=
    paperStep_le_upper
      (c := c) (lam := lam) hlam hstep hout.output.upperBarrier
  exact
    { step_op := hstep
      cont := hbasic.1
      diff := hbasic.2.1
      contDiff2 := paperStep_contDiff_two_of_core hlam hout.output.analytic
      deriv_le := hbasic.2.2
      left_rate := ⟨sigma, aL, C, hout.ell, hsigma, hout.rate⟩
      nonneg := hnonneg
      le_barrier := hle_barrier
      le_old := hle_old
      anti := paperStep_antitone_of_trap_via_mollification hlam hout.output.approx
      paperSuper :=
        paperWaveOperator_nonpos_of_implicitStep_le
          (p := p) (c := c) (lam := lam) (u := u) (Z := Z) (W := W)
          hlam hstep hle_old }

/-- The dependent Rothe recursion on the true quantitative invariant. -/
def paperSharedRateRotheStep
    (p : CMParams) (c lam M κ Λ sigma aL C : ℝ) (u : ℝ → ℝ)
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) :
    ∀ _k : ℕ, {Z : ℝ → ℝ //
      PaperSharedRateIterateBase p c κ M sigma aL C u Z}
  | 0 => ⟨upperBarrier κ M, core.initial⟩
  | k + 1 =>
      let prev := paperSharedRateRotheStep
        p c lam M κ Λ sigma aL C u core k
      let out := core.produce prev.1 prev.2
      ⟨out.1,
        { base := (paperRotheStepFacts_of_sharedRate_output
            core.hlam core.hsigma out.2).toBase
          rate := ⟨out.2.ell, out.2.rate⟩ }⟩

def rotheSeqOfPaperSharedRate
    (p : CMParams) (c lam M κ Λ sigma aL C : ℝ) (u : ℝ → ℝ)
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) : ℕ → ℝ → ℝ :=
  fun k => (paperSharedRateRotheStep
    p c lam M κ Λ sigma aL C u core k).1

def paperSharedRateOutputAt
    (p : CMParams) (c lam M κ Λ sigma aL C : ℝ) (u : ℝ → ℝ)
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    Σ' W : ℝ → ℝ,
      PaperStepOutputRouteAQuantitativeCore
        p c lam M κ Λ sigma aL C u
          (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k) W :=
  core.produce
    (paperSharedRateRotheStep p c lam M κ Λ sigma aL C u core k).1
    (paperSharedRateRotheStep p c lam M κ Λ sigma aL C u core k).2

@[simp] theorem rotheSeqOfPaperSharedRate_zero
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) :
    rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core 0 =
      upperBarrier κ M := rfl

theorem rotheSeqOfPaperSharedRate_stepFacts
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    PaperRotheStepFacts p c lam M κ Λ u
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k)
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core (k + 1)) := by
  exact paperRotheStepFacts_of_sharedRate_output core.hlam core.hsigma
    (paperSharedRateOutputAt p c lam M κ Λ sigma aL C u core k).2

theorem rotheSeqOfPaperSharedRate_shared_rate
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    ∃ ell : ℝ, ExpLeftRate sigma aL C
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k) ell :=
  (paperSharedRateRotheStep p c lam M κ Λ sigma aL C u core k).2.rate

section AxiomAudit

#print axioms paperSharedRateRouteACore_of_params
#print axioms paperRotheStepFacts_of_sharedRate_output
#print axioms paperSharedRateRotheStep
#print axioms rotheSeqOfPaperSharedRate_stepFacts
#print axioms rotheSeqOfPaperSharedRate_shared_rate

end AxiomAudit

end ShenWork.Paper1
