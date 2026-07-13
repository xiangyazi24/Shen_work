import ShenWork.Paper1.WaveControlledRouteA
import ShenWork.Paper1.WaveControlledStepWitness

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- The actual invariant required by the weighted whole-line source box.  In
contrast to the qualitative `PaperIterateBase`, the constants `sigma`, `aL`, and `C`
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
        { output := (out.toOutputRouteACore params.hlam).2
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
  exact
    { step_op := hstep
      cont := hbasic.1
      diff := hbasic.2.1
      contDiff2 := paperStep_contDiff_two_of_core hlam hout.output.analytic
      deriv_le := hbasic.2.2
      nonneg := hout.output.nonneg
      le_barrier := hout.output.le_barrier
      le_old := hout.output.le_old
      anti := hout.output.anti
      paperSuper :=
        paperWaveOperator_nonpos_of_implicitStep_le
          (p := p) (c := c) (lam := lam) (u := u) (Z := Z) (W := W)
          hlam hstep hout.output.le_old }

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

def rotheSeqOfPaperSharedRate_stepAnalytic
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    PaperStepAnalytic p c lam M κ Λ u
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k)
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core (k + 1)) :=
  paperStepAnalytic_of_core core.hlam
    (paperSharedRateOutputAt
      p c lam M κ Λ sigma aL C u core k).2.output.analytic

theorem rotheSeqOfPaperSharedRate_shared_rate
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    ∃ ell : ℝ, ExpLeftRate sigma aL C
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k) ell :=
  (paperSharedRateRotheStep p c lam M κ Λ sigma aL C u core k).2.rate

theorem rotheSeqOfPaperSharedRate_base
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    PaperSharedRateIterateBase p c κ M sigma aL C u
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k) :=
  (paperSharedRateRotheStep p c lam M κ Λ sigma aL C u core k).2

theorem rotheSeqOfPaperSharedRate_cont
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    Continuous (rotheSeqOfPaperSharedRate
      p c lam M κ Λ sigma aL C u core k) :=
  (rotheSeqOfPaperSharedRate_base core k).base.cont

theorem rotheSeqOfPaperSharedRate_anti_x
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) :
    Antitone (rotheSeqOfPaperSharedRate
      p c lam M κ Λ sigma aL C u core k) :=
  (rotheSeqOfPaperSharedRate_base core k).base.anti

theorem rotheSeqOfPaperSharedRate_nonneg
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) (x : ℝ) :
    0 ≤ rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k x :=
  (rotheSeqOfPaperSharedRate_base core k).base.nonneg x

theorem rotheSeqOfPaperSharedRate_le_barrier
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) (x : ℝ) :
    rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k x ≤
      upperBarrier κ M x :=
  (rotheSeqOfPaperSharedRate_base core k).base.le_barrier x

theorem rotheSeqOfPaperSharedRate_le_M
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) (x : ℝ) :
    rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k x ≤ M :=
  le_trans (rotheSeqOfPaperSharedRate_le_barrier core k x)
    (upperBarrier_le_M κ M x)

theorem rotheSeqOfPaperSharedRate_succ_le
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (k : ℕ) (x : ℝ) :
    rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core (k + 1) x ≤
      rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k x :=
  (rotheSeqOfPaperSharedRate_stepFacts core k).le_old x

theorem rotheSeqOfPaperSharedRate_anti_k
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (x : ℝ) :
    Antitone (fun k =>
      rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k x) :=
  antitone_nat_of_succ_le (fun k => rotheSeqOfPaperSharedRate_succ_le core k x)

theorem rotheSeqOfPaperSharedRate_bddBelow
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u) (x : ℝ) :
    BddBelow (Set.range (fun k =>
      rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k x)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact rotheSeqOfPaperSharedRate_nonneg core k x

theorem rotheSeqOfPaperSharedRate_succ_lipschitz
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u)
    (hΛ : 0 ≤ Λ) (k : ℕ) (x y : ℝ) :
    |rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core (k + 1) x -
        rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core (k + 1) y| ≤
      Λ * |x - y| := by
  have hfacts := rotheSeqOfPaperSharedRate_stepFacts core k
  have hLip : LipschitzWith (Real.toNNReal Λ)
      (rotheSeqOfPaperSharedRate
        p c lam M κ Λ sigma aL C u core (k + 1)) :=
    crossImplicitStep_lipschitz hΛ hfacts.diff hfacts.deriv_le
  have h := hLip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ] at h
  exact h

theorem rotheSeqOfPaperSharedRate_equiLip
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    (k : ℕ) (x y : ℝ) :
    |rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k x -
        rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core k y| ≤
      L * |x - y| := by
  cases k with
  | zero => simpa using hbarLip x y
  | succ k =>
      exact le_trans (rotheSeqOfPaperSharedRate_succ_lipschitz
        core hΛ0 k x y)
        (mul_le_mul_of_nonneg_right hΛL (abs_nonneg _))

theorem rotheSeqOfPaperSharedRate_limitLip
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|)
    (x y : ℝ) :
    |rotheLimit (rotheSeqOfPaperSharedRate
          p c lam M κ Λ sigma aL C u core) x -
        rotheLimit (rotheSeqOfPaperSharedRate
          p c lam M κ Λ sigma aL C u core) y| ≤ L * |x - y| := by
  let z := rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core
  have hx : Tendsto (fun k => z k x) atTop (𝓝 (rotheLimit z x)) :=
    rotheLimit_tendsto (rotheSeqOfPaperSharedRate_anti_k core)
      (rotheSeqOfPaperSharedRate_bddBelow core) x
  have hy : Tendsto (fun k => z k y) atTop (𝓝 (rotheLimit z y)) :=
    rotheLimit_tendsto (rotheSeqOfPaperSharedRate_anti_k core)
      (rotheSeqOfPaperSharedRate_bddBelow core) y
  have ht := (hx.sub hy).abs
  refine le_of_tendsto ht ?_
  exact Eventually.of_forall fun k =>
    rotheSeqOfPaperSharedRate_equiLip core hΛ0 hΛL hbarLip k x y

theorem paperSharedRate_orbitData
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|) :
    PaperRotheOrbitDataWithModulus p c lam M κ L
      (rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core) :=
  { iterate_cont := rotheSeqOfPaperSharedRate_cont core
    anti_k := rotheSeqOfPaperSharedRate_anti_k core
    anti_x := rotheSeqOfPaperSharedRate_anti_x core
    nonneg := rotheSeqOfPaperSharedRate_nonneg core
    le_M := rotheSeqOfPaperSharedRate_le_M core
    le_upperBarrier := rotheSeqOfPaperSharedRate_le_barrier core
    bddBelow := rotheSeqOfPaperSharedRate_bddBelow core
    equiLip := rotheSeqOfPaperSharedRate_equiLip core hΛ0 hΛL hbarLip
    limitLip := rotheSeqOfPaperSharedRate_limitLip core hΛ0 hΛL hbarLip }

/-- The common exponential left rate passes to the long-time limit without a
family-uniform time tail.  Only the one-orbit local-uniform convergence and
compactness of the scalar limit interval are used. -/
theorem paperSharedRate_rotheLimit_rate
    (core : PaperGreenStepInputRouteASharedRateOrbitCore
      p c lam M κ Λ sigma aL C u)
    (hL : 0 ≤ L)
    (hΛ0 : 0 ≤ Λ) (hΛL : Λ ≤ L)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ L * |x - y|) :
    ∃ ell : ℝ, ell ∈ Icc (0 : ℝ) M ∧
      ExpLeftRate sigma aL C
        (rotheLimit (rotheSeqOfPaperSharedRate
          p c lam M κ Λ sigma aL C u core)) ell := by
  let z := rotheSeqOfPaperSharedRate p c lam M κ Λ sigma aL C u core
  let ellSeq : ℕ → ℝ := fun k =>
    Classical.choose (rotheSeqOfPaperSharedRate_shared_rate core k)
  have hellRate : ∀ k, ExpLeftRate sigma aL C (z k) (ellSeq k) :=
    fun k => Classical.choose_spec (rotheSeqOfPaperSharedRate_shared_rate core k)
  have hellMem : ∀ k, ellSeq k ∈ Icc (0 : ℝ) M := by
    intro k
    exact ExpLeftRate.limit_mem_Icc core.hsigma (hellRate k)
      (rotheSeqOfPaperSharedRate_nonneg core k)
      (rotheSeqOfPaperSharedRate_le_M core k)
  obtain ⟨ell, hell, sub, hsub, hellConv⟩ :=
    isCompact_Icc.tendsto_subseq hellMem
  let hdata := paperSharedRate_orbitData core hΛ0 hΛL hbarLip
  have hzConv : LocallyUniformConverges (fun n => z (sub n)) (rotheLimit z) := by
    simpa [z] using (hdata.locallyUniform hL).comp_strictMono hsub
  refine ⟨ell, hell, ?_⟩
  intro x
  have htend : Tendsto
      (fun n => |z (sub n) x - ellSeq (sub n)|) atTop
      (𝓝 (|rotheLimit z x - ell|)) :=
    ((hzConv.tendsto_at x).sub hellConv).abs
  refine le_of_tendsto htend ?_
  exact Eventually.of_forall fun n => hellRate (sub n) x

section AxiomAudit

#print axioms paperSharedRateRouteACore_of_params
#print axioms paperRotheStepFacts_of_sharedRate_output
#print axioms paperSharedRateRotheStep
#print axioms rotheSeqOfPaperSharedRate_stepFacts
#print axioms rotheSeqOfPaperSharedRate_stepAnalytic
#print axioms rotheSeqOfPaperSharedRate_shared_rate
#print axioms PaperRotheOrbitDataWithModulus.locallyUniform
#print axioms paperSharedRate_orbitData
#print axioms paperSharedRate_rotheLimit_rate

end AxiomAudit

end ShenWork.Paper1
