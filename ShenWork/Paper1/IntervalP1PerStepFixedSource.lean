/-
  IntervalP1PerStepFixedSource

  Wiring brick for the Chen-Ruan-Shen Paper-1 per-step parabolic solver.

  `ShenWork/Paper1/WavePaperRotheProducer.lean` builds, axiom-clean and
  sorry-free, the full per-step truncated source-box data
  `paperTruncatedFixedSourceBoxData_of_trap` from trap membership together with
  a bundle of *scalar / parameter* side conditions.  That producer is, however,
  an orphan: nothing consumes it to discharge the carried
  `PaperStepFixedSourceExistsForSuperTrap` hypothesis — the genuine per-step
  nonlinear fixed-source existence that feeds Route A → `PaperRotheStepProducer`
  → `PaperGreenStepInput`.

  This file closes that wiring gap.  We package the `Z`-independent
  scalar/geometric data as `PerStepBoxParams`, and expose a per-`Z` provider
  `PerStepBoxZProvider` that hands back, for each trapped supersolution iterate
  `Z`, the already-built `PaperTruncatedFixedSourceBoxData` (constructed via
  `paperTruncatedFixedSourceBoxData_of_trap` with the `Z`-dependent regularity
  data in scope).  The theorem `paperStepFixedSourceExistsForSuperTrap_of_trap`
  then chains it into
  `PaperStepFixedSourceExistsForSuperTrap.of_truncated_sourceBox`.

  No new analytic content is introduced; this is the missing assembly that turns
  the carried per-step fixed-source existence into a theorem on trapped
  profiles, and a thin convenience wrapper that builds the box data inline from
  the full explicit scalar bundle.

  RESIDUAL / SATISFIABILITY BOUNDARY (honest accounting).
  `paperStepFixedSourceExistsForSuperTrap_of_params` discharges the per-step
  nonlinear *fixed-source existence* (trap invariance / `mapsTo` and source-box
  continuity are PROVEN inside `paperTruncatedFixedSourceBoxData_of_trap`).
  What remains carried, isolated cleanly ABOVE the closed existence layer:
    * the per-`Z` regularity witness `PerStepBoxZWitness` (a `PaperIterateBase`
      for the iterate, its exponential left rate, and Hölder absorption) — these
      hold along the Rothe orbit, where every iterate is a Green image and hence
      C² with bounded derivative; they are NOT claimed for arbitrary trapped
      barriers, exactly matching the orbit-satisfiable obligations the repo
      already carries via `PaperGreenStepInputRouteASuperRestProvider`;
    * the `PaperStepOutput` order/antitonicity layer (`hrest` in the capstone)
      — barrier comparison `W ≤ Z`, monotonicity, left-rate decay.
  The capstone `paperRotheStepProducer_of_params` relays these unchanged; it does
  not weaken or fake any obligation.
-/
import ShenWork.Paper1.WavePaperRouteA

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-- The `Z`-independent scalar / geometric data of the per-step truncated
source-box construction for a fixed frozen profile `u`.  Each field is exactly a
non-`Z` hypothesis of `paperTruncatedFixedSourceBoxData_of_trap`. -/
structure PerStepBoxParams
    (p : CMParams) (c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ)
    (u : ℝ → ℝ) : Prop where
  hlam : 0 < lam
  hrpκ : κ < greenRootPlus c lam
  hrmκ : κ < -greenRootMinus c lam
  hκ : 0 < κ
  hM : 0 < M
  hBnn : 0 ≤ B
  hBpos : 0 < B
  hsigma : 0 < sigma
  hsigma1 : sigma < 1
  hsigma_root : sigma < greenRootPlus c lam
  hCRnn : 0 ≤ C_R
  hUleft : M ≤ Real.exp (-κ * aL)
  hObsRight : 2 * (B * M) ≤ C_R
  hu : InMonotoneWaveTrapSet κ M u
  hu_rate : ExpLeftRate sigma aL C_u u L_u
  hsourceBound_eq : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M)
  hscalar :
    |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
          greenWeightedMass1 c lam κ * B
      + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
          + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
      + lam ≤ B
  hcontract :
    paperTruncatedNonlinearityRateClam p c lam M B sigma C_u +
        paperFixedSourceMapAZ lam * m_sigma < 1
  hCR :
    paperTruncatedNonlinearityRateD0 p c lam M B sigma C_u /
        (1 - (paperTruncatedNonlinearityRateClam p c lam M B sigma C_u +
          paperFixedSourceMapAZ lam * m_sigma)) ≤ C_R
  hbarrierScalar : PaperUpperBarrierSuperScalarConditions p c κ M
  hNL_M_nonpos :
    paperTruncatedLimitNonlinearity p M (L_u ^ p.γ) ≤ 0

/-- A per-`Z` provider of the already-assembled truncated source-box data.

For every trapped supersolution iterate `Z`, this hands back the
`PaperTruncatedFixedSourceBoxData` (with `Λ` and `M`, `κ` fixed by the params),
together with the agreement `H = box.H` so the box source-bound normalisation
`Λ = 2·δ⁻¹·(B·M)` matches `PerStepBoxParams.hsourceBound_eq`.  Callers build the
box via `paperTruncatedFixedSourceBoxData_of_trap`, which keeps the
`Z`-dependent regularity (`PaperIterateBase`, `ExpLeftRate Z`, Hölder
absorption, the reaction-contraction `C_chem`) local to that call. -/
def PerStepBoxZProvider
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
    (∀ x, 0 ≤ Z x) →
    (∀ x, Z x ≤ upperBarrier κ M x) →
    (∀ x, paperWaveOperator p c u Z x ≤ 0) →
      PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z

/-- Orbit-faithful fixed-source existence: the old iterate carries exactly the
regularity invariant produced at the preceding Rothe step.  Unlike
`PaperStepFixedSourceExistsForSuperTrap`, this does not quantify over arbitrary
continuous trapped supersolutions. -/
def PaperStepFixedSourceExistsForRegularSuperTrap
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M u →
  ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
    ∃ R : ℝ → ℝ,
      Continuous R ∧
      (∃ B : ℝ, (∀ y, |R y| ≤ B) ∧
        Λ = 2 * (greenDelta c lam)⁻¹ * B) ∧
      R = paperStepSource p c lam u Z
        (fun x => greenConv c lam R x)

/-- Repackage orbit-faithful fixed-source existence as the concrete Green
source consumed by Route A. -/
def PaperStepFixedSourceCore.of_existsForRegularSuperTrap
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hfixed : PaperStepFixedSourceExistsForRegularSuperTrap
      p c lam M κ Λ u)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperIterateBase p c κ M u Z) :
    PaperStepFixedSourceCore p c lam M κ Λ u Z :=
  let hex := hfixed hu Z hZ
  let R : ℝ → ℝ := Classical.choose hex
  have hRspec :
      Continuous R ∧
        (∃ B : ℝ, (∀ y, |R y| ≤ B) ∧
          Λ = 2 * (greenDelta c lam)⁻¹ * B) ∧
        R = paperStepSource p c lam u Z
          (fun x => greenConv c lam R x) :=
    Classical.choose_spec hex
  let B : ℝ := Classical.choose hRspec.2.1
  have hBspec : (∀ y, |R y| ≤ B) ∧
      Λ = 2 * (greenDelta c lam)⁻¹ * B :=
    Classical.choose_spec hRspec.2.1
  { R := R
    source_eq := hRspec.2.2
    R_cont := hRspec.1
    R_bound_const := B
    R_bound := hBspec.1
    R_bound_eq := hBspec.2 }

/-- Route-A comparison and antitonicity payload, quantified only over the
regular iterates that can actually occur in the Rothe orbit. -/
def PaperGreenStepInputRouteARegularRestProvider
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  ∀ Z : ℝ → ℝ, (hZ : PaperIterateBase p c κ M u Z) →
    (fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z) →
      PaperStepOutputRouteAFixedRestData p c lam M κ Λ u Z fixed

/-- Assemble exactly the orbit core from regular-iterate fixed-source
existence.  No all-continuous-profile regularity oracle is introduced. -/
def paperGreenStepInputRouteAOrbitCore_of_regularFixedSource
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hu : InMonotoneWaveTrapSet κ M u)
    (hlam : 0 < lam)
    (hbase : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hfixed : PaperStepFixedSourceExistsForRegularSuperTrap
      p c lam M κ Λ u)
    (hrest : PaperGreenStepInputRouteARegularRestProvider
      p c lam M κ Λ u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u where
  hlam := hlam
  basePaperSuper := hbase
  produce_regular := by
    intro Z hZ
    let fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z :=
      PaperStepFixedSourceCore.of_existsForRegularSuperTrap hfixed hu hZ
    exact (hrest Z hZ fixed).toOutputRouteACore hlam

/-- Regular-iterate fixed-source existence from the same validated truncated
weighted-Hölder source box.  The proof is the genuine source-box Schauder fixed
point plus clamp-inactivity argument, specialized to the orbit invariant. -/
theorem PaperStepFixedSourceExistsForRegularSuperTrap.of_truncated_sourceBox
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hdata : InMonotoneWaveTrapSet κ M u →
      ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
        PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z) :
    PaperStepFixedSourceExistsForRegularSuperTrap p c lam M κ Λ u := by
  intro hu Z hZ
  let hd : PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z :=
    hdata hu Z hZ
  obtain ⟨R, hRbox, hRfix⟩ := hd.exists_fixed
  have hIcc :
      ∀ x, (fun y => greenConv c lam R y) x ∈
        Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
    hd.truncation_inactive R hRbox hRfix
  have htrunc_eq :
      paperFixedSourceMap p c lam M κ u Z R =
        paperStepSource p c lam u Z (fun x => greenConv c lam R x) :=
    paperStepSource_truncated_eq_paperStepSource_of_Icc
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hd.hM_nonneg hIcc
  have hRbound_const : ∀ y, |R y| ≤ hd.B * M := by
    intro y
    calc
      |R y| ≤ hd.B * upperBarrier κ M y := hRbox.bound y
      _ ≤ hd.B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hd.B_nonneg
  refine ⟨R, hRbox.cont, ⟨hd.B * M, hRbound_const, hd.sourceBound_eq⟩, ?_⟩
  calc
    R = paperFixedSourceMap p c lam M κ u Z R := hRfix.symm
    _ = paperStepSource p c lam u Z (fun x => greenConv c lam R x) := htrunc_eq

/-- **Per-step fixed-source existence on a trapped profile.**

From a per-`Z` provider of truncated source-box data and the profile's
exponential left rate, the carried `PaperStepFixedSourceExistsForSuperTrap`
becomes a theorem.  This is the wiring that collapses the orphan
`paperTruncatedFixedSourceBoxData_of_trap` into the interface consumed by
Route A. -/
theorem paperStepFixedSourceExistsForSuperTrap_of_boxProvider
    {p : CMParams} {c lam M κ Λ sigma aL C_u L_u : ℝ} {u : ℝ → ℝ}
    (hu_rate : ExpLeftRate sigma aL C_u u L_u)
    (prov : PerStepBoxZProvider p c lam M κ Λ u) :
    PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u :=
  PaperStepFixedSourceExistsForSuperTrap.of_truncated_sourceBox
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
    (sigma := sigma) (aL := aL) (C_u := C_u) (L_u := L_u) (u := u)
    hu_rate
    (fun _hu _hu_rate Z hZc hZa hZ0 hZB hZsuper =>
      prov Z hZc hZa hZ0 hZB hZsuper)

/-- The per-`Z` regularity data the box construction needs for a given iterate
`Z`, beyond the trapped-supersolution facts: a Hölder radius `H`, a
reaction-contraction constant `C_chem`, the iterate's own `PaperIterateBase`
regularity, its exponential left rate (with the two-radius source constant), the
large-box obstacle absorption, the Hölder-kernel absorption, and the
reaction-step contraction smallness.  Packaged per `Z` so the `∀ Z` interface of
`PaperStepFixedSourceExistsForSuperTrap` can be discharged. -/
structure PerStepBoxZWitness
    (p : CMParams) (c lam M κ B sigma aL C_R m_sigma : ℝ) (u Z : ℝ → ℝ)
    (hlam : 0 < lam) (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam) (hκ : 0 < κ) (hM : 0 < M)
    (hBnn : 0 ≤ B) (hutrap : InWaveTrapSet κ M u) where
  H : ℝ
  C_chem : ℝ
  base : PaperIterateBase p c κ M u Z
  rate : ∃ LZ : ℝ,
    ExpLeftRate sigma aL (paperFixedSourceMapTwoRadiusCZ m_sigma C_R) Z LZ
  hH_obs : sourceObstacleHolderConst κ M B sigma C_R ≤ H
  hHolder_le :
    Classical.choose
      (paperFixedSourceMap_holder_kernel
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
        (u := u) (Z := Z)
        hlam hrpκ hrmκ hκ.le hM hBnn hutrap base) ≤ H
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1

/-- **Inline per-step box provider from the explicit scalar bundle.**

Builds `PerStepBoxZProvider` directly by calling
`paperTruncatedFixedSourceBoxData_of_trap` for each trapped supersolution
iterate `Z`, discharging the `Z`-dependent fields from a per-`Z`
`PerStepBoxZWitness`.  No carried fixed-source existence remains. -/
def perStepBoxZProvider_of_params
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap) :
    PerStepBoxZProvider p c lam M κ Λ u := by
  intro Z hZc hZa hZ0 hZB hZsuper
  let w := wit Z hZc hZa hZ0 hZB hZsuper
  exact
    paperTruncatedFixedSourceBoxData_of_trap
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      (B := B) (H := w.H) (C_chem := w.C_chem)
      (sigma := sigma) (aL := aL) (C_u := C_u) (L_u := L_u)
      (C_R := C_R) (m_sigma := m_sigma) (u := u) (Z := Z)
      params.hlam params.hrpκ params.hrmκ params.hκ params.hM
      params.hBnn params.hBpos params.hsigma params.hsigma1
      params.hsigma_root params.hCRnn params.hUleft params.hObsRight
      w.hH_obs params.hu params.hu_rate w.base w.rate
      params.hsourceBound_eq params.hscalar w.hHolder_le
      params.hcontract params.hCR w.hCB params.hbarrierScalar
      params.hNL_M_nonpos

/-- **Per-step fixed-source existence from the explicit scalar bundle.**

Composes `perStepBoxZProvider_of_params` with
`paperStepFixedSourceExistsForSuperTrap_of_boxProvider`: from the
`Z`-independent `PerStepBoxParams` and a per-`Z` `PerStepBoxZWitness`, the
carried `PaperStepFixedSourceExistsForSuperTrap` is a theorem. -/
theorem paperStepFixedSourceExistsForSuperTrap_of_params
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap) :
    PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u :=
  paperStepFixedSourceExistsForSuperTrap_of_boxProvider
    (sigma := sigma) (aL := aL) (C_u := C_u) (L_u := L_u)
    params.hu_rate (perStepBoxZProvider_of_params params wit)

/-- The explicit source-box construction on the satisfiable regular-iterate
interface.  Every regularity field is supplied by the preceding Rothe output;
the source-box proof itself is unchanged. -/
theorem paperStepFixedSourceExistsForRegularSuperTrap_of_params
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
      PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
        params.hlam params.hrpκ params.hrmκ params.hκ params.hM
        params.hBnn params.hu.trap) :
    PaperStepFixedSourceExistsForRegularSuperTrap p c lam M κ Λ u := by
  apply PaperStepFixedSourceExistsForRegularSuperTrap.of_truncated_sourceBox
  intro _hu Z hZ
  let w := wit Z hZ
  exact
    paperTruncatedFixedSourceBoxData_of_trap
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      (B := B) (H := w.H) (C_chem := w.C_chem)
      (sigma := sigma) (aL := aL) (C_u := C_u) (L_u := L_u)
      (C_R := C_R) (m_sigma := m_sigma) (u := u) (Z := Z)
      params.hlam params.hrpκ params.hrmκ params.hκ params.hM
      params.hBnn params.hBpos params.hsigma params.hsigma1
      params.hsigma_root params.hCRnn params.hUleft params.hObsRight
      w.hH_obs params.hu params.hu_rate hZ w.rate
      params.hsourceBound_eq params.hscalar w.hHolder_le
      params.hcontract params.hCR w.hCB params.hbarrierScalar
      params.hNL_M_nonpos

/-- The upper-barrier paper-supersolution from the scalar barrier conditions
carried in `PerStepBoxParams`. -/
theorem PerStepBoxParams.basePaperSuper
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u) :
    ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 :=
  paperUpperBarrier_super_of_scalar
    (p := p) (c := c) (κ := κ) (M := M) (u := u)
    params.hκ params.hbarrierScalar params.hu

/-- **Capstone: the full paper Rothe step producer from the explicit bundle.**

Chains `paperStepFixedSourceExistsForSuperTrap_of_params` into the Route-A
fixed-source assembly and `paperRotheStepProducer_of_routeA_greenCore`.  The
remaining input is the genuine per-step `PaperStepOutput` order/antitonicity
layer (`PaperGreenStepInputRouteASuperRestProvider`).  The inductive
supersolution precondition is already an argument of each `produce` call and is
threaded directly; it is not a separate all-profile residual. -/
theorem paperRotheStepProducer_of_params
    {p : CMParams} {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
        PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ params.hκ params.hM
          params.hBnn params.hu.trap)
    (hrest : PaperGreenStepInputRouteASuperRestProvider p c lam M κ Λ u) :
    PaperRotheStepProducer p c lam M κ Λ u :=
  paperRotheStepProducer_of_routeA_greenCore
    (paperGreenStepInputRouteACore_of_superCore
      (paperGreenStepInputRouteASuperCore_of_fixedSource
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ) (u := u)
        params.hu params.hlam params.basePaperSuper
        (paperStepFixedSourceExistsForSuperTrap_of_params params wit)
        hrest))

section AxiomAudit
#print axioms paperStepFixedSourceExistsForSuperTrap_of_boxProvider
#print axioms PaperStepFixedSourceExistsForRegularSuperTrap.of_truncated_sourceBox
#print axioms PaperStepFixedSourceCore.of_existsForRegularSuperTrap
#print axioms paperGreenStepInputRouteAOrbitCore_of_regularFixedSource
#print axioms perStepBoxZProvider_of_params
#print axioms paperStepFixedSourceExistsForSuperTrap_of_params
#print axioms paperStepFixedSourceExistsForRegularSuperTrap_of_params
#print axioms PerStepBoxParams.basePaperSuper
#print axioms paperRotheStepProducer_of_params
end AxiomAudit

end ShenWork.Paper1
