import ShenWork.Paper1.WaveControlledModulusTrap
import ShenWork.Paper1.WaveLemma42ParamCore

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Uniform exponential left-rate constant of the Green profile selected by a
single source-box fixed point. -/
def paperControlledStepRateConst
    (c lam sigma B M C_R : ℝ) : ℝ :=
  greenKernelExpMoment c lam sigma *
    (paperFixedSourceMapExpOmegaRadius C_R + 2 * (B * M))

/-- Fixed source together with the quantitative left rate of its Green
profile.  The legacy fixed-source interface retained only an existential
`ExpLeftRateData`; this payload keeps the common constants needed by the
compact controlled outer trap. -/
structure PaperStepFixedSourceQuantitativeCore
    (p : CMParams) (c lam M κ Λ sigma aL C_W : ℝ)
    (u Z : ℝ → ℝ) where
  fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z
  ell : ℝ
  W_rate : ExpLeftRate sigma aL C_W fixed.W ell

/-- The source-box Schauder fixed point, without erasing its quantitative
exponential left tail. -/
noncomputable def paperStepFixedSourceQuantitativeCore_of_params
    {p : CMParams}
    {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u Z : ℝ → ℝ}
    (params :
      PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (w : PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
      params.hlam params.hrpκ params.hrmκ params.hκ params.hM
      params.hBnn params.hu.trap) :
    PaperStepFixedSourceQuantitativeCore p c lam M κ Λ sigma aL
      (paperControlledStepRateConst c lam sigma B M C_R) u Z := by
  let hd : PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z :=
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
  let R : ℝ → ℝ := Classical.choose hd.exists_fixed
  have hRspec :
      PaperWeightedHolderSourceBox κ M hd.beta hd.B hd.H hd.omega R ∧
        paperFixedSourceMap p c lam M κ u Z R = R :=
    Classical.choose_spec hd.exists_fixed
  have hRbox :
      PaperWeightedHolderSourceBox κ M hd.beta hd.B hd.H hd.omega R :=
    hRspec.1
  have hRfix : paperFixedSourceMap p c lam M κ u Z R = R := hRspec.2
  have hIcc : ∀ x, (fun y => greenConv c lam R y) x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
    hd.truncation_inactive R hRbox hRfix
  have htrunc_eq :
      paperFixedSourceMap p c lam M κ u Z R =
        paperStepSource p c lam u Z (fun x => greenConv c lam R x) :=
    paperStepSource_truncated_eq_paperStepSource_of_Icc
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hd.hM_nonneg hIcc
  have hRbound : ∀ y, |R y| ≤ B * M := by
    intro y
    simpa [hd, paperTruncatedFixedSourceBoxData_of_trap] using
      hRbox.abs_le_const params.hBnn y
  let fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z :=
    { R := R
      source_eq := by
        calc
          R = paperFixedSourceMap p c lam M κ u Z R := hRfix.symm
          _ = paperStepSource p c lam u Z
              (fun x => greenConv c lam R x) := htrunc_eq
      R_cont := hRbox.cont
      R_bound_const := B * M
      R_bound := hRbound
      R_bound_eq := params.hsourceBound_eq }
  let ellR : ℝ := Classical.choose hRbox.leftTail
  have hellR : Tendsto R atBot (𝓝 ellR) :=
    Classical.choose_spec hRbox.leftTail
  have hK : 0 ≤ paperFixedSourceMapExpOmegaRadius C_R := by
    dsimp [paperFixedSourceMapExpOmegaRadius]
    linarith [params.hCRnn]
  have hRrate : ExpLeftRate sigma aL
      (paperFixedSourceMapExpOmegaRadius C_R + 2 * (B * M)) R ellR :=
    leftTailCauchy_to_ExpLeftRate_of_tendsto
      params.hsigma hK (mul_nonneg params.hBnn params.hM.le)
      hRbound hellR
      (by
        intro A _hA x y hx hy
        simpa [hd, paperTruncatedFixedSourceBoxData_of_trap,
          expLeftOmega] using hRbox.leftTailCauchy A x y hx hy)
  have hWrate : ExpLeftRate sigma aL
      (paperControlledStepRateConst c lam sigma B M C_R)
      (greenConv c lam R) (ellR * lam⁻¹) := by
    simpa [paperControlledStepRateConst] using
      greenConv_expLeftRate (c := c) (lam := lam)
        params.hlam params.hsigma.le params.hsigma_root hRbox.cont
        hRbound hRrate
  exact
    { fixed := fixed
      ell := ellR * lam⁻¹
      W_rate := by simpa [fixed, PaperStepFixedSourceCore.W] using hWrate }

/-- One Route-A output together with a quantitative left-rate witness. -/
structure PaperStepOutputRouteAQuantitativeCore
    (p : CMParams) (c lam M κ Λ sigma aL C_W : ℝ)
    (u Z W : ℝ → ℝ) where
  output : PaperStepOutputRouteACore p c lam M κ Λ u Z W
  ell : ℝ
  rate : ExpLeftRate sigma aL C_W W ell

/-- A Route-A Green orbit core that retains a shared quantitative left-rate
constant at every successor. -/
structure PaperGreenStepInputRouteAQuantitativeOrbitCore
    (p : CMParams) (c lam M κ Λ sigma aL C_W : ℝ)
    (u : ℝ → ℝ) where
  hlam : 0 < lam
  basePaperSuper : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0
  produce_regular : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
    Σ' W : ℝ → ℝ,
      PaperStepOutputRouteAQuantitativeCore
        p c lam M κ Λ sigma aL C_W u Z W

namespace PaperGreenStepInputRouteAQuantitativeOrbitCore

def toOrbitCore
    {p : CMParams} {c lam M κ Λ sigma aL C_W : ℝ}
    {u : ℝ → ℝ}
    (h : PaperGreenStepInputRouteAQuantitativeOrbitCore
      p c lam M κ Λ sigma aL C_W u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u where
  hlam := h.hlam
  basePaperSuper := h.basePaperSuper
  produce_regular := fun Z hZ =>
    ⟨(h.produce_regular Z hZ).1, (h.produce_regular Z hZ).2.output⟩

theorem successor_rate
    {p : CMParams} {c lam M κ Λ sigma aL C_W : ℝ}
    {u : ℝ → ℝ}
    (h : PaperGreenStepInputRouteAQuantitativeOrbitCore
      p c lam M κ Λ sigma aL C_W u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    ∃ ell : ℝ, ExpLeftRate sigma aL C_W
      (rotheSeqOfPaperRouteA p c lam M κ Λ u h.toOrbitCore hκ hM (k + 1))
      ell := by
  change ∃ ell, ExpLeftRate sigma aL C_W
    ((h.produce_regular
      (paperRouteARotheStep p c lam M κ Λ u h.toOrbitCore hκ hM k).1
      (paperRouteARotheStep p c lam M κ Λ u h.toOrbitCore hκ hM k).2).1) ell
  exact ⟨(h.produce_regular _ _).2.ell, (h.produce_regular _ _).2.rate⟩

/-- Direct orbit data for one quantitative core, without totalizing over a
larger bare trap. -/
theorem orbitData
    {p : CMParams} {c lam M κ Λ sigma aL C_W : ℝ}
    {u : ℝ → ℝ}
    (h : PaperGreenStepInputRouteAQuantitativeOrbitCore
      p c lam M κ Λ sigma aL C_W u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperRotheOrbitData p c lam M κ
      (fun _ => rotheSeqOfPaperRouteA p c lam M κ Λ u
        h.toOrbitCore hκ hM) u := by
  let z := rotheSeqOfPaperRouteA p c lam M κ Λ u h.toOrbitCore hκ hM
  refine
    { iterate_cont := ?_
      anti_k := ?_
      anti_x := ?_
      nonneg := ?_
      le_M := ?_
      le_upperBarrier := ?_
      bddBelow := ?_
      equiLip := ?_
      limitLip := ?_ }
  · simpa [z] using rotheSeqOfPaperRouteA_cont h.toOrbitCore hκ hM
  · simpa [z] using rotheSeqOfPaperRouteA_anti_k h.toOrbitCore hκ hM
  · simpa [z] using rotheSeqOfPaperRouteA_anti_x h.toOrbitCore hκ hM
  · simpa [z] using rotheSeqOfPaperRouteA_nonneg h.toOrbitCore hκ hM
  · simpa [z] using rotheSeqOfPaperRouteA_le_M h.toOrbitCore hκ hM
  · simpa [z] using rotheSeqOfPaperRouteA_le_barrier h.toOrbitCore hκ hM
  · simpa [z] using rotheSeqOfPaperRouteA_bddBelow h.toOrbitCore hκ hM
  · simpa [z] using
      rotheSeqOfPaperRouteA_equiLip h.toOrbitCore hκ hM
        hΛ0 hΛM hbarLip
  · intro x y
    simpa [z] using
      rotheSeqOfPaperRouteA_limitLip h.toOrbitCore hκ hM
        hΛ0 hΛM hbarLip x y

/-- Shared successor rates pass to the long-time Rothe limit.  The left limit
may vary with the successor, so it is selected in the compact interval
`[0,M]`; local-uniform convergence then passes the quantitative estimate. -/
theorem rotheLimit_rate
    {p : CMParams} {c lam M κ Λ sigma aL C_W : ℝ}
    {u : ℝ → ℝ}
    (h : PaperGreenStepInputRouteAQuantitativeOrbitCore
      p c lam M κ Λ sigma aL C_W u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hsigma : 0 < sigma) :
    ∃ ell : ℝ, ell ∈ Icc (0 : ℝ) M ∧
      ExpLeftRate sigma aL C_W
        (rotheLimit (rotheSeqOfPaperRouteA p c lam M κ Λ u
          h.toOrbitCore hκ hM)) ell := by
  let z := rotheSeqOfPaperRouteA p c lam M κ Λ u h.toOrbitCore hκ hM
  let ellSeq : ℕ → ℝ := fun k =>
    Classical.choose (h.successor_rate hκ hM k)
  have hellRate : ∀ k,
      ExpLeftRate sigma aL C_W (z (k + 1)) (ellSeq k) := by
    intro k
    exact Classical.choose_spec (h.successor_rate hκ hM k)
  have hellMem : ∀ k, ellSeq k ∈ Icc (0 : ℝ) M := by
    intro k
    exact ExpLeftRate.limit_mem_Icc hsigma (hellRate k)
      (rotheSeqOfPaperRouteA_nonneg h.toOrbitCore hκ hM (k + 1))
      (rotheSeqOfPaperRouteA_le_M h.toOrbitCore hκ hM (k + 1))
  obtain ⟨ell, hell, sub, hsub, hellConv⟩ :=
    isCompact_Icc.tendsto_subseq hellMem
  have hzConv : LocallyUniformConverges
      (fun n => z (sub n + 1)) (rotheLimit z) := by
    have horbit : LocallyUniformConverges z (rotheLimit z) := by
      let hdata := h.orbitData hκ hM hΛ0 hΛM hbarLip
      simpa [z] using hdata.locallyUniform hM
    exact horbit.comp_strictMono (hsub.add_const 1)
  have hlimitRate : ExpLeftRate sigma aL C_W (rotheLimit z) ell := by
    intro x
    have htend : Tendsto
        (fun n => |z (sub n + 1) x - ellSeq (sub n)|) atTop
        (𝓝 (|rotheLimit z x - ell|)) :=
      ((hzConv.tendsto_at x).sub hellConv).abs
    refine le_of_tendsto htend ?_
    exact Eventually.of_forall fun n => hellRate (sub n) x
  exact ⟨ell, hell, by simpa [z] using hlimitRate⟩

end PaperGreenStepInputRouteAQuantitativeOrbitCore

/-- Build the quantitative Route-A core from the explicit source-box
parameters and the existing comparison/Route-A remainder. -/
def paperRouteAQuantitativeCore_of_params
    {p : CMParams}
    {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params :
      PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (wit : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
      PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
        params.hlam params.hrpκ params.hrmκ params.hκ params.hM
        params.hBnn params.hu.trap)
    (hrest : PaperGreenStepInputRouteARegularRestProvider
      p c lam M κ Λ u) :
    PaperGreenStepInputRouteAQuantitativeOrbitCore p c lam M κ Λ sigma aL
      (paperControlledStepRateConst c lam sigma B M C_R) u where
  hlam := params.hlam
  basePaperSuper := params.basePaperSuper
  produce_regular := by
    intro Z hZ
    let q := paperStepFixedSourceQuantitativeCore_of_params params (wit Z hZ)
    let out := hrest Z hZ q.fixed
    exact ⟨q.fixed.W,
      { output := out.toOutputRouteACore.2
        ell := q.ell
        rate := q.W_rate }⟩

/-- Per-profile lower-raw producer on the corrected controlled trap. -/
structure PaperControlledLowerRawStepProducer
    (p : CMParams) (c lam M κ κtilde D Λ sigma aL C : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (u : ℝ → ℝ) where
  core : PaperGreenStepInputRouteAQuantitativeOrbitCore
    p c lam M κ Λ sigma aL C u
  lowerRawAux : ∀ k,
    (∀ x, lowerBarrierRaw κ κtilde D x ≤
      rotheSeqOfPaperRouteA p c lam M κ Λ u core.toOrbitCore hκ hM k x) →
      ∃ C_chem La Lb,
        PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
          (rotheSeqOfPaperRouteA p c lam M κ Λ u
            core.toOrbitCore hκ hM (k + 1))

/-- The corrected lower-raw floor quantifies only over the compact controlled
parameter trap.  This replaces the formally empty bare-trap floor. -/
structure PaperControlledLowerRawFloor
    (p : CMParams) (c lam M κ κtilde D Λ sigma aL C : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer : ∀ u,
    InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u →
    PaperControlledLowerRawStepProducer
      p c lam M κ κtilde D Λ sigma aL C hκ hM u

/-- Total Rothe sequence for the controlled Schauder map. -/
def paperControlledLowerRawRotheSeq
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => by
    classical
    exact if hu : InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) u then
      rotheSeqOfPaperRouteA p c lam M κ Λ u
        (floor.producer u hu).core.toOrbitCore hκ hM
    else fun _ => upperBarrier κ M

@[simp] theorem paperControlledLowerRawRotheSeq_eq
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    {u : ℝ → ℝ}
    (hu : InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u) :
    paperControlledLowerRawRotheSeq floor u =
      rotheSeqOfPaperRouteA p c lam M κ Λ u
        (floor.producer u hu).core.toOrbitCore hκ hM := by
  simp [paperControlledLowerRawRotheSeq, hu]

theorem paperControlledLowerRaw_orbitData
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    {u : ℝ → ℝ}
    (hu : InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u) :
    PaperRotheOrbitData p c lam M κ
      (paperControlledLowerRawRotheSeq floor) u := by
  let hd := (floor.producer u hu).core.orbitData
    hκ hM hΛ0 hΛM hbarLip
  refine
    { iterate_cont := ?_
      anti_k := ?_
      anti_x := ?_
      nonneg := ?_
      le_M := ?_
      le_upperBarrier := ?_
      bddBelow := ?_
      equiLip := ?_
      limitLip := ?_ }
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.iterate_cont
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.anti_k
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.anti_x
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.nonneg
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.le_M
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using
      hd.le_upperBarrier
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.bddBelow
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.equiLip
  · simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hd.limitLip

theorem paperControlledLowerRaw_stepLowerInvariant
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
      (paperControlledLowerRawRotheSeq floor) := by
  intro u hu k hprev
  by_cases huControlled :
      InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) u
  · let prod := floor.producer u huControlled
    rw [paperControlledLowerRawRotheSeq_eq floor huControlled] at hprev ⊢
    obtain ⟨C_chem, La, Lb, haux⟩ := prod.lowerRawAux k hprev
    have hstep := rotheSeqOfPaperRouteA_stepFacts
      prod.core.toOrbitCore hκ hM k
    have hdata := paperLowerBarrierStepData_lowerBarrierRaw_of_paperStep
      (Λ := Λ) hcond hD hD_ge_one hu hprev prod.core.hlam
      hstep.step_op haux
    exact lowerBarrier_step_ge_of_paperData hdata
  · simp [paperControlledLowerRawRotheSeq, huControlled]
    exact fun x => le_trans (hu.lower x) (hu.bare.le_upperBarrier x)

/-- Full lower invariant on the controlled domain. -/
theorem paperControlledLowerRaw_orbitLowerBound
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    ∀ u, InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u →
      ∀ k x, lowerBarrierRaw κ κtilde D x ≤
        paperControlledLowerRawRotheSeq floor u k x := by
  intro u hu
  apply rotheOrbitLowerBound_of_stepLowerInvariant
    (φ := lowerBarrierRaw κ κtilde D)
    (rotheSeq := paperControlledLowerRawRotheSeq floor) ?_
    (paperControlledLowerRaw_stepLowerInvariant floor hcond hD hD_ge_one)
    u ⟨hu.bare, hu.lower⟩
  intro v hv x
  by_cases hvC : InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) v
  · rw [paperControlledLowerRawRotheSeq_eq floor hvC,
      rotheSeqOfPaperRouteA_zero]
    exact le_trans (hv.lower x) (hv.bare.le_upperBarrier x)
  · simp [paperControlledLowerRawRotheSeq, hvC]
    exact le_trans (hv.lower x) (hv.bare.le_upperBarrier x)

/-- The controlled long-time map is a self-map of the same compact trap. -/
theorem paperControlledLowerRaw_mapsTo
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hsigma : 0 < sigma) :
    ∀ u, InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u →
      InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D)
        (rotheLimit (paperControlledLowerRawRotheSeq floor u)) := by
  intro u hu
  let hdata := paperControlledLowerRaw_orbitData floor hΛ0 hΛM hbarLip hu
  have hbare : InMonotoneWaveTrapSet κ M
      (rotheLimit (paperControlledLowerRawRotheSeq floor u)) :=
    rotheLimit_mem_trap (hdata.limit_continuous hM) hdata.bddBelow
      hdata.anti_x hdata.nonneg hdata.le_upperBarrier
      (upperBarrier_isBddFun hM)
  have hlower : ∀ x, lowerBarrierRaw κ κtilde D x ≤
      rotheLimit (paperControlledLowerRawRotheSeq floor u) x := by
    intro x
    exact rotheLimit_ge_of_ge
      (paperControlledLowerRaw_orbitLowerBound floor hcond hD hD_ge_one u hu)
      x
  have hrate := (floor.producer u hu).core.rotheLimit_rate
    hκ hM hΛ0 hΛM hbarLip hsigma
  exact
    { uniformTrap := ⟨hbare, hdata.limitLip⟩
      lower := hlower
      leftRateData := by
        simpa only [paperControlledLowerRawRotheSeq_eq floor hu] using hrate }

/-- Compactness of the controlled map range is now immediate from compactness
of the corrected trap itself. -/
theorem paperControlledLowerRaw_compactRange
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hmap : ∀ u, InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u →
      InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D)
        (rotheLimit (paperControlledLowerRawRotheSeq floor u))) :
    LocalUniformSequentiallyCompactRange
      (InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D))
      (fun u => rotheLimit (paperControlledLowerRawRotheSeq floor u)) := by
  intro seq hseq
  simpa using
    (InControlledLowerPinnedMonotoneTrap.locallyUniform_sequentiallyCompact
      (κ := κ) (M := M) (L := M) (sigma := sigma) (aL := aL) (C := C)
      (φ := lowerBarrierRaw κ κtilde D) hM hM
      (fun n => rotheLimit (paperControlledLowerRawRotheSeq floor (seq n)))
      (fun n => hmap (seq n) (hseq n)))

/-- Exact remaining L10 analytic statement for the corrected construction. -/
def PaperControlledLowerRawContinuousDependence
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM) : Prop :=
  LocalUniformContinuousOn
    (InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D))
    (fun u => rotheLimit (paperControlledLowerRawRotheSeq floor u))

section AxiomAudit

#print axioms paperStepFixedSourceQuantitativeCore_of_params
#print axioms PaperGreenStepInputRouteAQuantitativeOrbitCore.successor_rate
#print axioms PaperGreenStepInputRouteAQuantitativeOrbitCore.orbitData
#print axioms PaperGreenStepInputRouteAQuantitativeOrbitCore.rotheLimit_rate
#print axioms paperRouteAQuantitativeCore_of_params
#print axioms paperControlledLowerRaw_mapsTo
#print axioms paperControlledLowerRaw_compactRange
#print axioms PaperControlledLowerRawContinuousDependence

end AxiomAudit

end ShenWork.Paper1
