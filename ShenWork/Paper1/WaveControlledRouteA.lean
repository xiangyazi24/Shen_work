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

section AxiomAudit

#print axioms paperStepFixedSourceQuantitativeCore_of_params
#print axioms PaperGreenStepInputRouteAQuantitativeOrbitCore.successor_rate
#print axioms paperRouteAQuantitativeCore_of_params

end AxiomAudit

end ShenWork.Paper1
