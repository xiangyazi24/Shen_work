/-
  Negative-branch per-step parameters with the paper upper barrier automatic.
-/
import ShenWork.Paper1.WaveLemma42ParamCore
import ShenWork.Paper1.WaveNegativeSuperBarrier

noncomputable section

namespace ShenWork.Paper1

/-- The `M = 1`, `κ = kappa c` source-box parameters for the negative branch,
with the paper upper-barrier scalar field removed.  That field follows from
`cStarLower p < c` for every `χ ≤ 0`. -/
structure NegativePerStepBoxParams
    (p : CMParams) (c lam Λ B sigma aL C_u L_u C_R m_sigma : ℝ)
    (u : ℝ → ℝ) : Prop where
  hlam : 0 < lam
  hrpκ : kappa c < greenRootPlus c lam
  hrmκ : kappa c < -greenRootMinus c lam
  hBnn : 0 ≤ B
  hBpos : 0 < B
  hsigma : 0 < sigma
  hsigma1 : sigma < 1
  hsigma_root : sigma < greenRootPlus c lam
  hCRnn : 0 ≤ C_R
  hUleft : (1 : ℝ) ≤ Real.exp (-(kappa c) * aL)
  hObsRight : 2 * (B * 1) ≤ C_R
  hu : InMonotoneWaveTrapSet (kappa c) 1 u
  hu_rate : ExpLeftRate sigma aL C_u u L_u
  hsourceBound_eq :
    Λ = 2 * (greenDelta c lam)⁻¹ * (B * 1)
  hscalar :
    |(-p.χ * p.m)| * (1 : ℝ) ^ (p.m - 1) * (1 : ℝ) ^ p.γ *
          greenWeightedMass1 c lam (kappa c) * B
      + (1 + |p.χ| * (1 : ℝ) ^ (p.m - 1) * (1 : ℝ) ^ p.γ
          + (1 : ℝ) ^ p.α + |p.χ| * (1 : ℝ) ^ (p.m + p.γ - 1))
      + lam ≤ B
  hcontract :
    paperTruncatedNonlinearityRateClam p c lam 1 B sigma C_u +
        paperFixedSourceMapAZ lam * m_sigma < 1
  hCR :
    paperTruncatedNonlinearityRateD0 p c lam 1 B sigma C_u /
        (1 - (paperTruncatedNonlinearityRateClam p c lam 1 B sigma C_u +
          paperFixedSourceMapAZ lam * m_sigma)) ≤ C_R
  hNL_M_nonpos :
    paperTruncatedLimitNonlinearity p 1 (L_u ^ p.γ) ≤ 0

/-- Fill the existing per-step parameter bundle with the paper-faithful
negative upper barrier.  No plateau source comparison is required. -/
def NegativePerStepBoxParams.toPerStepBoxParams
    {p : CMParams} {c lam Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (h : NegativePerStepBoxParams p c lam Λ B sigma aL C_u L_u C_R m_sigma u)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c) :
    PerStepBoxParams p c lam 1 (kappa c) Λ B sigma aL C_u L_u C_R m_sigma u :=
  { hlam := h.hlam
    hrpκ := h.hrpκ
    hrmκ := h.hrmκ
    hκ := kappa_pos_of_cStarLower_lt hc
    hM := one_pos
    hBnn := h.hBnn
    hBpos := h.hBpos
    hsigma := h.hsigma
    hsigma1 := h.hsigma1
    hsigma_root := h.hsigma_root
    hCRnn := h.hCRnn
    hUleft := h.hUleft
    hObsRight := h.hObsRight
    hu := h.hu
    hu_rate := h.hu_rate
    hsourceBound_eq := h.hsourceBound_eq
    hscalar := h.hscalar
    hcontract := h.hcontract
    hCR := h.hCR
    hbarrierScalar :=
      paperUpperBarrierSuperScalarConditions_one_of_cStarLower_lt
        p hχ hα hc
    hNL_M_nonpos := h.hNL_M_nonpos }

/-- Direct feed into the already existing Route-A Green core.  The caller now
carries only the source-box witness and the non-barrier Route-A rest data; the
negative paper upper barrier is generated from the headline speed regime. -/
def paperRouteAParamGreenCore_negative
    {p : CMParams} {c lam Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params : NegativePerStepBoxParams
      p c lam Λ B sigma aL C_u L_u C_R m_sigma u)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c)
    (wit : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier (kappa c) 1 x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
        PerStepBoxZWitness p c lam 1 (kappa c) B sigma aL C_R m_sigma u Z
          params.hlam params.hrpκ params.hrmκ
          (kappa_pos_of_cStarLower_lt hc) one_pos params.hBnn params.hu.trap)
    (hrest : PaperGreenStepInputRouteASuperRestProvider
      p c lam 1 (kappa c) Λ u) :
    PaperGreenStepInputRouteACore p c lam 1 (kappa c) Λ u :=
  paperRouteAParamGreenCore
    (params.toPerStepBoxParams hχ hα hc) wit hrest

section AxiomAudit

#print axioms NegativePerStepBoxParams.toPerStepBoxParams
#print axioms paperRouteAParamGreenCore_negative

end AxiomAudit

end ShenWork.Paper1
