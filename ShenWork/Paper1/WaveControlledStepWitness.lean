import ShenWork.Paper1.IntervalP1PerStepFixedSource

open Set

noncomputable section

namespace ShenWork.Paper1

/-- Once an orbit iterate carries the quantitative left rate used by the
two-radius source box, all remaining fields of `PerStepBoxZWitness` are
automatic.  The Hölder radius is simply enlarged to absorb both the obstacle
radius and the explicit kernel radius.  The source-box clamp argument itself
needs no chemotactic comparison constant, so `C_chem = 0` is sufficient here.

This deliberately takes the quantitative rate as an input: it is an additional
shared-orbit invariant and cannot be inferred from the qualitative iterate
record. -/
noncomputable def perStepBoxZWitness_of_quantitative_rate
    {p : CMParams}
    {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u Z : ℝ → ℝ}
    (params :
      PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (hZ : PaperIterateBase p c κ M u Z)
    (hZrate : ∃ ell : ℝ,
      ExpLeftRate sigma aL (paperFixedSourceMapTwoRadiusCZ m_sigma C_R) Z ell)
    (hreact : (1 / lam) * reactionLip p.α M < 1) :
    PerStepBoxZWitness p c lam M κ B sigma aL C_R m_sigma u Z
      params.hlam params.hrpκ params.hrmκ params.hκ params.hM
      params.hBnn params.hu.trap := by
  let holderKernel :=
    paperFixedSourceMap_holder_kernel
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
      (u := u) (Z := Z)
      params.hlam params.hrpκ params.hrmκ params.hκ.le params.hM
      params.hBnn params.hu.trap hZ
  let H0 : ℝ := Classical.choose holderKernel
  let H : ℝ := max (sourceObstacleHolderConst κ M B sigma C_R) H0
  refine
    { H := H
      C_chem := 0
      base := hZ
      rate := hZrate
      hH_obs := ?_
      hHolder_le := ?_
      hCB := ?_ }
  · exact le_max_left _ _
  · change H0 ≤ H
    exact le_max_right _ _
  · simpa using hreact

/-- Orbit-faithful fixed-source existence with the old impossible all-regular-
profile witness removed.  A caller supplies only the shared quantitative rate
of the actual iterate; the Hölder/source-box witness is built above. -/
theorem paperStepFixedSourceExistsForRegularSuperTrap_of_quantitative_rate
    {p : CMParams}
    {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params :
      PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (hreact : (1 / lam) * reactionLip p.α M < 1)
    (hrate : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
      ∃ ell : ℝ,
        ExpLeftRate sigma aL
          (paperFixedSourceMapTwoRadiusCZ m_sigma C_R) Z ell) :
    PaperStepFixedSourceExistsForRegularSuperTrap p c lam M κ Λ u :=
  paperStepFixedSourceExistsForRegularSuperTrap_of_params params
    (fun Z hZ =>
      perStepBoxZWitness_of_quantitative_rate params hZ (hrate Z hZ) hreact)

section AxiomAudit

#print axioms perStepBoxZWitness_of_quantitative_rate
#print axioms paperStepFixedSourceExistsForRegularSuperTrap_of_quantitative_rate

end AxiomAudit

end ShenWork.Paper1
