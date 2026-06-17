import ShenWork.Paper1.WaveLemma42Paper

namespace ShenWork.Paper1

noncomputable section

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

#print axioms paperImplicitStep_fixed_paperWaveOperator_zero
#print axioms paperImplicitStep_fixed_frozenWaveOperator_zero
#print axioms paperLimit_fixedStepIdentity_of_stepLimitPassage
#print axioms paperRotheLimitFixedStepIdentity_of_stepLimitPassage
#print axioms paperLowerPinnedStationary_of_fixedStepIdentity
#print axioms paperLowerPinnedStationaryFlatFloor_of_fixedStepIdentity

end

end ShenWork.Paper1
