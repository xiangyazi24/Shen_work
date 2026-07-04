import ShenWork.PDE.P3MoserRealInduction
import ShenWork.PDE.P3MoserEnergyGapRefactor
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.Paper2.IntervalDomainCrossDiffusionBootstrap

/-!
# Subinterval Moser input wiring

This file wires the pointwise cross-diffusion bootstrap and the p-dependent
gap producer on a positive subinterval.  The remaining analytic seed needed for
`AbstractLpBootstrapHypothesis` is kept as a named residual: the current
`BoundedBeforeOnSubinterval` predicate has only timewise pointwise bounds, while
`LpPowerBoundedBefore` needs one uniform integral constant on the whole
subinterval.

There is also a small interface mismatch in `SubintervalMoserInputResidual`:
it assumes only `0 ≤ τ`, but `AbstractLpBootstrapHypothesis ... τ ...`
contains the field `0 < τ`.  The final theorem below therefore takes the
positive-time implication as a named residual rather than hiding that boundary
case.
-/

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation
open ShenWork.IntervalDomainExistence.P3MoserRealInduction
open ShenWork.IntervalDomainExistence.P3MoserEnergyGapRefactor

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserSubintervalInput

/-- The canonical Moser subinterval exponent increment for the interval
cross-diffusion estimate. -/
def subintervalMoserRho (p : CM2Params) : ℝ :=
  2 * p.γ

/-- A bootstrap seed exponent chosen above both the abstract bootstrap threshold
and the p-dependent gap threshold. -/
def subintervalMoserP0 (p : CM2Params) : ℝ :=
  max (max 1 (subintervalMoserRho p * (p.N : ℝ) / 2))
      (gapThresholdPDep p.χ₀) + 1

theorem subintervalMoserRho_pos (p : CM2Params) :
    0 < subintervalMoserRho p := by
  unfold subintervalMoserRho
  nlinarith [p.hγ]

theorem subintervalMoserP0_gt_bootstrapThreshold (p : CM2Params) :
    max 1 (subintervalMoserRho p * (p.N : ℝ) / 2) <
      subintervalMoserP0 p := by
  unfold subintervalMoserP0
  have hle :
      max 1 (subintervalMoserRho p * (p.N : ℝ) / 2) ≤
        max (max 1 (subintervalMoserRho p * (p.N : ℝ) / 2))
          (gapThresholdPDep p.χ₀) :=
    le_max_left _ _
  linarith

theorem gapThresholdPDep_le_subintervalMoserP0 (p : CM2Params) :
    gapThresholdPDep p.χ₀ ≤ subintervalMoserP0 p := by
  unfold subintervalMoserP0
  have hle :
      gapThresholdPDep p.χ₀ ≤
        max (max 1 (subintervalMoserRho p * (p.N : ℝ) / 2))
          (gapThresholdPDep p.χ₀) :=
    le_max_right _ _
  linarith

/-- The analytic seed not supplied by `BoundedBeforeOnSubinterval`: a uniform
`LpPowerBoundedBefore` bound on the positive subinterval for the chosen seed
exponent. -/
def SubintervalLpPowerBoundResidual (p : CM2Params) : Prop :=
  ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 < τ →
          LpPowerBoundedBefore intervalDomain (subintervalMoserP0 p) τ u

/-- The missing positivity premise in the current non-strict residual
interface. -/
def SubintervalPositiveTimeResidual (p : CM2Params) : Prop :=
  ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 ≤ τ →
          0 < τ

/-- Positive-time version of `SubintervalMoserInputResidual`, modulo the one
uniform Lp seed residual. -/
def PositiveSubintervalMoserInputResidual (p : CM2Params) : Prop :=
  ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 < τ →
          ∃ rho p0,
            CrossDiffusionBootstrapEstimate intervalDomain p τ rho u v ∧
              AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) τ rho p0 ∧
                LpBootstrapEnergyInequalityWithGap intervalDomain u τ rho p0

theorem intervalDomain_positiveSubintervalMoserInputResidual
    {p : CM2Params}
    (hLp : SubintervalLpPowerBoundResidual p) :
    PositiveSubintervalMoserInputResidual p := by
  intro T τ u v hsol hsub hτ_pos
  let rho : ℝ := subintervalMoserRho p
  let p0 : ℝ := subintervalMoserP0 p
  have hsolτ :
      IsPaper2ClassicalSolution intervalDomain p τ u v :=
    isPaper2ClassicalSolution_intervalDomain_mono
      (p := p) (Tshort := τ) (Tlong := T) (u := u) (v := v)
      hτ_pos hsub.1 hsol
  have hcross :
      CrossDiffusionBootstrapEstimate intervalDomain p τ rho u v := by
    simpa [rho, subintervalMoserRho] using
      intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsolτ
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) τ rho p0 := by
    refine ⟨?_, hτ_pos, ?_, ?_⟩
    · simpa [rho] using subintervalMoserRho_pos p
    · simpa [rho, p0] using
        subintervalMoserP0_gt_bootstrapThreshold p
    · simpa [p0] using hLp hsol hsub hτ_pos
  have hgap :
      LpBootstrapEnergyInequalityWithGap intervalDomain u τ rho p0 :=
    lpBootstrapEnergyInequalityWithGap_of_classical_pDep
      (params := p) (T := τ) (rho := rho) (p0 := p0) (u := u) (v := v)
      (by simpa [p0] using gapThresholdPDep_le_subintervalMoserP0 p)
      hsolτ hcross hboot
  exact ⟨rho, p0, hcross, hboot, hgap⟩

/-- Discharge the original non-strict residual interface from the positive-time
interface fix and the uniform Lp seed residual. -/
theorem intervalDomain_subintervalMoserInputResidual
    {p : CM2Params}
    (hτ_pos : SubintervalPositiveTimeResidual p)
    (hLp : SubintervalLpPowerBoundResidual p) :
    SubintervalMoserInputResidual p := by
  intro T τ u v hsol hsub hτ_nonneg
  exact intervalDomain_positiveSubintervalMoserInputResidual hLp
    hsol hsub (hτ_pos hsol hsub hτ_nonneg)

#print axioms subintervalMoserRho_pos
#print axioms subintervalMoserP0_gt_bootstrapThreshold
#print axioms gapThresholdPDep_le_subintervalMoserP0
#print axioms intervalDomain_positiveSubintervalMoserInputResidual
#print axioms intervalDomain_subintervalMoserInputResidual

end ShenWork.IntervalDomainExistence.P3MoserSubintervalInput

end
