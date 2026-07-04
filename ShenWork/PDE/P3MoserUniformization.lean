import ShenWork.PDE.P3MoserRealInductionClosure
import ShenWork.PDE.P3MoserSubintervalInput
import ShenWork.PDE.IntervalDomain1DLinfRoute

/-!
# Uniformization bridges for the interval-domain Moser assembly

The current `intervalDomainClassicalRegularity` gives joint continuity of the
solution field on the open-time slab `Ioo 0 T × Icc 0 1`, not on a closed time
slab including `t = 0`.  Thus compactness alone bounds each closed interior
sub-slab, but it does not by itself prove one bound on all of `(0,T)`.

This file records the non-circular part that is available from the existing
interfaces: once the pointwise uniformization residual is supplied on a
sub-horizon, the subinterval `LpPowerBoundedBefore` seed follows immediately.
-/

open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation
open ShenWork.IntervalDomainExistence.P3MoserRealInductionClosure
open ShenWork.IntervalDomainExistence.P3MoserSubintervalInput
open ShenWork.IntervalDomainExistence.IntervalDomain1DLinfRoute

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserUniformization

/-- The chosen subinterval Moser seed exponent is strictly larger than `1`. -/
theorem subintervalMoserP0_gt_one (p : CM2Params) :
    1 < subintervalMoserP0 p := by
  have hle :
      (1 : ℝ) ≤ max 1 (subintervalMoserRho p * (p.N : ℝ) / 2) :=
    le_max_left _ _
  exact lt_of_le_of_lt hle (subintervalMoserP0_gt_bootstrapThreshold p)

/-- A uniform pointwise absolute-value bound on `(0,T)` produces all
`LpPowerBoundedBefore` bounds with exponent `r > 1`.

The existing `intervalDomain_all_Lp_of_Linf` only needs an upper bound
`u(t,x) ≤ M`; the absolute-value bound gives that by `u ≤ |u|`. -/
theorem intervalDomain_all_Lp_of_pointwise_abs_uniform
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {M : ℝ}
    (hM_nonneg : 0 ≤ M)
    (hM : ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point, |u t x| ≤ M) :
    ∀ r, 1 < r → LpPowerBoundedBefore intervalDomain r T u := by
  refine intervalDomain_all_Lp_of_Linf hsol hM_nonneg ?_
  intro t ht0 htT x
  exact le_trans (le_abs_self (u t x)) (hM t ht0 htT x)

/-- Pointwise uniformization on every horizon discharges the subinterval
`LpPowerBoundedBefore` seed residual.

Given a positive subinterval `τ`, restrict the classical solution from horizon
`T` to horizon `τ`, use pointwise uniformization there, and then convert the
uniform pointwise bound into the required `L^p` bound for the canonical seed
exponent. -/
theorem subintervalLpPowerBoundResidual_of_pointwiseUniformizationResidual
    {p : CM2Params}
    (huniform : PointwiseUniformizationResidual intervalDomain p) :
    SubintervalLpPowerBoundResidual p := by
  intro T τ u v hsol hsub hτ_pos
  have hsolτ :
      IsPaper2ClassicalSolution intervalDomain p τ u v :=
    isPaper2ClassicalSolution_intervalDomain_mono
      (p := p) (Tshort := τ) (Tlong := T) (u := u) (v := v)
      hτ_pos hsub.1 hsol
  have hsubτ : BoundedBeforeOnSubinterval intervalDomain u τ τ := by
    refine ⟨le_rfl, ?_⟩
    intro t ht0 htτ
    exact hsub.2 t ht0 htτ
  rcases huniform hsolτ hsubτ with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := by
    let x0 : intervalDomain.Point := ⟨0, by exact ⟨by norm_num, by norm_num⟩⟩
    have hbound : |u (τ / 2) x0| ≤ M :=
      hM (τ / 2) (by linarith) (by linarith) x0
    exact le_trans (abs_nonneg (u (τ / 2) x0)) hbound
  exact
    intervalDomain_all_Lp_of_pointwise_abs_uniform
      (params := p) (T := τ) (u := u) (v := v)
      hsolτ hM_nonneg hM
      (subintervalMoserP0 p) (subintervalMoserP0_gt_one p)

#print axioms subintervalMoserP0_gt_one
#print axioms intervalDomain_all_Lp_of_pointwise_abs_uniform
#print axioms subintervalLpPowerBoundResidual_of_pointwiseUniformizationResidual

end ShenWork.IntervalDomainExistence.P3MoserUniformization

end
