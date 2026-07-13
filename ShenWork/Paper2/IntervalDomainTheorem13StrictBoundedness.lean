import ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer
import ShenWork.Paper2.IntervalDomainMRestartedLpLinfGeneral

/-!
Direct boundedness for the two strict alternatives of Paper 2, Theorem 1.3,
on the paper-faithful general-`m` interval model.

The exponent is selected once above `2`, `m`, and `gamma`.  The genuine
finite-power energy estimate is then fed directly to the general-`m` restarted
`L^P -> L^infinity` endpoint; no Corollary 2.1 or Proposition 2.5 package field
is projected.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMRestartedLpLinfGeneral
open ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer

/-- A fixed exponent above every threshold needed by the general-`m`
restarted endpoint. -/
def strictEndpointExponent (p : CM2Params) : ℝ :=
  max 2 (max p.m p.γ) + 1

lemma strictEndpointExponent_gt_two (p : CM2Params) :
    2 < strictEndpointExponent p := by
  unfold strictEndpointExponent
  linarith [le_max_left (2 : ℝ) (max p.m p.γ)]

lemma strictEndpointExponent_gt_m (p : CM2Params) :
    p.m < strictEndpointExponent p := by
  unfold strictEndpointExponent
  linarith [le_max_right (2 : ℝ) (max p.m p.γ),
    le_max_left p.m p.γ]

lemma strictEndpointExponent_ge_gamma (p : CM2Params) :
    p.γ ≤ strictEndpointExponent p := by
  unfold strictEndpointExponent
  linarith [le_max_right (2 : ℝ) (max p.m p.γ),
    le_max_right p.m p.γ]

private lemma boundedBefore_of_selected_power
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hLp : LpPowerBoundedBefore intervalDomainM
      (strictEndpointExponent p) T u) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  let P := strictEndpointExponent p
  let Q := P / p.m
  have hP2 : 2 < P := strictEndpointExponent_gt_two p
  have hmP : p.m < P := strictEndpointExponent_gt_m p
  have hP : 1 < P := lt_trans one_lt_two hP2
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (lt_div_iff₀ p.hm).2 (by simpa using hmP)
  have hmQ : p.m * Q = P := by
    dsimp [Q]
    field_simp [p.hm.ne']
  have hγP : p.γ ≤ P := strictEndpointExponent_ge_gamma p
  exact boundedBefore_of_lp_restarted_affine_general hu₀ hsol htrace
    hP hQ hmQ hγP hLp

/-- Strict alternative (i), in the positive-sensitivity branch, gives
boundedness on the entire classical horizon.  The nonpositive-sensitivity
branch belongs to Theorem 1.1 and is intentionally not hidden here. -/
theorem boundedBefore_strict_case_i_positive_chi
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hb : 0 < p.b) (hchi : 0 < p.χ₀)
    (hgap : p.m + p.γ - 1 < p.α) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  apply boundedBefore_of_selected_power hu₀ hsol htrace
  exact strong_case_i_lp_power_bounded_before hu₀ hsol htrace hb hchi.le
    (strictEndpointExponent_gt_two p) hgap

/-- Strict alternative (ii) gives boundedness on the entire classical
horizon.  Its energy proof uses the squared cross coefficient and therefore
does not require a sign assumption on `chi_0`. -/
theorem boundedBefore_strict_case_ii
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hb : 0 < p.b) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hgap : 2 * p.m + p.γ - 2 < p.α) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  apply boundedBefore_of_selected_power hu₀ hsol htrace
  exact strong_case_ii_lp_power_bounded_before hu₀ hsol htrace hb
    (strictEndpointExponent_gt_two p) hbeta hgap

#print axioms strictEndpointExponent_gt_two
#print axioms strictEndpointExponent_gt_m
#print axioms strictEndpointExponent_ge_gamma
#print axioms boundedBefore_strict_case_i_positive_chi
#print axioms boundedBefore_strict_case_ii

end ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness
