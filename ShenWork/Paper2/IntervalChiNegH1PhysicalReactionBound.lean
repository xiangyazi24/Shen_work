import ShenWork.Paper2.IntervalChiNegH1PhysicalSqrtBounds
import ShenWork.Paper2.IntervalDomainLpEnergyFrontiers

/-!
# Logistic reaction bound reducer for the physical H¹ sqrt route

This file isolates the remaining logistic reaction estimate.  It proves that a
fixed-time spatial IBP identity for the physical reaction scalar, together with a
pointwise slope bound, implies the reaction part required by
`H1PhysicalRHSSqrtBoundsBefore`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalSqrtBounds
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalFullKernelRegularity

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalReactionBound

/-- The spatial derivative slope of the logistic reaction `u * (a - b*u^α)`. -/
def H1PhysicalLogisticSlope (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) : ℝ :=
  p.a - p.b * (1 + p.α) * (intervalDomainLift (u τ) x) ^ p.α

private theorem H1PhysicalLogisticSlope_eq_alpha_add_one
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) :
    H1PhysicalLogisticSlope p u τ x =
      p.a - p.b * (p.α + 1) * (intervalDomainLift (u τ) x) ^ p.α := by
  unfold H1PhysicalLogisticSlope
  ring

private theorem H1PhysicalLogisticReactionPart_continuousOn_Icc_of_classicalSolution
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (fun x => H1PhysicalLogisticReactionPart p u τ x)
      (Set.Icc (0 : ℝ) 1) := by
  have hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have hU : ContinuousOn (fun x => intervalDomainLift (u τ) x)
      (Set.Icc (0 : ℝ) 1) :=
    hC2.continuousOn
  have hpow : ContinuousOn
      (fun x => (intervalDomainLift (u τ) x) ^ p.α)
      (Set.Icc (0 : ℝ) 1) :=
    hU.rpow_const (fun _ _ => Or.inr p.hα.le)
  simpa [H1PhysicalLogisticReactionPart] using
    hU.mul (continuousOn_const.sub (continuousOn_const.mul hpow))

private theorem H1PhysicalLogisticSlope_continuousOn_Icc_of_classicalSolution
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (fun x => H1PhysicalLogisticSlope p u τ x)
      (Set.Icc (0 : ℝ) 1) := by
  have hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have hU : ContinuousOn (fun x => intervalDomainLift (u τ) x)
      (Set.Icc (0 : ℝ) 1) :=
    hC2.continuousOn
  have hpow : ContinuousOn
      (fun x => (intervalDomainLift (u τ) x) ^ p.α)
      (Set.Icc (0 : ℝ) 1) :=
    hU.rpow_const (fun _ _ => Or.inr p.hα.le)
  have hterm : ContinuousOn
      (fun x => (p.b * (1 + p.α)) *
        (intervalDomainLift (u τ) x) ^ p.α)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul hpow
  simpa [H1PhysicalLogisticSlope, mul_assoc] using
    continuousOn_const.sub hterm

private theorem H1PhysicalUx_continuousOn_Icc_of_classicalSolution
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (fun x => deriv (intervalDomainLift (u τ)) x)
      (Set.Icc (0 : ℝ) 1) := by
  have hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have hdw0 :
      derivWithin (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) 0 = 0 :=
    intervalDomain_solution_derivWithin_u_left_zero hsol hτ.1 hτ.2
  have hdw1 :
      derivWithin (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) 1 = 0 :=
    intervalDomain_solution_derivWithin_u_right_zero hsol hτ.1 hτ.2
  exact deriv_intervalDomainLift_continuousOn_Icc_of_regularity hC2 hdw0 hdw1

/-- Fixed-time derivative of the logistic H¹ reaction factor.
The real-rpow chain rule uses strict positivity of the classical solution. -/
theorem H1PhysicalLogisticReactionPart_hasDerivAt_of_classicalSolution
    {p : CM2Params} {T τ x : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y => H1PhysicalLogisticReactionPart p u τ y)
      (H1PhysicalLogisticSlope p u τ x *
        deriv (intervalDomainLift (u τ)) x)
      x := by
  let U : ℝ → ℝ := fun y => intervalDomainLift (u τ) y
  have hC2 : ContDiffOn ℝ 2 U (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have hU : HasDerivAt U (deriv U x) x :=
    hasDerivAt_of_contDiffOn_two_interior hC2 hx
  have hU_pos : 0 < U x := by
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hpos : 0 < u τ (⟨x, hxIcc⟩ : intervalDomain.Point) :=
      hsol.u_pos' hτ.1 hτ.2
    dsimp [U]
    rw [intervalDomainLift, dif_pos hxIcc]
    exact hpos
  have hpow_raw :=
    hU.rpow_const (p := 1 + p.α) (Or.inl (ne_of_gt hU_pos))
  have hpow :
      HasDerivAt (fun y => (U y) ^ (1 + p.α))
        (deriv U x * (1 + p.α) * (U x) ^ p.α) x := by
    refine hpow_raw.congr_deriv ?_
    ring_nf
  have halt :
      HasDerivAt (fun y => p.a * U y - p.b * (U y) ^ (1 + p.α))
        (p.a * deriv U x -
          p.b * (deriv U x * (1 + p.α) * (U x) ^ p.α)) x :=
    (hU.const_mul p.a).sub (hpow.const_mul p.b)
  have halt' :
      HasDerivAt (fun y => p.a * U y - p.b * (U y) ^ (1 + p.α))
        (H1PhysicalLogisticSlope p u τ x * deriv U x) x := by
    refine halt.congr_deriv ?_
    simp [H1PhysicalLogisticSlope, U]
    ring
  have heq :
      (fun y => H1PhysicalLogisticReactionPart p u τ y) =ᶠ[𝓝 x]
        fun y => p.a * U y - p.b * (U y) ^ (1 + p.α) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    have hy_pos : 0 < U y := by
      have hpos : 0 < u τ (⟨y, hyIcc⟩ : intervalDomain.Point) :=
        hsol.u_pos' hτ.1 hτ.2
      dsimp [U]
      rw [intervalDomainLift, dif_pos hyIcc]
      exact hpos
    have hpowmul : U y * (U y) ^ p.α = (U y) ^ (1 + p.α) := by
      calc
        U y * (U y) ^ p.α = (U y) ^ (1 : ℝ) * (U y) ^ p.α := by
          rw [Real.rpow_one]
        _ = (U y) ^ ((1 : ℝ) + p.α) := by
          rw [← Real.rpow_add hy_pos]
    change U y * (p.a - p.b * (U y) ^ p.α) =
      p.a * U y - p.b * (U y) ^ (1 + p.α)
    calc
      U y * (p.a - p.b * (U y) ^ p.α) =
          p.a * U y - p.b * (U y * (U y) ^ p.α) := by
        ring
      _ = p.a * U y - p.b * (U y) ^ (1 + p.α) := by
        rw [hpowmul]
  exact halt'.congr_of_eventuallyEq heq

/-- Logistic reaction scalar after one spatial integration by parts. -/
theorem H1PhysicalReactX_eq_logisticSlope_grad_sq_of_classicalSolution
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    H1PhysicalReactX p u τ =
      ∫ x in (0 : ℝ)..1,
        H1PhysicalLogisticSlope p u τ x *
          (deriv (intervalDomainLift (u τ)) x) ^ 2 := by
  let U : ℝ → ℝ := fun y => intervalDomainLift (u τ) y
  let q : ℝ → ℝ := fun y => H1PhysicalLogisticReactionPart p u τ y
  let s : ℝ → ℝ := fun y => H1PhysicalLogisticSlope p u τ y
  have hC2 : ContDiffOn ℝ 2 U (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have hq_cont_Icc : ContinuousOn q (Set.Icc (0 : ℝ) 1) := by
    simpa [q] using
      H1PhysicalLogisticReactionPart_continuousOn_Icc_of_classicalSolution
        (p := p) (u := u) (v := v) hsol hτ
  have hux_cont_Icc : ContinuousOn (fun x => deriv U x)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using
      H1PhysicalUx_continuousOn_Icc_of_classicalSolution
        (p := p) (u := u) (v := v) hsol hτ
  have hs_cont_Icc : ContinuousOn s (Set.Icc (0 : ℝ) 1) := by
    simpa [s] using
      H1PhysicalLogisticSlope_continuousOn_Icc_of_classicalSolution
        (p := p) (u := u) (v := v) hsol hτ
  have hq_cont : ContinuousOn q (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hq_cont_Icc
  have hux_cont : ContinuousOn (fun x => deriv U x) (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hux_cont_Icc
  have hs_cont : ContinuousOn s (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs_cont_Icc
  have hq_deriv : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt q (s x * deriv U x) x := by
    intro x hx
    have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simpa [q, s, U] using
      H1PhysicalLogisticReactionPart_hasDerivAt_of_classicalSolution
        (p := p) (u := u) (v := v) hsol hτ hx01
  have hux_deriv : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun y => deriv U y) (deriv (deriv U) x) x := by
    intro x hx
    have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact hasDerivAt_deriv_of_contDiffOn_two_interior hC2 hx01
  have hq_deriv_int : IntervalIntegrable (fun x => s x * deriv U x)
      volume (0 : ℝ) 1 :=
    (hs_cont.mul hux_cont).intervalIntegrable
  have huxx_int : IntervalIntegrable (fun x => deriv (deriv U) x)
      volume (0 : ℝ) 1 := by
    simpa [U] using intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2
  have hIBP :
      (∫ x in (0 : ℝ)..1, q x * deriv (deriv U) x) =
        q 1 * deriv U 1 - q 0 * deriv U 0 -
          ∫ x in (0 : ℝ)..1, (s x * deriv U x) * deriv U x := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hq_cont hux_cont hq_deriv hux_deriv hq_deriv_int huxx_int
  have hU0 : deriv U 0 = 0 := by
    simpa [U] using deriv_intervalDomainLift_eq_zero_at_zero (u τ)
  have hU1 : deriv U 1 = 0 := by
    simpa [U] using deriv_intervalDomainLift_eq_zero_at_one (u τ)
  have hIBP_sq :
      (∫ x in (0 : ℝ)..1, q x * deriv (deriv U) x) =
        -∫ x in (0 : ℝ)..1, s x * (deriv U x) ^ 2 := by
    rw [hIBP, hU0, hU1]
    have hsquare :
        (∫ x in (0 : ℝ)..1, s x * deriv U x * deriv U x) =
          ∫ x in (0 : ℝ)..1, s x * (deriv U x) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    rw [hsquare]
    ring
  have hreact_def :
      H1PhysicalReactX p u τ =
        -(∫ x in (0 : ℝ)..1, deriv (deriv U) x * q x) := by
    simp [H1PhysicalReactX, q, U,
      ShenWork.Paper2.IntervalChiNegH1EnergyIdentity.liftDeriv2]
  calc
    H1PhysicalReactX p u τ
        = -(∫ x in (0 : ℝ)..1, deriv (deriv U) x * q x) := hreact_def
    _ = -(∫ x in (0 : ℝ)..1, q x * deriv (deriv U) x) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    _ = ∫ x in (0 : ℝ)..1, s x * (deriv U x) ^ 2 := by
      rw [hIBP_sq]
      ring

/-- Source-side data sufficient for the physical logistic reaction H¹ bound.

The substantive analytic input is `react_ibp`; it is the spatial integration by
parts identity that should eventually be produced from classical regularity,
Neumann endpoints, positivity, and the `rpow` chain rule. -/
structure H1PhysicalReactionIBPBoundDataBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T L : ℝ) : Prop where
  hL : 0 ≤ L
  grad_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => (deriv (intervalDomainLift (u τ)) x) ^ 2) volume (0 : ℝ) 1
  slope_grad_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x =>
        H1PhysicalLogisticSlope p u τ x *
          (deriv (intervalDomainLift (u τ)) x) ^ 2)
      volume (0 : ℝ) 1
  react_ibp : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    H1PhysicalReactX p u τ =
      ∫ x in (0 : ℝ)..1,
        H1PhysicalLogisticSlope p u τ x *
          (deriv (intervalDomainLift (u τ)) x) ^ 2
  slope_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      H1PhysicalLogisticSlope p u τ x ≤ L

/-- Classical regularity and positivity produce the abstract reaction IBP bound
data with any slope cap `L ≥ p.a`. -/
theorem H1PhysicalReactionIBPBoundDataBefore_of_classicalSolution
    {p : CM2Params} {T L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hL : p.a ≤ L) :
    H1PhysicalReactionIBPBoundDataBefore p u T L := by
  refine
    { hL := le_trans p.ha hL
      grad_sq_int := ?_
      slope_grad_sq_int := ?_
      react_ibp := ?_
      slope_le := ?_ }
  · intro τ hτ
    have huxIcc : ContinuousOn
        (fun x => deriv (intervalDomainLift (u τ)) x)
        (Set.Icc (0 : ℝ) 1) :=
      H1PhysicalUx_continuousOn_Icc_of_classicalSolution
        (p := p) (T := T) (τ := τ) (u := u) (v := v) hsol hτ
    have hux : ContinuousOn
        (fun x => deriv (intervalDomainLift (u τ)) x)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using huxIcc
    exact (hux.pow 2).intervalIntegrable
  · intro τ hτ
    have hsIcc : ContinuousOn
        (fun x => H1PhysicalLogisticSlope p u τ x)
        (Set.Icc (0 : ℝ) 1) :=
      H1PhysicalLogisticSlope_continuousOn_Icc_of_classicalSolution
        (p := p) (T := T) (τ := τ) (u := u) (v := v) hsol hτ
    have huxIcc : ContinuousOn
        (fun x => deriv (intervalDomainLift (u τ)) x)
        (Set.Icc (0 : ℝ) 1) :=
      H1PhysicalUx_continuousOn_Icc_of_classicalSolution
        (p := p) (T := T) (τ := τ) (u := u) (v := v) hsol hτ
    have hprodIcc : ContinuousOn
        (fun x =>
          H1PhysicalLogisticSlope p u τ x *
            (deriv (intervalDomainLift (u τ)) x) ^ 2)
        (Set.Icc (0 : ℝ) 1) :=
      hsIcc.mul (huxIcc.pow 2)
    have hprod : ContinuousOn
        (fun x =>
          H1PhysicalLogisticSlope p u τ x *
            (deriv (intervalDomainLift (u τ)) x) ^ 2)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hprodIcc
    exact hprod.intervalIntegrable
  · intro τ hτ
    exact H1PhysicalReactX_eq_logisticSlope_grad_sq_of_classicalSolution
      (p := p) (T := T) (τ := τ) (u := u) (v := v) hsol hτ
  · intro τ hτ x hx
    have hpos : 0 < intervalDomainLift (u τ) x := by
      have hpos0 : 0 < u τ (⟨x, hx⟩ : intervalDomain.Point) :=
        hsol.u_pos' hτ.1 hτ.2
      rw [intervalDomainLift, dif_pos hx]
      exact hpos0
    have huα_nonneg : 0 ≤ (intervalDomainLift (u τ) x) ^ p.α :=
      Real.rpow_nonneg hpos.le _
    have hα1_nonneg : 0 ≤ 1 + p.α := by
      linarith [p.hα]
    have hsub_nonneg :
        0 ≤ p.b * (1 + p.α) *
          (intervalDomainLift (u τ) x) ^ p.α :=
      mul_nonneg (mul_nonneg p.hb hα1_nonneg) huα_nonneg
    have hslope_le_a :
        p.a - p.b * (1 + p.α) *
            (intervalDomainLift (u τ) x) ^ p.α ≤ p.a := by
      linarith
    simpa [H1PhysicalLogisticSlope] using le_trans hslope_le_a hL

/-- The integral defining the H¹ gradient seminorm agrees with the canonical
square-root representative. -/
theorem H1grad_sq_integral_eq_H1gradL2Norm_sq
    (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    (∫ x in (0 : ℝ)..1, (deriv (intervalDomainLift (u τ)) x) ^ 2) =
      (H1gradL2Norm u τ) ^ 2 := by
  rw [H1gradL2Norm_sq, H1energy]
  ring

/-- The reaction IBP data imply the concrete physical reaction bound needed by
the square-root H¹ route. -/
theorem H1PhysicalReactX_le_gradSq_of_reactionIBPBoundDataBefore
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T L : ℝ}
    (h : H1PhysicalReactionIBPBoundDataBefore p u T L) :
    ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1PhysicalReactX p u τ ≤ L * (H1gradL2Norm u τ) ^ 2 := by
  intro τ hτ
  have hright_int :
      IntervalIntegrable
        (fun x => L * (deriv (intervalDomainLift (u τ)) x) ^ 2)
        volume (0 : ℝ) 1 :=
    (h.grad_sq_int τ hτ).const_mul L
  have hmono :
      (∫ x in (0 : ℝ)..1,
        H1PhysicalLogisticSlope p u τ x *
          (deriv (intervalDomainLift (u τ)) x) ^ 2) ≤
        ∫ x in (0 : ℝ)..1,
          L * (deriv (intervalDomainLift (u τ)) x) ^ 2 := by
    refine intervalIntegral.integral_mono_on (μ := volume)
      (a := (0 : ℝ)) (b := 1)
      (f := fun x =>
        H1PhysicalLogisticSlope p u τ x *
          (deriv (intervalDomainLift (u τ)) x) ^ 2)
      (g := fun x => L * (deriv (intervalDomainLift (u τ)) x) ^ 2)
      (by norm_num) (h.slope_grad_sq_int τ hτ) hright_int ?_
    intro x hx
    exact mul_le_mul_of_nonneg_right (h.slope_le τ hτ x hx) (sq_nonneg _)
  calc
    H1PhysicalReactX p u τ
        = ∫ x in (0 : ℝ)..1,
            H1PhysicalLogisticSlope p u τ x *
              (deriv (intervalDomainLift (u τ)) x) ^ 2 := h.react_ibp τ hτ
    _ ≤ ∫ x in (0 : ℝ)..1,
          L * (deriv (intervalDomainLift (u τ)) x) ^ 2 := hmono
    _ = L * ∫ x in (0 : ℝ)..1,
          (deriv (intervalDomainLift (u τ)) x) ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
    _ = L * (H1gradL2Norm u τ) ^ 2 := by
        rw [H1grad_sq_integral_eq_H1gradL2Norm_sq]

/-- Classical solution reaction estimate with any `L ≥ p.a`. -/
theorem H1PhysicalReactX_le_L_H1gradL2Norm_sq_of_classicalSolution
    {p : CM2Params} {T τ L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hL : p.a ≤ L) :
    H1PhysicalReactX p u τ ≤ L * (H1gradL2Norm u τ) ^ 2 :=
  H1PhysicalReactX_le_gradSq_of_reactionIBPBoundDataBefore
    (H1PhysicalReactionIBPBoundDataBefore_of_classicalSolution
      (p := p) (T := T) (L := L) (u := u) (v := v) hsol hL)
    τ hτ

/-- Classical solution reaction estimate with the canonical cap `L = p.a`. -/
theorem H1PhysicalReactX_le_a_H1gradL2Norm_sq_of_classicalSolution
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    H1PhysicalReactX p u τ ≤ p.a * (H1gradL2Norm u τ) ^ 2 :=
  H1PhysicalReactX_le_L_H1gradL2Norm_sq_of_classicalSolution
    (p := p) (T := T) (τ := τ) (L := p.a) (u := u) (v := v)
    hsol hτ le_rfl

/-- The remaining chemotaxis-side fixed-time L² data for the physical H¹
sqrt-bound route, after the logistic reaction estimate has been split off. -/
structure H1PhysicalChemL2SqrtBoundDataBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M : ℝ) : Prop where
  hchi : 0 ≤ -p.χ₀
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  lap_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1
  taxis_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => (H1PhysicalChemTaxisPart p u v τ x) ^ 2) volume (0 : ℝ) 1
  uvxx_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => (H1PhysicalChemUvxxPart p u v τ x) ^ 2) volume (0 : ℝ) 1
  taxis_prod_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x|)
      volume (0 : ℝ) 1
  uvxx_prod_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x|)
      volume (0 : ℝ) 1
  taxis_l2_bound : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
      ≤ V₁ * H1gradL2Norm u τ
  uvxx_l2_bound : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
      ≤ M * V₂

/-- Chemotaxis-side L² sqrt data plus reaction IBP data rebuild the older
all-components L² sqrt data package. -/
theorem H1PhysicalRHSL2SqrtBoundDataBefore_of_chemL2SqrtBoundData_and_reactionIBP
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hchem : H1PhysicalChemL2SqrtBoundDataBefore p u v T V₁ V₂ M)
    (hreact : H1PhysicalReactionIBPBoundDataBefore p u T L) :
    H1PhysicalRHSL2SqrtBoundDataBefore p u v T V₁ V₂ M L :=
  { hchi := hchem.hchi
    hV1 := hchem.hV1
    hV2 := hchem.hV2
    hM := hchem.hM
    hL := hreact.hL
    lap_sq_int := hchem.lap_sq_int
    taxis_sq_int := hchem.taxis_sq_int
    uvxx_sq_int := hchem.uvxx_sq_int
    taxis_prod_int := hchem.taxis_prod_int
    uvxx_prod_int := hchem.uvxx_prod_int
    taxis_l2_bound := hchem.taxis_l2_bound
    uvxx_l2_bound := hchem.uvxx_l2_bound
    react_bound := H1PhysicalReactX_le_gradSq_of_reactionIBPBoundDataBefore hreact }

/-- Chemotaxis-side L² sqrt data plus the classical reaction producer rebuild
the older all-components L² sqrt data package. -/
theorem H1PhysicalRHSL2SqrtBoundDataBefore_of_chemL2SqrtBoundData_and_classical_reaction
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hL : p.a ≤ L)
    (hchem : H1PhysicalChemL2SqrtBoundDataBefore p u v T V₁ V₂ M) :
    H1PhysicalRHSL2SqrtBoundDataBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSL2SqrtBoundDataBefore_of_chemL2SqrtBoundData_and_reactionIBP
    hchem
    (H1PhysicalReactionIBPBoundDataBefore_of_classicalSolution
      (p := p) (T := T) (L := L) (u := u) (v := v) hsol hL)

/-- Chemotaxis-side L² sqrt data plus reaction IBP data produce the concrete
physical H¹ sqrt-bound frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_chemL2SqrtBoundData_and_reactionIBP
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hchem : H1PhysicalChemL2SqrtBoundDataBefore p u v T V₁ V₂ M)
    (hreact : H1PhysicalReactionIBPBoundDataBefore p u T L) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_L2SqrtBoundData
    (H1PhysicalRHSL2SqrtBoundDataBefore_of_chemL2SqrtBoundData_and_reactionIBP
      hchem hreact)

/-- Chemotaxis-side L² sqrt data plus the classical logistic reaction producer
give the concrete physical H¹ sqrt-bound frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_chemL2SqrtBoundData_and_classical_reaction
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hL : p.a ≤ L)
    (hchem : H1PhysicalChemL2SqrtBoundDataBefore p u v T V₁ V₂ M) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_L2SqrtBoundData
    (H1PhysicalRHSL2SqrtBoundDataBefore_of_chemL2SqrtBoundData_and_classical_reaction
      hsol hL hchem)

/-- Pointwise taxis/uvxx estimates plus reaction IBP data produce the concrete
physical H¹ sqrt-bound frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds_and_reactionIBP
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hchi : 0 ≤ -p.χ₀)
    (hV1 : 0 ≤ V₁) (hV2 : 0 ≤ V₂) (hM : 0 ≤ M)
    (htaxis_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      |H1PhysicalTaxisX p u v τ| ≤
        V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ))
    (huvxx_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      |H1PhysicalUvxxX p u v τ| ≤ M * (V₂ * H1lapL2Norm u τ))
    (hreact : H1PhysicalReactionIBPBoundDataBefore p u T L) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds
    hchi hV1 hV2 hM hreact.hL htaxis_abs huvxx_abs
    (H1PhysicalReactX_le_gradSq_of_reactionIBPBoundDataBefore hreact)

/-- Pointwise taxis/uvxx estimates plus the classical logistic reaction IBP
producer give the physical H¹ sqrt-bound frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds_and_classical_reaction
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hV1 : 0 ≤ V₁) (hV2 : 0 ≤ V₂) (hM : 0 ≤ M)
    (hL : p.a ≤ L)
    (htaxis_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      |H1PhysicalTaxisX p u v τ| ≤
        V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ))
    (huvxx_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      |H1PhysicalUvxxX p u v τ| ≤ M * (V₂ * H1lapL2Norm u τ)) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds_and_reactionIBP
    hchi hV1 hV2 hM htaxis_abs huvxx_abs
    (H1PhysicalReactionIBPBoundDataBefore_of_classicalSolution
      (p := p) (T := T) (L := L) (u := u) (v := v) hsol hL)

#print axioms H1PhysicalLogisticReactionPart_hasDerivAt_of_classicalSolution
#print axioms H1PhysicalReactX_eq_logisticSlope_grad_sq_of_classicalSolution
#print axioms H1PhysicalReactionIBPBoundDataBefore_of_classicalSolution
#print axioms H1grad_sq_integral_eq_H1gradL2Norm_sq
#print axioms H1PhysicalReactX_le_gradSq_of_reactionIBPBoundDataBefore
#print axioms H1PhysicalReactX_le_L_H1gradL2Norm_sq_of_classicalSolution
#print axioms H1PhysicalReactX_le_a_H1gradL2Norm_sq_of_classicalSolution
#print axioms H1PhysicalRHSL2SqrtBoundDataBefore_of_chemL2SqrtBoundData_and_reactionIBP
#print axioms H1PhysicalRHSL2SqrtBoundDataBefore_of_chemL2SqrtBoundData_and_classical_reaction
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_chemL2SqrtBoundData_and_reactionIBP
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_chemL2SqrtBoundData_and_classical_reaction
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds_and_reactionIBP
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds_and_classical_reaction

end ShenWork.Paper2.IntervalChiNegH1PhysicalReactionBound
