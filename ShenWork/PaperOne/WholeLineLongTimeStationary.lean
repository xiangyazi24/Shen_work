import ShenWork.PaperOne.WholeLineLongTimeLimit
import ShenWork.PaperOne.WholeLineFrozenSignal
import ShenWork.PaperOne.WholeLineExponentialBarrierTrapping

open Filter
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Stationarity of the long-time limit of the whole-line auxiliary flow.

The parabolic compactness inputs are kept as named hypotheses.  In particular,
`time_derivative_tendsto_zero` is the regularized consequence of time
monotonicity plus convergence, while the two spatial derivative convergence
fields are the Schauder-limit inputs.  This file assembles those hypotheses
with the pointwise auxiliary equation.
-/

/-- Named long-time limit data for the auxiliary moving-frame equation. -/
structure WholeLineLongTimeStationarityData
    (p : CMParams) (c : ℝ)
    (w wt wx wxx : ℝ → ℝ → ℝ) (U V Vx : ℝ → ℝ) : Prop where
  orbit_tendsto :
    ∀ x, Tendsto (fun t : ℝ => w t x) atTop (𝓝 (U x))
  time_derivative_tendsto_zero :
    ∀ x, Tendsto (fun t : ℝ => wt t x) atTop (𝓝 0)
  spatial_derivative_tendsto :
    ∀ x, Tendsto (fun t : ℝ => wx t x) atTop (𝓝 (deriv U x))
  spatial_second_derivative_tendsto :
    ∀ x, Tendsto (fun t : ℝ => wxx t x) atTop
      (𝓝 (iteratedDeriv 2 U x))
  evolution_eq :
    ∀ t x,
      wt t x =
        wxx t x + c * wx t x +
          auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x

namespace WholeLineLongTimeStationarityData

/-- The frozen nonlinear source converges after the carried pointwise
parabolic-limit hypotheses are applied. -/
theorem nonlinearity_tendsto
    {p : CMParams} {c : ℝ}
    {w wt wx wxx : ℝ → ℝ → ℝ} {U V Vx : ℝ → ℝ}
    (H : WholeLineLongTimeStationarityData p c w wt wx wxx U V Vx)
    (x : ℝ) :
    Tendsto
      (fun t : ℝ => auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x)
      atTop
      (𝓝 (auxiliaryFrozenNonlinearity p U (fun y => deriv U y) V Vx x)) := by
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hγ_nonneg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hpow_m_sub_one :
      Tendsto (fun t : ℝ => (w t x) ^ (p.m - 1)) atTop
        (𝓝 ((U x) ^ (p.m - 1))) :=
    (H.orbit_tendsto x).rpow_const (Or.inr (sub_nonneg.mpr p.hm))
  have hpow_m :
      Tendsto (fun t : ℝ => (w t x) ^ p.m) atTop
        (𝓝 ((U x) ^ p.m)) :=
    (H.orbit_tendsto x).rpow_const (Or.inr hm_nonneg)
  have hpow_m_add_γ :
      Tendsto (fun t : ℝ => (w t x) ^ (p.m + p.γ)) atTop
        (𝓝 ((U x) ^ (p.m + p.γ))) :=
    (H.orbit_tendsto x).rpow_const
      (Or.inr (add_nonneg hm_nonneg hγ_nonneg))
  have hpow_α :
      Tendsto (fun t : ℝ => (w t x) ^ p.α) atTop
        (𝓝 ((U x) ^ p.α)) :=
    (H.orbit_tendsto x).rpow_const (Or.inr hα_nonneg)
  have hterm_grad :
      Tendsto
        (fun t : ℝ =>
          -p.χ * p.m * (w t x) ^ (p.m - 1) * wx t x * Vx x)
        atTop
        (𝓝 (-p.χ * p.m * (U x) ^ (p.m - 1) * deriv U x * Vx x)) :=
    ((hpow_m_sub_one.const_mul (-p.χ * p.m)).mul
      (H.spatial_derivative_tendsto x)).mul tendsto_const_nhds
  have hterm_absorb :
      Tendsto
        (fun t : ℝ => p.χ * (w t x) ^ p.m * V x)
        atTop
        (𝓝 (p.χ * (U x) ^ p.m * V x)) :=
    (hpow_m.const_mul p.χ).mul tendsto_const_nhds
  have hterm_power :
      Tendsto
        (fun t : ℝ => p.χ * (w t x) ^ (p.m + p.γ))
        atTop
        (𝓝 (p.χ * (U x) ^ (p.m + p.γ))) :=
    hpow_m_add_γ.const_mul p.χ
  have hreaction :
      Tendsto
        (fun t : ℝ => w t x * (1 - (w t x) ^ p.α))
        atTop
        (𝓝 (U x * (1 - (U x) ^ p.α))) :=
    (H.orbit_tendsto x).mul (tendsto_const_nhds.sub hpow_α)
  have hsum :=
    ((hterm_grad.sub hterm_absorb).add hterm_power).add hreaction
  simpa [auxiliaryFrozenNonlinearity, wholeLineReaction] using hsum

/-- The right-hand side of the auxiliary equation converges to the stationary
residual of the limiting profile. -/
theorem residual_tendsto
    {p : CMParams} {c : ℝ}
    {w wt wx wxx : ℝ → ℝ → ℝ} {U V Vx : ℝ → ℝ}
    (H : WholeLineLongTimeStationarityData p c w wt wx wxx U V Vx)
    (x : ℝ) :
    Tendsto
      (fun t : ℝ =>
        wxx t x + c * wx t x +
          auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x)
      atTop
      (𝓝 (auxiliaryStationaryResidual p c U (fun y => deriv U y)
        (fun y => iteratedDeriv 2 U y) V Vx x)) := by
  have hlinear :
      Tendsto (fun t : ℝ => wxx t x + c * wx t x) atTop
        (𝓝 (iteratedDeriv 2 U x + c * deriv U x)) :=
    (H.spatial_second_derivative_tendsto x).add
      ((H.spatial_derivative_tendsto x).const_mul c)
  have hsum := hlinear.add (H.nonlinearity_tendsto x)
  simpa [auxiliaryStationaryResidual] using hsum

end WholeLineLongTimeStationarityData

/-- Profile-level assembly: if an auxiliary orbit converges with the named
parabolic estimates, then its limit has zero stationary residual. -/
theorem wholeLine_longTime_stationary_of_profile
    {p : CMParams} {c : ℝ}
    {w wt wx wxx : ℝ → ℝ → ℝ} {U V Vx : ℝ → ℝ}
    (H : WholeLineLongTimeStationarityData p c w wt wx wxx U V Vx) :
    ∀ x,
      auxiliaryStationaryResidual p c U (fun y => deriv U y)
        (fun y => iteratedDeriv 2 U y) V Vx x = 0 := by
  intro x
  have hrhs_zero :
      Tendsto
        (fun t : ℝ =>
          wxx t x + c * wx t x +
            auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x)
        atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ (H.time_derivative_tendsto_zero x)
    exact Eventually.of_forall fun t => H.evolution_eq t x
  have hrhs_residual := H.residual_tendsto x
  exact (tendsto_nhds_unique hrhs_zero hrhs_residual).symm

/--
Stationarity of the Brick-9 whole-line long-time limit for the frozen input
`u`, with `V = Ψ(u^γ)`.
-/
theorem wholeLine_longTime_stationary
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ}
    {w wt wx wxx : ℝ → ℝ → ℝ}
    (H : WholeLineLongTimeStationarityData p c w wt wx wxx
      (wholeLineLongTimeLimit w)
      (frozenSignal p.γ u)
      (fun x => deriv (frozenSignal p.γ u) x)) :
    ∀ x,
      auxiliaryStationaryResidual p c (wholeLineLongTimeLimit w)
        (fun y => deriv (wholeLineLongTimeLimit w) y)
        (fun y => iteratedDeriv 2 (wholeLineLongTimeLimit w) y)
        (frozenSignal p.γ u)
        (fun y => deriv (frozenSignal p.γ u) y) x = 0 :=
  wholeLine_longTime_stationary_of_profile H

/-- Expanded pointwise form of `wholeLine_longTime_stationary`. -/
theorem wholeLine_longTime_stationary_expanded
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ}
    {w wt wx wxx : ℝ → ℝ → ℝ}
    (H : WholeLineLongTimeStationarityData p c w wt wx wxx
      (wholeLineLongTimeLimit w)
      (frozenSignal p.γ u)
      (fun x => deriv (frozenSignal p.γ u) x)) :
    ∀ x,
      iteratedDeriv 2 (wholeLineLongTimeLimit w) x
        + c * deriv (wholeLineLongTimeLimit w) x
        - p.χ * p.m * (wholeLineLongTimeLimit w x) ^ (p.m - 1)
            * deriv (wholeLineLongTimeLimit w) x
            * deriv (frozenSignal p.γ u) x
        - p.χ * (wholeLineLongTimeLimit w x) ^ p.m
            * frozenSignal p.γ u x
        + p.χ * (wholeLineLongTimeLimit w x) ^ (p.m + p.γ)
        + wholeLineLongTimeLimit w x
            * (1 - (wholeLineLongTimeLimit w x) ^ p.α) = 0 := by
  intro x
  have h := wholeLine_longTime_stationary H x
  rw [auxiliaryStationaryResidual, auxiliaryFrozenNonlinearity,
    wholeLineReaction] at h
  ring_nf at h ⊢
  exact h

#print axioms WholeLineLongTimeStationarityData.nonlinearity_tendsto
#print axioms WholeLineLongTimeStationarityData.residual_tendsto
#print axioms wholeLine_longTime_stationary_of_profile
#print axioms wholeLine_longTime_stationary
#print axioms wholeLine_longTime_stationary_expanded

end ShenWork.PaperOne
