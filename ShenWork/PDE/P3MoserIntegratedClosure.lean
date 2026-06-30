import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-!
This file isolates the routine part of the integrated-Moser route.  The hard
PDE step is represented by `IntegratedMoserFirstCrossingStep`; downstream
iteration and endpoint closure are proved here from that step.
-/

/-- Closed-time and time-integrability data needed by an integrated
first-crossing Moser step.  The existing L2 closed-energy bridge is not enough:
this data is indexed by every exponent `p >= p0` used in the ladder. -/
structure IntegratedMoserFirstCrossingRegularity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  initialPowerBound :
    ∀ p, p0 ≤ p →
      ∃ C0, 0 ≤ C0 ∧
        D.integral (fun x => (u 0 x) ^ p) ≤ C0
  powerTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- The one-step output needed from the integrated first-crossing argument. -/
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u

/-- Iterate a supplied integrated first-crossing step along the arithmetic
Moser ladder. -/
theorem moser_iteration_chain_of_integrated_first_crossing_step
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
      simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      exact hbase
  | succ n ih =>
      have hexp_eq :
          p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
        push_cast
        ring
      rw [hexp_eq]
      have hp_ge : p0 ≤ p0 + ↑n * rho :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
      exact hstep (p0 + ↑n * rho) hp_ge ih

/-- A supplied integrated first-crossing step plus downward Lp monotonicity
gives all finite exponents. -/
theorem all_exponents_of_integrated_first_crossing_step_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_integrated_first_crossing_step
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      hstep)
    hLpMono

/-- Interval-domain finite-horizon boundedness from a supplied integrated
first-crossing step and the existing quantitative endpoint. -/
theorem intervalDomain_boundedBefore_of_integrated_first_crossing_step
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u :=
    all_exponents_of_integrated_first_crossing_step_lpmono
      hboot hstep hLpMono
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hEndpoint hAll)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
