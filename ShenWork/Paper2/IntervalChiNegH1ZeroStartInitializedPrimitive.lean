import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-!
# Initialized primitive C1/sign reducer for the zero-start H1 route

The raw B-form/Picard local output stores the value `0` at `t = 0`, so it must
not be fed directly into the zero-start primitive C1/sign frontier.  This file
adds a source-facing guard package that records the actual initialized zero
slices together with the closed-zero-slab primitive data.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-- Source-facing initialized primitive C1/sign data for a zero-start
trajectory.  The zero-slice fields are not consumed by the current target
record, but they keep the source interface from being accidentally instantiated
by raw trajectories whose stored value at `t = 0` is not the initial datum. -/
structure H1ZeroStartInitializedPrimitiveC1SignSource
    (u₀ v₀ : intervalDomainPoint → ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  u_zero : u (0 : ℝ) = u₀
  v_zero : v (0 : ℝ) = v₀
  u_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  v_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  ux_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  vx_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  u_pos0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 <
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z
  v_nonneg0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 ≤
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z

/-- An initialized source package supplies the p-free closed primitive
continuity/sign frontier.  This theorem is deliberately just a projection: the
construction layer still has to prove the closed-zero-slab fields. -/
theorem H1ZeroStartClosedPrimitiveC1SignBefore_of_initializedSource
    {u₀ v₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h : H1ZeroStartInitializedPrimitiveC1SignSource u₀ v₀ u v T) :
    H1ZeroStartClosedPrimitiveC1SignBefore u v T where
  u_cont0 := h.u_cont0
  v_cont0 := h.v_cont0
  ux_cont0 := h.ux_cont0
  vx_cont0 := h.vx_cont0
  u_pos0 := h.u_pos0
  v_nonneg0 := h.v_nonneg0

#print axioms H1ZeroStartClosedPrimitiveC1SignBefore_of_initializedSource

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
