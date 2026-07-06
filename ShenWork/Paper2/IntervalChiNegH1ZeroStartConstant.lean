import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
import ShenWork.PDE.IntervalDomainExistence

/-!
# Constant zero-start primitive data for the H¹ physical route

This file records the source-visible constant-solution special case for the
zero-start primitive C¹/sign frontier.  It does not claim a general producer for
the B-form/Picard construction.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

private lemma intervalDomainLift_const_deriv_zero_Icc (c : ℝ) :
    Set.EqOn
      (fun x : ℝ => deriv (intervalDomainLift
        (fun _ : intervalDomainPoint => c)) x)
      (fun _ : ℝ => (0 : ℝ))
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  by_cases h0 : x = 0
  · subst x
    exact (intervalDomainLift_const_deriv_endpoint_zero c).1
  by_cases h1 : x = 1
  · subst x
    exact (intervalDomainLift_const_deriv_endpoint_zero c).2
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm h0), lt_of_le_of_ne hx.2 h1⟩
  exact intervalDomainLift_const_deriv_zero c hxIoo

private theorem const_lift_closed_zero_slab_continuousOn (c b : ℝ) :
    ContinuousOn
      (Function.uncurry
        (fun (_t : ℝ) (x : ℝ) =>
          intervalDomainLift (fun _ : intervalDomainPoint => c) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine (continuousOn_const :
    ContinuousOn (fun _ : ℝ × ℝ => c)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)).congr ?_
  intro z hz
  rcases z with ⟨_t, x⟩
  simp [Function.uncurry, intervalDomainLift_const, hz.2]

private theorem const_lift_deriv_closed_zero_slab_continuousOn (c b : ℝ) :
    ContinuousOn
      (Function.uncurry
        (fun (_t : ℝ) (x : ℝ) =>
          deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine (continuousOn_const :
    ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)).congr ?_
  intro z hz
  rcases z with ⟨_t, x⟩
  exact intervalDomainLift_const_deriv_zero_Icc c hz.2

/-- Constant-in-time/space positive solution data produce the zero-start
primitive C¹/sign source package.  This is a special-case producer, not a
general B-form/Picard construction producer. -/
theorem H1ZeroStartClosedPrimitiveC1SignBefore_const
    (p : CM2Params) {c T : ℝ} (hc : 0 < c) :
    H1ZeroStartClosedPrimitiveC1SignBefore
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T where
  u_cont0 := by
    intro b _hb _hbT
    simpa using const_lift_closed_zero_slab_continuousOn c b
  v_cont0 := by
    intro b _hb _hbT
    simpa using const_lift_closed_zero_slab_continuousOn (ellipticV p c) b
  ux_cont0 := by
    intro b _hb _hbT
    simpa using const_lift_deriv_closed_zero_slab_continuousOn c b
  vx_cont0 := by
    intro b _hb _hbT
    simpa using const_lift_deriv_closed_zero_slab_continuousOn (ellipticV p c) b
  u_pos0 := by
    intro _b _hb _hbT z hz
    rcases z with ⟨_t, x⟩
    simpa [Function.uncurry, intervalDomainLift_const, hz.2] using hc
  v_nonneg0 := by
    intro _b _hb _hbT z hz
    rcases z with ⟨_t, x⟩
    simpa [Function.uncurry, intervalDomainLift_const, hz.2] using
      (ellipticV_pos p hc).le

section AxiomAudit

#print axioms H1ZeroStartClosedPrimitiveC1SignBefore_const

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
