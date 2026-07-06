import ShenWork.Paper2.IntervalChiNegH1ZeroStartConstant
import ShenWork.Paper2.IntervalChiNegH1ZeroStartInitialTrace
import ShenWork.Paper2.IntervalChiNegH1ZeroStartInitializedPrimitive

/-!
# Constant zero-start primitive-data producers

This file connects the constant closed-slab primitive source package and the
constant literal initial trace package to the older route-facing
`H1ZeroStartPhysicalPrimitiveDataBefore` frontier.  It records only the
constant equilibrium / zero-reaction regimes; it is not a general producer for
the B-form/Picard construction.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-- A p-free closed primitive package plus explicit zero-slice equalities
supplies the initialized source guard.  This is only a wrapper: the closed
zero-start fields still come from the source package. -/
theorem H1ZeroStartInitializedPrimitiveC1SignSource_of_closedPrimitiveC1Sign
    {u₀ v₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hu0 : u (0 : ℝ) = u₀)
    (hv0 : v (0 : ℝ) = v₀)
    (h : H1ZeroStartClosedPrimitiveC1SignBefore u v T) :
    H1ZeroStartInitializedPrimitiveC1SignSource u₀ v₀ u v T where
  u_zero := hu0
  v_zero := hv0
  u_cont0 := h.u_cont0
  v_cont0 := h.v_cont0
  ux_cont0 := h.ux_cont0
  vx_cont0 := h.vx_cont0
  u_pos0 := h.u_pos0
  v_nonneg0 := h.v_nonneg0

/-- Constant positive trajectories supply the initialized primitive guard. -/
theorem H1ZeroStartInitializedPrimitiveC1SignSource_const
    (p : CM2Params) {c T : ℝ} (hc : 0 < c) :
    H1ZeroStartInitializedPrimitiveC1SignSource
      (fun _ : intervalDomainPoint => c)
      (fun _ : intervalDomainPoint => ellipticV p c)
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T :=
  H1ZeroStartInitializedPrimitiveC1SignSource_of_closedPrimitiveC1Sign
    (u := fun _ (_ : intervalDomainPoint) => c)
    (v := fun _ (_ : intervalDomainPoint) => ellipticV p c)
    (T := T) rfl rfl
    (H1ZeroStartClosedPrimitiveC1SignBefore_const
      (p := p) (c := c) (T := T) hc)

/-- Constant reaction equilibria satisfy the route-facing initial PDE
compatibility package. -/
theorem H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_of_reaction_zero
    (p : CM2Params) {c T : ℝ}
    (hreact : c * (p.a - p.b * c ^ p.α) = 0) :
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T where
  time_cont0 := by
    intro b _hb _hbT
    refine
      (continuousOn_const :
        ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ))
          (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)).congr ?_
    intro q _hq
    rcases q with ⟨t, x⟩
    simp only [Function.uncurry]
    change liftTimeDeriv (fun _ (_ : intervalDomainPoint) => c) t x = 0
    change deriv
      (fun _s : ℝ => intervalDomainLift (fun _ : intervalDomainPoint => c) x)
      t = 0
    exact deriv_const t (intervalDomainLift (fun _ : intervalDomainPoint => c) x)
  eq0Interior :=
    eq0Interior_of_initialLiteralUPDETrace_withChemRep
      (H1ZeroStartLiteralUPDETraceWithChemRepBefore_const
        (p := p) hreact)

/-- Equilibrium constants satisfy the route-facing initial PDE compatibility
package. -/
theorem H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_equilibrium
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) {T : ℝ} :
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore p
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      (fun _ (_ : intervalDomainPoint) =>
        ellipticV p ((p.a / p.b) ^ (1 / p.α)))
      T := by
  refine
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_of_reaction_zero
      (p := p) ?_
  rw [equilibrium_reaction_zero p ha hb]
  ring

/-- Zero-reaction constants satisfy the route-facing initial PDE compatibility
package. -/
theorem H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_zeroReaction
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) {c T : ℝ} :
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T := by
  refine
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_of_reaction_zero
      (p := p) ?_
  rw [ha, hb]
  ring

/-- Equilibrium constants supply the older full zero-start primitive-data
frontier. -/
theorem H1ZeroStartPhysicalPrimitiveDataBefore_const_equilibrium
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) {T : ℝ}
    (hT : 0 < T) :
    H1ZeroStartPhysicalPrimitiveDataBefore p
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      (fun _ (_ : intervalDomainPoint) =>
        ellipticV p ((p.a / p.b) ^ (1 / p.α)))
      T := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  have hc : 0 < c := equilibrium_pos p ha hb
  have hcont :
      H1ZeroStartPhysicalPrimitiveContinuityBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPrimitiveContinuityBefore_of_closedPrimitiveC1Sign
      (p := p)
      (H1ZeroStartClosedPrimitiveC1SignBefore_const
        (p := p) (c := c) (T := T) hc)
  have hinit :
      H1ZeroStartPhysicalPDEInitialCompatibilityBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_equilibrium
      (p := p) ha hb
  have hseam :
      H1ZeroStartPhysicalPDESeamBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPDESeamBefore_of_classicalSolution_initialCompatibility
      (p := p) (T := T)
      ((equilibrium_isPaper2ClassicalSolution p ha hb) T hT)
      hinit
  exact
    H1ZeroStartPhysicalPrimitiveDataBefore_of_continuity_and_pdeSeam
      hcont hseam

/-- Zero-reaction constants supply the older full zero-start primitive-data
frontier. -/
theorem H1ZeroStartPhysicalPrimitiveDataBefore_const_zeroReaction
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) {c T : ℝ}
    (hc : 0 < c) (hT : 0 < T) :
    H1ZeroStartPhysicalPrimitiveDataBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T := by
  have hcont :
      H1ZeroStartPhysicalPrimitiveContinuityBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPrimitiveContinuityBefore_of_closedPrimitiveC1Sign
      (p := p)
      (H1ZeroStartClosedPrimitiveC1SignBefore_const
        (p := p) (c := c) (T := T) hc)
  have hinit :
      H1ZeroStartPhysicalPDEInitialCompatibilityBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_zeroReaction
      (p := p) ha hb
  have hseam :
      H1ZeroStartPhysicalPDESeamBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPDESeamBefore_of_classicalSolution_initialCompatibility
      (p := p) (T := T)
      ((zeroReaction_isPaper2ClassicalSolution p ha hb c hc) T hT)
      hinit
  exact
    H1ZeroStartPhysicalPrimitiveDataBefore_of_continuity_and_pdeSeam
      hcont hseam

section AxiomAudit

#print axioms H1ZeroStartInitializedPrimitiveC1SignSource_of_closedPrimitiveC1Sign
#print axioms H1ZeroStartInitializedPrimitiveC1SignSource_const
#print axioms H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_of_reaction_zero
#print axioms H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_equilibrium
#print axioms H1ZeroStartPhysicalPDEInitialCompatibilityBefore_const_zeroReaction
#print axioms H1ZeroStartPhysicalPrimitiveDataBefore_const_equilibrium
#print axioms H1ZeroStartPhysicalPrimitiveDataBefore_const_zeroReaction

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
