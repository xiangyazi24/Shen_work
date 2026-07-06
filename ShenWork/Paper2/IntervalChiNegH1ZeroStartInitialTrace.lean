import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
import ShenWork.PDE.IntervalDomainExistence

/-!
# Initial trace reducer for the zero-start H1 physical route

This file isolates the source-facing pointwise trace needed at `t = 0`.
It does not try to manufacture that trace from positive-time classical data,
Moser/FTC scalar data, or downstream H1 hypotheses.
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

private lemma ellipticV_reaction_core_zero (p : CM2Params) (c : ℝ) :
    p.μ * ellipticV p c - p.ν * c ^ p.γ = 0 := by
  unfold ellipticV
  field_simp [p.hμ.ne']
  ring

/-- Source-facing initial `u`-PDE trace together with the initial chemotaxis
representative seam.  This is exactly the pointwise `t = 0` content needed by
the zero-start H1 route; it carries neither closed-slab time continuity nor any
downstream H1 boundedness/sqrt package. -/
structure H1ZeroStartLiteralUPDETraceWithChemRepBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) : Prop where
  pde0 : ∀ X : intervalDomainPoint, X.1 ∈ Set.Ioo (0 : ℝ) 1 →
    intervalDomain.timeDeriv u (0 : ℝ) X =
      intervalDomain.laplacian (u (0 : ℝ)) X -
        p.χ₀ * intervalDomain.chemotaxisDiv p (u (0 : ℝ)) (v (0 : ℝ)) X +
        u (0 : ℝ) X * (p.a - p.b * (u (0 : ℝ) X) ^ p.α)
  chem0 : ∀ X : intervalDomainPoint, X.1 ∈ Set.Ioo (0 : ℝ) 1 →
    intervalDomainLift
        (fun Y : intervalDomainPoint =>
          intervalDomain.chemotaxisDiv p (u (0 : ℝ)) (v (0 : ℝ)) Y) X.1 =
      liftChemotaxisDivPhysicalRep p u v (0 : ℝ) X.1

/-- A literal initial `u`-PDE trace plus the initial chemotaxis-representative
seam implies the `eq0Interior` field used by
`H1ZeroStartPhysicalPDEInitialCompatibilityBefore`. -/
theorem eq0Interior_of_initialLiteralUPDETrace_withChemRep
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1ZeroStartLiteralUPDETraceWithChemRepBefore p u v) :
    Set.EqOn
      (fun x => liftDeriv2 u (0 : ℝ) x)
      (fun x =>
        liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v) (0 : ℝ) x)
      (Set.Ioo (0 : ℝ) 1) := by
  classical
  intro x hx
  let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have htime_lift :
      liftTimeDeriv u (0 : ℝ) x = intervalDomain.timeDeriv u (0 : ℝ) X := by
    simp [liftTimeDeriv, intervalDomain, intervalDomainLift, hxIcc, X]
  have hlap :
      liftDeriv2 u (0 : ℝ) x =
        intervalDomain.laplacian (u (0 : ℝ)) X := by
    simp [liftDeriv2, intervalDomain, intervalDomainLaplacian, X]
  have hu_lift :
      intervalDomainLift (u (0 : ℝ)) x = u (0 : ℝ) X := by
    simp [intervalDomainLift, hxIcc, X]
  have hchem_lift :
      intervalDomainLift
          (fun Y : intervalDomainPoint =>
            intervalDomain.chemotaxisDiv p (u (0 : ℝ)) (v (0 : ℝ)) Y) x =
        intervalDomain.chemotaxisDiv p (u (0 : ℝ)) (v (0 : ℝ)) X := by
    simp [intervalDomainLift, hxIcc, X]
  have hchem :
      intervalDomain.chemotaxisDiv p (u (0 : ℝ)) (v (0 : ℝ)) X =
        liftChemotaxisDivPhysicalRep p u v (0 : ℝ) x := by
    rw [← hchem_lift]
    simpa [X] using h.chem0 X hx
  have hpde := h.pde0 X hx
  have hsolve :
      intervalDomain.laplacian (u (0 : ℝ)) X =
        intervalDomain.timeDeriv u (0 : ℝ) X +
          p.χ₀ * intervalDomain.chemotaxisDiv p (u (0 : ℝ)) (v (0 : ℝ)) X -
          u (0 : ℝ) X * (p.a - p.b * (u (0 : ℝ) X) ^ p.α) := by
    linarith
  calc
    liftDeriv2 u (0 : ℝ) x =
        intervalDomain.laplacian (u (0 : ℝ)) X := hlap
    _ = intervalDomain.timeDeriv u (0 : ℝ) X +
          p.χ₀ * intervalDomain.chemotaxisDiv p (u (0 : ℝ)) (v (0 : ℝ)) X -
          u (0 : ℝ) X * (p.a - p.b * (u (0 : ℝ) X) ^ p.α) := hsolve
    _ =
        liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v) (0 : ℝ) x := by
      rw [← htime_lift, hchem, ← hu_lift]

#print axioms eq0Interior_of_initialLiteralUPDETrace_withChemRep

/-- Constant-in-time/space sources with zero logistic reaction satisfy the
literal initial PDE trace and chemotaxis-representative seam.  This is the
initial-trace companion to `H1ZeroStartClosedPrimitiveC1SignBefore_const`; it is
not a general B-form/Picard producer. -/
theorem H1ZeroStartLiteralUPDETraceWithChemRepBefore_const
    (p : CM2Params) {c : ℝ}
    (hreact : c * (p.a - p.b * c ^ p.α) = 0) :
    H1ZeroStartLiteralUPDETraceWithChemRepBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c) where
  pde0 := by
    intro X hx
    have hxInside : X ∈ intervalDomain.inside := by
      simpa [intervalDomain] using hx
    change deriv (fun _s : ℝ => c) (0 : ℝ) =
      intervalDomainLaplacian (fun _ : intervalDomainPoint => c) X -
        p.χ₀ * intervalDomainChemotaxisDiv p
          (fun _ : intervalDomainPoint => c)
          (fun _ : intervalDomainPoint => ellipticV p c) X +
        c * (p.a - p.b * c ^ p.α)
    rw [deriv_const, intervalDomainLaplacian_const_zero c hxInside,
      intervalDomainChemotaxisDiv_const_zero p c (ellipticV p c) hxInside,
      hreact]
    ring
  chem0 := by
    intro X hx
    have hxIcc : X.1 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hxInside : X ∈ intervalDomain.inside := by
      simpa [intervalDomain] using hx
    have hu_deriv :
        deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) X.1 = 0 :=
      intervalDomainLift_const_deriv_zero c hx
    have hv_deriv :
        deriv
            (intervalDomainLift
              (fun _ : intervalDomainPoint => ellipticV p c)) X.1 = 0 :=
      intervalDomainLift_const_deriv_zero (ellipticV p c) hx
    have hchem_zero :
        intervalDomainChemotaxisDiv p
          (fun _ : intervalDomainPoint => c)
          (fun _ : intervalDomainPoint => ellipticV p c) X = 0 :=
      intervalDomainChemotaxisDiv_const_zero p c (ellipticV p c) hxInside
    calc
      intervalDomainLift
          (fun Y : intervalDomainPoint =>
            intervalDomain.chemotaxisDiv p
              ((fun _ (_ : intervalDomainPoint) => c) (0 : ℝ))
              ((fun _ (_ : intervalDomainPoint) => ellipticV p c) (0 : ℝ)) Y)
          X.1
          = 0 := by
            simp [intervalDomain, intervalDomainLift, hxIcc, hchem_zero]
      _ = liftChemotaxisDivPhysicalRep p
          (fun _ (_ : intervalDomainPoint) => c)
          (fun _ (_ : intervalDomainPoint) => ellipticV p c) (0 : ℝ) X.1 := by
            simp [liftChemotaxisDivPhysicalRep, intervalDomainLift, hxIcc,
              hu_deriv, hv_deriv, ellipticV_reaction_core_zero]

#print axioms H1ZeroStartLiteralUPDETraceWithChemRepBefore_const

/-- Equilibrium constants satisfy the literal initial trace package. -/
theorem H1ZeroStartLiteralUPDETraceWithChemRepBefore_equilibrium
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    H1ZeroStartLiteralUPDETraceWithChemRepBefore p
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      (fun _ (_ : intervalDomainPoint) =>
        ellipticV p ((p.a / p.b) ^ (1 / p.α))) :=
  H1ZeroStartLiteralUPDETraceWithChemRepBefore_const p
    (by
      rw [equilibrium_reaction_zero p ha hb]
      ring)

/-- Zero-reaction constants satisfy the literal initial trace package. -/
theorem H1ZeroStartLiteralUPDETraceWithChemRepBefore_zeroReaction
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (c : ℝ) :
    H1ZeroStartLiteralUPDETraceWithChemRepBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c) :=
  H1ZeroStartLiteralUPDETraceWithChemRepBefore_const p
    (by
      rw [ha, hb]
      ring)

#print axioms H1ZeroStartLiteralUPDETraceWithChemRepBefore_equilibrium
#print axioms H1ZeroStartLiteralUPDETraceWithChemRepBefore_zeroReaction

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
