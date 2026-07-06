import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-!
# Initial trace reducer for the zero-start H1 physical route

This file isolates the source-facing pointwise trace needed at `t = 0`.
It does not try to manufacture that trace from positive-time classical data,
Moser/FTC scalar data, or downstream H1 hypotheses.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

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

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
