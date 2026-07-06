import ShenWork.Paper2.IntervalChiNegH1ZeroStartConstantPrimitiveData
import ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial

/-!
# Constant zero-start physical H1 route lowerers

This file lowers the constant zero-start primitive-data producers to the
route-facing zero-window RHS interfaces.  It does not claim bounded-before or
close the physical strict/initial route.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
open ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-- Constant equilibrium primitive data immediately gives the concrete
zero-start physical RHS data package. -/
theorem H1ZeroStartPhysicalRHSDataBefore_const_equilibrium
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) {T : ℝ}
    (hT : 0 < T) :
    H1ZeroStartPhysicalRHSDataBefore p
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      (fun _ (_ : intervalDomainPoint) =>
        ellipticV p ((p.a / p.b) ^ (1 / p.α)))
      T :=
  H1ZeroStartPhysicalRHSDataBefore_of_zeroStartPrimitiveData
    (H1ZeroStartPhysicalPrimitiveDataBefore_const_equilibrium
      (p := p) ha hb (T := T) hT)

/-- Zero-reaction constant primitive data immediately gives the concrete
zero-start physical RHS data package. -/
theorem H1ZeroStartPhysicalRHSDataBefore_const_zeroReaction
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) {c T : ℝ}
    (hc : 0 < c) (hT : 0 < T) :
    H1ZeroStartPhysicalRHSDataBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T :=
  H1ZeroStartPhysicalRHSDataBefore_of_zeroStartPrimitiveData
    (H1ZeroStartPhysicalPrimitiveDataBefore_const_zeroReaction
      (p := p) ha hb (c := c) (T := T) hc hT)

/-- Constant equilibrium primitive data gives the before-`T` zero-slab
representative used by the lap-component route. -/
theorem H1LiftDeriv2ZeroSlabRepBefore_const_equilibrium
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) {T : ℝ}
    (hT : 0 < T) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      T
      (liftDeriv2PhysicalRHSWithChemRep p
        (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
        (liftChemotaxisDivPhysicalRep p
          (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
          (fun _ (_ : intervalDomainPoint) =>
            ellipticV p ((p.a / p.b) ^ (1 / p.α))))) :=
  H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPrimitiveData
    (H1ZeroStartPhysicalPrimitiveDataBefore_const_equilibrium
      (p := p) ha hb (T := T) hT)

/-- Zero-reaction constant primitive data gives the before-`T` zero-slab
representative used by the lap-component route. -/
theorem H1LiftDeriv2ZeroSlabRepBefore_const_zeroReaction
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) {c T : ℝ}
    (hc : 0 < c) (hT : 0 < T) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore
      (fun _ (_ : intervalDomainPoint) => c)
      T
      (liftDeriv2PhysicalRHSWithChemRep p
        (fun _ (_ : intervalDomainPoint) => c)
        (liftChemotaxisDivPhysicalRep p
          (fun _ (_ : intervalDomainPoint) => c)
          (fun _ (_ : intervalDomainPoint) => ellipticV p c))) :=
  H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPrimitiveData
    (H1ZeroStartPhysicalPrimitiveDataBefore_const_zeroReaction
      (p := p) ha hb (c := c) (T := T) hc hT)

/-- Constant equilibrium primitive data and the constant classical solution give
physical Young zero-window scalar majorants. -/
theorem H1PhysicalRHSYoungScalarZeroMajorantsBefore_const_equilibrium
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) {T : ℝ}
    (hT : 0 < T) :
    H1PhysicalRHSYoungScalarZeroMajorantsBefore p
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      (fun _ (_ : intervalDomainPoint) =>
        ellipticV p ((p.a / p.b) ^ (1 / p.α)))
      T := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  have hδ_pos : 0 < T / 2 := by linarith
  have hδ_before : T / 2 < T := by linarith
  have hprim :
      H1ZeroStartPhysicalPrimitiveDataBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPrimitiveDataBefore_const_equilibrium
      (p := p) ha hb (T := T) hT
  have hsol :
      IsPaper2ClassicalSolution intervalDomain p T
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c) :=
    (equilibrium_isPaper2ClassicalSolution p ha hb) T hT
  have hSpatial :
      H1PhysicalRHSComponentSquareSpatialYoungDataBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_zeroStartPrimitiveData
      (p := p) (T := T) (δ := T / 2)
      (u := fun _ (_ : intervalDomainPoint) => c)
      (v := fun _ (_ : intervalDomainPoint) => ellipticV p c)
      hsol hprim hδ_pos hδ_before
  exact
    H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_spatialYoungData hSpatial

/-- Zero-reaction constant primitive data and the constant classical solution
give physical Young zero-window scalar majorants. -/
theorem H1PhysicalRHSYoungScalarZeroMajorantsBefore_const_zeroReaction
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) {c T : ℝ}
    (hc : 0 < c) (hT : 0 < T) :
    H1PhysicalRHSYoungScalarZeroMajorantsBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T := by
  have hδ_pos : 0 < T / 2 := by linarith
  have hδ_before : T / 2 < T := by linarith
  have hprim :
      H1ZeroStartPhysicalPrimitiveDataBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1ZeroStartPhysicalPrimitiveDataBefore_const_zeroReaction
      (p := p) ha hb (c := c) (T := T) hc hT
  have hsol :
      IsPaper2ClassicalSolution intervalDomain p T
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c) :=
    (zeroReaction_isPaper2ClassicalSolution p ha hb c hc) T hT
  have hSpatial :
      H1PhysicalRHSComponentSquareSpatialYoungDataBefore p
        (fun _ (_ : intervalDomainPoint) => c)
        (fun _ (_ : intervalDomainPoint) => ellipticV p c)
        T :=
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_zeroStartPrimitiveData
      (p := p) (T := T) (δ := T / 2)
      (u := fun _ (_ : intervalDomainPoint) => c)
      (v := fun _ (_ : intervalDomainPoint) => ellipticV p c)
      hsol hprim hδ_pos hδ_before
  exact
    H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_spatialYoungData hSpatial

section AxiomAudit

#print axioms H1ZeroStartPhysicalRHSDataBefore_const_equilibrium
#print axioms H1ZeroStartPhysicalRHSDataBefore_const_zeroReaction
#print axioms H1LiftDeriv2ZeroSlabRepBefore_const_equilibrium
#print axioms H1LiftDeriv2ZeroSlabRepBefore_const_zeroReaction
#print axioms H1PhysicalRHSYoungScalarZeroMajorantsBefore_const_equilibrium
#print axioms H1PhysicalRHSYoungScalarZeroMajorantsBefore_const_zeroReaction

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
