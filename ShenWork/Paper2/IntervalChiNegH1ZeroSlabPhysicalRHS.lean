import ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
import ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

/-!
# Zero-start physical RHS bridge for the H¹ lap component

This file does not produce zero-time H²/lap trace data.  It only packages the
next honest producer target: a continuous zero-start physical RHS
representative, together with interior equality to `liftDeriv2`, gives the
zero-slab representative frontier consumed by the lap component route.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS

/-- A continuous zero-start representative plus interior equality is exactly
the single-slab `liftDeriv2` frontier needed by the lap component route. -/
theorem H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartRep
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ} {b : ℝ}
    (hb0 : 0 < b)
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2ZeroSlabRepresentative u F b :=
  { hb0 := hb0
    hFcont := hF
    hEqInterior := hEqInterior }

/-- Family version of `H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartRep`. -/
theorem H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartRep
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {b : ℝ}, 0 ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore u T F :=
  { cont0 := fun hb hbT => hF hb hbT
    eqInterior0 := fun hb hbT => hEqInterior hb hbT }

/-- Physical-RHS specialization with a chemotaxis-divergence representative.
The producer must still supply the zero-start continuity and the interior PDE
equality; this theorem only converts those facts into the lap-route atom. -/
theorem H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartPhysicalRHSRep
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {chemRep : ℝ → ℝ → ℝ} {b : ℝ}
    (hb0 : 0 < b)
    (hRHS : ContinuousOn
      (Function.uncurry (liftDeriv2PhysicalRHSWithChemRep p u chemRep))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHSWithChemRep p u chemRep))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2ZeroSlabRepresentative u
      (liftDeriv2PhysicalRHSWithChemRep p u chemRep) b :=
  H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartRep hb0 hRHS hEqInterior

/-- Component form of the zero-start physical RHS bridge. -/
theorem H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartPhysicalRHS_components
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {chemRep : ℝ → ℝ → ℝ} {b : ℝ}
    (hb0 : 0 < b)
    (hTime : ContinuousOn
      (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChemRep : ContinuousOn (Function.uncurry chemRep)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReact : ContinuousOn
      (Function.uncurry
        (fun t x =>
          intervalDomainLift (u t) x *
            (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHSWithChemRep p u chemRep))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2ZeroSlabRepresentative u
      (liftDeriv2PhysicalRHSWithChemRep p u chemRep) b :=
  H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartPhysicalRHSRep
    (p := p) (u := u) (chemRep := chemRep) hb0
    (liftDeriv2PhysicalRHSWithChemRep_continuousOn_of_components
      hTime hChemRep hReact)
    hEqInterior

/-- Existential form of the single-slab zero-start physical RHS bridge. -/
theorem H1LiftDeriv2HasZeroSlabRepresentative_of_zeroStartPhysicalRHS_components
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {chemRep : ℝ → ℝ → ℝ} {b : ℝ}
    (hb0 : 0 < b)
    (hTime : ContinuousOn
      (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChemRep : ContinuousOn (Function.uncurry chemRep)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReact : ContinuousOn
      (Function.uncurry
        (fun t x =>
          intervalDomainLift (u t) x *
            (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHSWithChemRep p u chemRep))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2HasZeroSlabRepresentative u :=
  ⟨liftDeriv2PhysicalRHSWithChemRep p u chemRep, b,
    H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartPhysicalRHS_components
      (p := p) (u := u) (chemRep := chemRep) hb0
      hTime hChemRep hReact hEqInterior⟩

/-- Before-`T` physical-RHS specialization with a chemotaxis-divergence
representative. -/
theorem H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartPhysicalRHSRep
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {chemRep : ℝ → ℝ → ℝ} {T : ℝ}
    (hRHS : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry (liftDeriv2PhysicalRHSWithChemRep p u chemRep))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {b : ℝ}, 0 ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHSWithChemRep p u chemRep))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore u T
      (liftDeriv2PhysicalRHSWithChemRep p u chemRep) :=
  H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartRep
    hRHS hEqInterior

/-- Component form of the before-`T` zero-start physical RHS bridge. -/
theorem
    H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartPhysicalRHS_components
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {chemRep : ℝ → ℝ → ℝ} {T : ℝ}
    (hTime : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChemRep : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry chemRep)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReact : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift (u t) x *
              (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {b : ℝ}, 0 ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHSWithChemRep p u chemRep))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore u T
      (liftDeriv2PhysicalRHSWithChemRep p u chemRep) :=
  H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartPhysicalRHSRep
    (p := p) (u := u) (chemRep := chemRep)
    (fun {b} hb hbT =>
      liftDeriv2PhysicalRHSWithChemRep_continuousOn_of_components
        (p := p) (u := u) (chemRep := chemRep)
        (s := Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
        (hTime (b := b) hb hbT)
        (hChemRep (b := b) hb hbT)
        (hReact (b := b) hb hbT))
    hEqInterior

/-- Concrete single-slab wrapper using the physical chemotaxis-divergence
representative as the `chemRep` component. -/
theorem H1LiftDeriv2HasZeroSlabRep_of_chemPhysical_components
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {b : ℝ}
    (hb0 : 0 < b)
    (hTime : ContinuousOn
      (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChem : ContinuousOn
      (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReact : ContinuousOn
      (Function.uncurry
        (fun t x =>
          intervalDomainLift (u t) x *
            (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry
          (liftDeriv2PhysicalRHSWithChemRep p u
            (liftChemotaxisDivPhysicalRep p u v)))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2HasZeroSlabRepresentative u :=
  H1LiftDeriv2HasZeroSlabRepresentative_of_zeroStartPhysicalRHS_components
    (p := p) (u := u) (chemRep := liftChemotaxisDivPhysicalRep p u v)
    hb0 hTime hChem hReact hEqInterior

/-- Concrete before-`T` wrapper using the physical chemotaxis-divergence
representative as the `chemRep` component. -/
theorem H1LiftDeriv2ZeroSlabRepBefore_of_chemPhysical_components
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hTime : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChem : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReact : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift (u t) x *
              (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {b : ℝ}, 0 ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry
          (liftDeriv2PhysicalRHSWithChemRep p u
            (liftChemotaxisDivPhysicalRep p u v)))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore u T
      (liftDeriv2PhysicalRHSWithChemRep p u
        (liftChemotaxisDivPhysicalRep p u v)) :=
  H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartPhysicalRHS_components
    (p := p) (u := u) (chemRep := liftChemotaxisDivPhysicalRep p u v)
    hTime hChem hReact hEqInterior

section AxiomAudit

#print axioms H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartRep
#print axioms H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartRep
#print axioms H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartPhysicalRHSRep
#print axioms H1LiftDeriv2ZeroSlabRepresentative_of_zeroStartPhysicalRHS_components
#print axioms H1LiftDeriv2HasZeroSlabRepresentative_of_zeroStartPhysicalRHS_components
#print axioms H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartPhysicalRHSRep
#print axioms
  H1LiftDeriv2ZeroSlabRepresentativeBefore_of_zeroStartPhysicalRHS_components
#print axioms H1LiftDeriv2HasZeroSlabRep_of_chemPhysical_components
#print axioms H1LiftDeriv2ZeroSlabRepBefore_of_chemPhysical_components

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS
