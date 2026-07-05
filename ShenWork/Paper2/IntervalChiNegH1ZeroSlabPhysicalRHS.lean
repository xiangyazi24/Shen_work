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

/-- Zero-start logistic reaction continuity from zero-start lift continuity and
strict positivity of the lifted `u` values.  This isolates the easy algebraic
part of the `reactionContinuous` field below. -/
theorem logisticReaction_continuousOn_zeroSlab_of_lift_continuous_positive
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {b : ℝ}
    (hLift : ContinuousOn
      (Function.uncurry (fun t x => intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hPos :
      ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
        0 <
          Function.uncurry
            (fun t x => intervalDomainLift (u t) x) z) :
    ContinuousOn
      (Function.uncurry
        (fun t x =>
          intervalDomainLift (u t) x *
            (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1
  have hPow :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (Function.uncurry
            (fun t x => intervalDomainLift (u t) x) z) ^ p.α) S :=
    hLift.rpow_const (fun z hz => Or.inl (ne_of_gt (hPos z hz)))
  have hFactor :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          p.a - p.b *
            (Function.uncurry
              (fun t x => intervalDomainLift (u t) x) z) ^ p.α) S :=
    continuousOn_const.sub (hPow.const_mul p.b)
  simpa [S, Function.uncurry] using hLift.mul hFactor

/-- Named frontier for producing the concrete zero-start physical RHS package.

This is deliberately an input package, not a theorem from the current
classical-solution API: the strict positive-time producers do not by themselves
give closed-time-at-zero continuity of these components. -/
structure H1ZeroStartPhysicalRHSDataBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  timeContinuous : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  chemContinuous : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  reactionContinuous : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun t x =>
          intervalDomainLift (u t) x *
            (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  eqInterior : ∀ {b : ℝ}, 0 ≤ b → b < T →
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry
        (liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)

/-- Construct the zero-start physical RHS data package when the reaction term
is supplied by zero-start lift continuity and positivity. -/
theorem H1ZeroStartPhysicalRHSDataBefore_of_lift_continuous_positive
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hTime : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChem : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hLift : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry (fun t x => intervalDomainLift (u t) x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hPos : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
        0 <
          Function.uncurry
            (fun t x => intervalDomainLift (u t) x) z)
    (hEqInterior : ∀ {b : ℝ}, 0 ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry
          (liftDeriv2PhysicalRHSWithChemRep p u
            (liftChemotaxisDivPhysicalRep p u v)))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1ZeroStartPhysicalRHSDataBefore p u v T :=
  { timeContinuous := hTime
    chemContinuous := hChem
    reactionContinuous := fun {b} hb hbT =>
      logisticReaction_continuousOn_zeroSlab_of_lift_continuous_positive
        (p := p) (u := u) (b := b)
        (hLift (b := b) hb hbT)
        (hPos (b := b) hb hbT)
    eqInterior := hEqInterior }

/-- The explicit zero-start physical RHS frontier discharges the before-`T`
zero-slab representative package used by the lap-component route. -/
theorem H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHSData
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h : H1ZeroStartPhysicalRHSDataBefore p u v T) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore u T
      (liftDeriv2PhysicalRHSWithChemRep p u
        (liftChemotaxisDivPhysicalRep p u v)) :=
  H1LiftDeriv2ZeroSlabRepBefore_of_chemPhysical_components
    (p := p) (u := u) (v := v) (T := T)
    h.timeContinuous h.chemContinuous h.reactionContinuous h.eqInterior

/-- Before-`T` zero-slab representative from the zero-start time and chem
continuity fields, plus zero-start lift continuity/positivity for the reaction
field. -/
theorem H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHS_lift_positive
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hTime : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChem : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hLift : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry (fun t x => intervalDomainLift (u t) x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hPos : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
        0 <
          Function.uncurry
            (fun t x => intervalDomainLift (u t) x) z)
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
  H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHSData
    (H1ZeroStartPhysicalRHSDataBefore_of_lift_continuous_positive
      (p := p) (u := u) (v := v) (T := T)
      hTime hChem hLift hPos hEqInterior)

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
#print axioms logisticReaction_continuousOn_zeroSlab_of_lift_continuous_positive
#print axioms H1ZeroStartPhysicalRHSDataBefore_of_lift_continuous_positive
#print axioms H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHSData
#print axioms H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHS_lift_positive

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS
