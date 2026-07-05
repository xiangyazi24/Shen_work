import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

/-!
# Strict-slab representative transfer for `liftDeriv2`

This file fixes the exact seam shape for producing the H¹ `u_xx` regularity
input: a jointly continuous strict-slab representative plus an `EqOn` proof
against `liftDeriv2`.  Endpoint equality remains an explicit hypothesis.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer

/-- Physical strict-slab representative for the `u`-equation solved as
`u_xx = u_t + chi * chemotaxisDiv - reaction`. -/
abbrev liftDeriv2PhysicalRHS (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  liftTimeDeriv u t x +
    p.χ₀ *
      intervalDomainLift
        (fun X : intervalDomainPoint =>
          intervalDomain.chemotaxisDiv p (u t) (v t) X) x -
    intervalDomainLift (u t) x *
      (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)

/-- The physical RHS representative is continuous wherever its three components
are continuous. -/
theorem liftDeriv2PhysicalRHS_continuousOn_of_components
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {s : Set (ℝ × ℝ)}
    (hTime :
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x)) s)
    (hChem :
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift
              (fun X : intervalDomainPoint =>
                intervalDomain.chemotaxisDiv p (u t) (v t) X) x)) s)
    (hReact :
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift (u t) x *
              (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α))) s) :
    ContinuousOn (Function.uncurry (liftDeriv2PhysicalRHS p u v)) s := by
  simpa [liftDeriv2PhysicalRHS, Function.uncurry] using
    (hTime.add (hChem.const_mul p.χ₀)).sub hReact

/-- If `liftDeriv2 u` has a continuous strict-slab representative `F`, then the
current strict-positive-time joint-continuity package follows. -/
theorem H1LiftDeriv2JointContinuousBefore_of_strictSlab_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1LiftDeriv2JointContinuousBefore u T := by
  refine ⟨?_⟩
  intro a b ha hab hbT
  exact (hF (a := a) (b := b) ha hab hbT).congr
    (fun z hz => hEq (a := a) (b := b) ha hab hbT hz)

/-- The same strict-slab representative immediately discharges the current
`u_xx` L¹-continuity frontier. -/
theorem H1UxxL1ContBefore_of_strictSlab_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1UxxL1ContBefore u T :=
  H1UxxL1ContBefore_of_liftDeriv2_jointContinuousBefore
    (H1LiftDeriv2JointContinuousBefore_of_strictSlab_eq_continuous
      (u := u) (T := T) (F := F) hF hEq)

/-- Strict-slab continuity of the physical RHS components, plus slabwise
agreement with `liftDeriv2`, produces the H¹ `u_xx` joint-continuity package.

This theorem deliberately keeps the chemotaxis-divergence continuity and the
endpoint-sensitive `EqOn` proof explicit. -/
theorem H1LiftDeriv2JointContinuousBefore_of_physicalRHS_components
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hTime : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChem : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift
              (fun X : intervalDomainPoint =>
                intervalDomain.chemotaxisDiv p (u t) (v t) X) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReact : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift (u t) x *
              (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHS p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1LiftDeriv2JointContinuousBefore u T := by
  refine H1LiftDeriv2JointContinuousBefore_of_strictSlab_eq_continuous
    (u := u) (T := T) (F := liftDeriv2PhysicalRHS p u v) ?_ hEq
  intro a b ha hab hbT
  exact liftDeriv2PhysicalRHS_continuousOn_of_components
    (p := p) (u := u) (v := v)
    (s := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
    (hTime (a := a) (b := b) ha hab hbT)
    (hChem (a := a) (b := b) ha hab hbT)
    (hReact (a := a) (b := b) ha hab hbT)

/-- The same physical-RHS component package immediately gives the current
`u_xx` L¹-continuity frontier. -/
theorem H1UxxL1ContBefore_of_physicalRHS_components
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hTime : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hChem : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift
              (fun X : intervalDomainPoint =>
                intervalDomain.chemotaxisDiv p (u t) (v t) X) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReact : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift (u t) x *
              (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHS p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1UxxL1ContBefore u T :=
  H1UxxL1ContBefore_of_liftDeriv2_jointContinuousBefore
    (H1LiftDeriv2JointContinuousBefore_of_physicalRHS_components
      (p := p) (u := u) (v := v) (T := T) hTime hChem hReact hEq)

/-- A classical solution supplies strict-slab continuity of `liftTimeDeriv`. -/
theorem liftTimeDeriv_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T a b : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hTime :
      ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.1.1
  refine hTime.mono (Set.prod_mono ?_ (Subset.rfl))
  intro t ht
  exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩

/-- A classical solution supplies strict-slab continuity of the logistic
reaction component in the physical `u_xx` representative. -/
theorem logisticReaction_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T a b : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    ContinuousOn
      (Function.uncurry
        (fun t x =>
          intervalDomainLift (u t) x *
            (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hu_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.2.1
  have hsub :
      Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    refine Set.prod_mono ?_ (Subset.rfl)
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hu :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hu_all.mono hsub
  have hu_pos :
      ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
        0 <
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z := by
    intro z hz
    rcases z with ⟨t, x⟩
    rcases hz with ⟨ht, hx⟩
    simp only [Function.uncurry_apply_pair]
    rw [intervalDomainLift, dif_pos hx]
    exact hsol.u_pos' (lt_of_lt_of_le ha ht.1) (lt_of_le_of_lt ht.2 hbT)
  have hupow :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^ p.α)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    exact hu.rpow_const (fun z hz => Or.inl (ne_of_gt (hu_pos z hz)))
  simpa [Function.uncurry] using
    hu.mul (continuousOn_const.sub (hupow.const_mul p.b))

/-- From a classical solution, only the chemotaxis-divergence continuity and
closed-slab equality with the physical RHS remain as explicit upstream inputs. -/
theorem H1LiftDeriv2JointContinuousBefore_of_classical_chem_eq_physicalRHS
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hChem : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift
              (fun X : intervalDomainPoint =>
                intervalDomain.chemotaxisDiv p (u t) (v t) X) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHS p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1LiftDeriv2JointContinuousBefore u T := by
  refine H1LiftDeriv2JointContinuousBefore_of_physicalRHS_components
    (p := p) (u := u) (v := v) (T := T) ?_ hChem ?_ hEq
  · intro a b ha hab hbT
    exact liftTimeDeriv_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT
  · intro a b ha hab hbT
    exact logisticReaction_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT

/-- The classical-solution version of the physical RHS seam also discharges the
current `u_xx` L¹-continuity frontier. -/
theorem H1UxxL1ContBefore_of_classical_chem_eq_physicalRHS
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hChem : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift
              (fun X : intervalDomainPoint =>
                intervalDomain.chemotaxisDiv p (u t) (v t) X) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHS p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1UxxL1ContBefore u T :=
  H1UxxL1ContBefore_of_liftDeriv2_jointContinuousBefore
    (H1LiftDeriv2JointContinuousBefore_of_classical_chem_eq_physicalRHS
      (p := p) (u := u) (v := v) (T := T) hsol hChem hEq)

section AxiomAudit

#print axioms H1LiftDeriv2JointContinuousBefore_of_strictSlab_eq_continuous
#print axioms H1UxxL1ContBefore_of_strictSlab_eq_continuous
#print axioms liftDeriv2PhysicalRHS_continuousOn_of_components
#print axioms H1LiftDeriv2JointContinuousBefore_of_physicalRHS_components
#print axioms H1UxxL1ContBefore_of_physicalRHS_components
#print axioms liftTimeDeriv_continuousOn_strictSlab_of_classicalSolution
#print axioms logisticReaction_continuousOn_strictSlab_of_classicalSolution
#print axioms H1LiftDeriv2JointContinuousBefore_of_classical_chem_eq_physicalRHS
#print axioms H1UxxL1ContBefore_of_classical_chem_eq_physicalRHS

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
