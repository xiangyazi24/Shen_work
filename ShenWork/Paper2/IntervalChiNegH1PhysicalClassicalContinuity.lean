import ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity
import ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS

/-!
# Classical strict-slab continuity for the physical H¹ scalar route

This file discharges the strict-positive-time continuity inputs in the
physical H¹ strict/initial route from the existing classical-solution
regularity and representative APIs.  It does not address the physical identity,
sqrt estimates, or zero-window Young/component-square estimates.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity

private theorem strict_slab_subset_ioo
    {T a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
  intro z hz
  exact ⟨⟨lt_of_lt_of_le ha hz.1.1, lt_of_le_of_lt hz.1.2 hbT⟩, hz.2⟩

private theorem one_add_lift_v_pos_on_strict_slab
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      0 < 1 +
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
  intro z hz
  rcases z with ⟨t, x⟩
  rcases hz with ⟨ht, hx⟩
  simp only [Function.uncurry_apply_pair]
  rw [intervalDomainLift, dif_pos hx]
  have htI : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hvnn : 0 ≤ v t ⟨x, hx⟩ := hsol.v_nonneg htI.1 htI.2
  linarith

/-- Strict-slab continuity of the concrete physical `liftDeriv2`
representative with the closed-slab chemotaxis-divergence representative. -/
theorem liftDeriv2PhysicalRHSWithChemRep_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn
      (Function.uncurry
        (liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
  liftDeriv2PhysicalRHSWithChemRep_continuousOn_of_components
    (p := p) (u := u)
    (chemRep := liftChemotaxisDivPhysicalRep p u v)
    (s := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
    (liftTimeDeriv_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (logisticReaction_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)

/-- Strict-slab interior equality of literal `liftDeriv2` with the concrete
physical RHS representative using `liftChemotaxisDivPhysicalRep`. -/
theorem liftDeriv2_eq_liftDeriv2PhysicalRHSWithChemRep_strictSlab_interior_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry
        (liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  have hphys :=
    liftDeriv2_eq_liftDeriv2PhysicalRHS_strictSlab_interior_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT hz
  have hchem :=
    lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_strictSlab_interior
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT hz
  rcases z with ⟨t, x⟩
  simp only [Function.uncurry_apply_pair] at hphys hchem ⊢
  rw [hphys]
  simp [liftDeriv2PhysicalRHS, liftDeriv2PhysicalRHSWithChemRep, hchem]

/-- Strict-slab continuity of the `u_x v_x / (1+v)^β` taxis part from the
existing joint-continuity producers. -/
theorem H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (H1PhysicalChemTaxisPart p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsub := strict_slab_subset_ioo (T := T) ha hab hbT
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hv_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2
  have hv := hv_all.mono hsub
  have hux :=
    (intervalDomain_dx_u_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hvx :=
    (intervalDomain_dx_v_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hv
  have hbase_pos :=
    one_add_lift_v_pos_on_strict_slab
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT
  have hden :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_ne : ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      (1 + Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  simpa [H1PhysicalChemTaxisPart, Function.uncurry] using
    (hux.mul hvx).div hden hden_ne

/-- Strict-slab continuity of the physical `u v_xx`/denominator part from the
reaction representative and `v_x` joint continuity. -/
theorem H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (H1PhysicalChemUvxxPart p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsub := strict_slab_subset_ioo (T := T) ha hab hbT
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hu_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.1
  have hv_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2
  have hu := hu_all.mono hsub
  have hv := hv_all.mono hsub
  have hvx :=
    (intervalDomain_dx_v_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hvxxRep :=
    (intervalDomain_v_xx_reaction_jointContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hv
  have hbase_pos :=
    one_add_lift_v_pos_on_strict_slab
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT
  have hdenβ :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hdenβ1 :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            (p.β + 1))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hdenβ_ne : ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      (1 + Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hdenβ1_ne : ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      (1 + Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
          (p.β + 1) ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hterm1 := (hu.mul hvxxRep).div hdenβ hdenβ_ne
  have hterm2 := ((hu.const_mul p.β).mul (hvx.pow 2)).div hdenβ1 hdenβ1_ne
  simpa [H1PhysicalChemUvxxPart, Function.uncurry] using hterm1.sub hterm2

/-- Strict-slab continuity of the physical logistic reaction part. -/
theorem H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (H1PhysicalLogisticReactionPart p u))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsub := strict_slab_subset_ioo (T := T) ha hab hbT
  simpa [H1PhysicalLogisticReactionPart, Function.uncurry] using
    (intervalDomain_u_logistic_jointContinuous
      (params := p) (T := T) (u := u) (v := v) hsol).mono hsub

/-- Classical solutions supply the representative-integrand continuity package
needed by the physical H¹ strict scalar-continuity route. -/
theorem H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore p u v T
      (liftDeriv2PhysicalRHSWithChemRep p u
        (liftChemotaxisDivPhysicalRep p u v)) :=
  H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_parts
    (p := p) (u := u) (v := v) (T := T)
    (F := liftDeriv2PhysicalRHSWithChemRep p u
      (liftChemotaxisDivPhysicalRep p u v))
    (fun {_a _b} ha hab hbT =>
      liftDeriv2PhysicalRHSWithChemRep_continuousOn_strictSlab_of_classicalSolution
        (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      liftDeriv2_eq_liftDeriv2PhysicalRHSWithChemRep_strictSlab_interior_of_classicalSolution
        (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
        (p := p) (T := T) (u := u) (v := v) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
        (p := p) (T := T) (u := u) (v := v) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
        (p := p) (T := T) (u := u) (v := v) hsol ha hab hbT)

/-- The strict physical component-continuity package follows from classical
strict-positive-time regularity, without zero-start `lapL2sq` continuity. -/
theorem H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    H1PhysicalRHSComponentsContinuousStrictBefore p u v T :=
  H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_repIntegrands
    (H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol)

/-- Physical strict/initial route constructor with strict component continuity
discharged from the classical solution.  The remaining inputs are the physical
identity, sqrt estimates, and the Young zero-window majorant. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hYoung : H1PhysicalRHSYoungScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_repIntegrands_youngScalarZero
    hId hBounds
    (H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol)
    hYoung

/-- Component-square version of the classical physical strict/initial route
constructor, using the Task94 zero-window square-data adapter. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_classical_componentSquareZero
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hSq : H1PhysicalRHSComponentSquareZeroDataBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero
    hsol hId hBounds
    (H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_componentSquareZeroData hSq)

#print axioms
  liftDeriv2PhysicalRHSWithChemRep_continuousOn_strictSlab_of_classicalSolution
#print axioms
  liftDeriv2_eq_liftDeriv2PhysicalRHSWithChemRep_strictSlab_interior_of_classicalSolution
#print axioms
  H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
#print axioms
  H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
#print axioms
  H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
#print axioms
  H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_componentSquareZero

end ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
