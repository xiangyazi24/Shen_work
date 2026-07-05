import ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
import ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity

/-!
# Strict-window continuity producers for physical H¹ scalar components

This file converts strict-slab joint continuity of the three concrete physical
H¹ integrands into strict-window continuity of the scalar functions introduced
in `IntervalChiNegH1PhysicalRHSScalars`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge
open ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity

/-- Integrand for the taxis part of the physical H¹ RHS scalar. -/
def H1PhysicalTaxisIntegrand (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) : ℝ :=
  liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x

/-- Integrand for the `u v_xx`/denominator part of the physical H¹ RHS scalar. -/
def H1PhysicalUvxxIntegrand (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) : ℝ :=
  liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x

/-- Integrand for the logistic reaction part of the physical H¹ RHS scalar. -/
def H1PhysicalReactIntegrand (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) : ℝ :=
  liftDeriv2 u τ x * H1PhysicalLogisticReactionPart p u τ x

/-- Representative integrand for the taxis scalar, with `F` standing in for
`liftDeriv2 u`. -/
def H1PhysicalTaxisRepIntegrand (F : ℝ → ℝ → ℝ) (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) : ℝ :=
  F τ x * H1PhysicalChemTaxisPart p u v τ x

/-- Representative integrand for the `u v_xx`/denominator scalar, with `F`
standing in for `liftDeriv2 u`. -/
def H1PhysicalUvxxRepIntegrand (F : ℝ → ℝ → ℝ) (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) : ℝ :=
  F τ x * H1PhysicalChemUvxxPart p u v τ x

/-- Representative integrand for the logistic scalar, with `F` standing in for
`liftDeriv2 u`. -/
def H1PhysicalReactRepIntegrand (F : ℝ → ℝ → ℝ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (τ x : ℝ) : ℝ :=
  F τ x * H1PhysicalLogisticReactionPart p u τ x

private theorem intervalIntegral_zero_one_congr_of_eqOn_Ioo
    {f g : ℝ → ℝ}
    (hEq : Set.EqOn f g (Set.Ioo (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1, f x) =
      ∫ x in (0 : ℝ)..1, g x := by
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [hne1] with x hx_ne1 hxmem
  rw [Set.uIoc_of_le zero_le_one] at hxmem
  exact hEq ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx_ne1⟩

/-- Joint continuity of the taxis integrand gives strict-window continuity of
the taxis scalar. -/
theorem H1PhysicalTaxisX_continuousOn_Icc_of_integrand
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (H1PhysicalTaxisIntegrand p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (H1PhysicalTaxisX p u v) (Set.Icc a b) := by
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hcont
  simpa [H1PhysicalTaxisX, H1PhysicalTaxisIntegrand] using hint.neg

/-- Joint continuity of the `u v_xx`/denominator integrand gives
strict-window continuity of the corresponding scalar. -/
theorem H1PhysicalUvxxX_continuousOn_Icc_of_integrand
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (H1PhysicalUvxxIntegrand p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (H1PhysicalUvxxX p u v) (Set.Icc a b) := by
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hcont
  simpa [H1PhysicalUvxxX, H1PhysicalUvxxIntegrand] using hint.neg

/-- Joint continuity of the logistic-reaction integrand gives strict-window
continuity of the reaction scalar. -/
theorem H1PhysicalReactX_continuousOn_Icc_of_integrand
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (H1PhysicalReactIntegrand p u))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (H1PhysicalReactX p u) (Set.Icc a b) := by
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hcont
  simpa [H1PhysicalReactX, H1PhysicalReactIntegrand] using hint.neg

/-- Continuity of a representative taxis integrand gives continuity of the
literal taxis scalar, provided the representative agrees with `liftDeriv2` on
the spatial interior. -/
theorem H1PhysicalTaxisX_continuousOn_Icc_of_rep_integrand
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (H1PhysicalTaxisRepIntegrand F p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ContinuousOn (H1PhysicalTaxisX p u v) (Set.Icc a b) := by
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hcont
  refine hint.neg.congr ?_
  intro τ hτ
  have hEqInt :
      (∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x) =
        ∫ x in (0 : ℝ)..1,
          H1PhysicalTaxisRepIntegrand F p u v τ x := by
    refine intervalIntegral_zero_one_congr_of_eqOn_Ioo ?_
    intro x hx
    have hEqτ := hEqInterior (x := (τ, x))
      (Set.mem_prod.mpr ⟨hτ, hx⟩)
    simp only [Function.uncurry_apply_pair] at hEqτ
    simp [H1PhysicalTaxisRepIntegrand, hEqτ]
  simpa [H1PhysicalTaxisX] using congrArg (fun z : ℝ => -z) hEqInt

/-- Continuity of a representative `u v_xx`/denominator integrand gives
continuity of the literal `uvxx` scalar. -/
theorem H1PhysicalUvxxX_continuousOn_Icc_of_rep_integrand
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (H1PhysicalUvxxRepIntegrand F p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ContinuousOn (H1PhysicalUvxxX p u v) (Set.Icc a b) := by
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hcont
  refine hint.neg.congr ?_
  intro τ hτ
  have hEqInt :
      (∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x) =
        ∫ x in (0 : ℝ)..1,
          H1PhysicalUvxxRepIntegrand F p u v τ x := by
    refine intervalIntegral_zero_one_congr_of_eqOn_Ioo ?_
    intro x hx
    have hEqτ := hEqInterior (x := (τ, x))
      (Set.mem_prod.mpr ⟨hτ, hx⟩)
    simp only [Function.uncurry_apply_pair] at hEqτ
    simp [H1PhysicalUvxxRepIntegrand, hEqτ]
  simpa [H1PhysicalUvxxX] using congrArg (fun z : ℝ => -z) hEqInt

/-- Continuity of a representative logistic-reaction integrand gives
continuity of the literal reaction scalar. -/
theorem H1PhysicalReactX_continuousOn_Icc_of_rep_integrand
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (H1PhysicalReactRepIntegrand F p u))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ContinuousOn (H1PhysicalReactX p u) (Set.Icc a b) := by
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hcont
  refine hint.neg.congr ?_
  intro τ hτ
  have hEqInt :
      (∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalLogisticReactionPart p u τ x) =
        ∫ x in (0 : ℝ)..1,
          H1PhysicalReactRepIntegrand F p u τ x := by
    refine intervalIntegral_zero_one_congr_of_eqOn_Ioo ?_
    intro x hx
    have hEqτ := hEqInterior (x := (τ, x))
      (Set.mem_prod.mpr ⟨hτ, hx⟩)
    simp only [Function.uncurry_apply_pair] at hEqτ
    simp [H1PhysicalReactRepIntegrand, hEqτ]
  simpa [H1PhysicalReactX] using congrArg (fun z : ℝ => -z) hEqInt

/-- Strict-slab joint continuity package for the three physical scalar
integrands. -/
structure H1PhysicalRHSIntegrandsContinuousStrictBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop where
  taxis_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry (H1PhysicalTaxisIntegrand p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
  uvxx_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry (H1PhysicalUvxxIntegrand p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
  react_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry (H1PhysicalReactIntegrand p u))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)

/-- Strict-slab joint continuity package for representative integrands, with
`F` serving as the continuous representative of `liftDeriv2 u`. -/
structure H1PhysicalRHSRepIntegrandsContinuousStrictBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) (F : ℝ → ℝ → ℝ) : Prop where
  uxx_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
  uxx_eqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)
  taxis_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry (H1PhysicalTaxisRepIntegrand F p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
  uvxx_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry (H1PhysicalUvxxRepIntegrand F p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
  react_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry (H1PhysicalReactRepIntegrand F p u))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)

/-- Build representative-integrand continuity from continuity of `F` and of
the three non-lap physical scalar parts. -/
theorem H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_parts
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    {F : ℝ → ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hTaxisPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalChemTaxisPart p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hUvxxPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalChemUvxxPart p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReactPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalLogisticReactionPart p u))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore p u v T F :=
  { uxx_cont := hF
    uxx_eqInterior := hEqInterior
    taxis_cont := by
      intro a b ha hab hbT
      simpa [H1PhysicalTaxisRepIntegrand, Function.uncurry] using
        (hF (a := a) (b := b) ha hab hbT).mul
          (hTaxisPart (a := a) (b := b) ha hab hbT)
    uvxx_cont := by
      intro a b ha hab hbT
      simpa [H1PhysicalUvxxRepIntegrand, Function.uncurry] using
        (hF (a := a) (b := b) ha hab hbT).mul
          (hUvxxPart (a := a) (b := b) ha hab hbT)
    react_cont := by
      intro a b ha hab hbT
      simpa [H1PhysicalReactRepIntegrand, Function.uncurry] using
        (hF (a := a) (b := b) ha hab hbT).mul
          (hReactPart (a := a) (b := b) ha hab hbT) }

/-- Strict lap continuity plus strict-slab joint continuity of the three
physical scalar integrands gives the Task88 strict component-continuity package. -/
theorem H1PhysicalRHSComponentsContinuousStrictBefore_of_lap_integrands
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hLap : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (hInt : H1PhysicalRHSIntegrandsContinuousStrictBefore p u v T) :
    H1PhysicalRHSComponentsContinuousStrictBefore p u v T :=
  ⟨H1IdentityRHSComponentsContinuousStrictBefore_of_components
    (p := p) (u := u) (T := T)
    (taxisX := H1PhysicalTaxisX p u v)
    (uvxx := H1PhysicalUvxxX p u v)
    (reactX := H1PhysicalReactX p u)
    hLap
    (fun ha hab hbT =>
      H1PhysicalTaxisX_continuousOn_Icc_of_integrand
        (hInt.taxis_cont ha hab hbT))
    (fun ha hab hbT =>
      H1PhysicalUvxxX_continuousOn_Icc_of_integrand
        (hInt.uvxx_cont ha hab hbT))
    (fun ha hab hbT =>
      H1PhysicalReactX_continuousOn_Icc_of_integrand
        (hInt.react_cont ha hab hbT))⟩

/-- Fill the strict lap component from `H1LiftDeriv2JointContinuousBefore`,
leaving only the three physical scalar integrand continuities as inputs. -/
theorem H1PhysicalRHSComponentsContinuousStrictBefore_of_liftDeriv2_integrands
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (huxx : H1LiftDeriv2JointContinuousBefore u T)
    (hInt : H1PhysicalRHSIntegrandsContinuousStrictBefore p u v T) :
    H1PhysicalRHSComponentsContinuousStrictBefore p u v T :=
  H1PhysicalRHSComponentsContinuousStrictBefore_of_lap_integrands
    (p := p) (u := u) (v := v) (T := T)
    (lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
      huxx)
    hInt

/-- Fill the strict lap component from a continuous strict-slab representative
of `liftDeriv2`, leaving only the three physical scalar integrand continuities
as inputs. -/
theorem
    H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_integrands
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {T : ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hInt : H1PhysicalRHSIntegrandsContinuousStrictBefore p u v T) :
    H1PhysicalRHSComponentsContinuousStrictBefore p u v T :=
  H1PhysicalRHSComponentsContinuousStrictBefore_of_lap_integrands
    (p := p) (u := u) (v := v) (T := T)
    (lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
      hF hEqInterior)
    hInt

/-- A continuous representative of `liftDeriv2`, interior equality, and
representative-integrand continuity give the Task88 strict component-continuity
package without asking for endpoint continuity of literal `liftDeriv2`. -/
theorem
    H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_repIntegrands
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {T : ℝ}
    (hRep : H1PhysicalRHSRepIntegrandsContinuousStrictBefore p u v T F) :
    H1PhysicalRHSComponentsContinuousStrictBefore p u v T :=
  ⟨H1IdentityRHSComponentsContinuousStrictBefore_of_strictSlab_interior_eq_continuous
    (p := p) (u := u) (T := T) (F := F)
    (taxisX := H1PhysicalTaxisX p u v)
    (uvxx := H1PhysicalUvxxX p u v)
    (reactX := H1PhysicalReactX p u)
    hRep.uxx_cont
    hRep.uxx_eqInterior
    (fun ha hab hbT =>
      H1PhysicalTaxisX_continuousOn_Icc_of_rep_integrand
        (hRep.taxis_cont ha hab hbT)
        (hRep.uxx_eqInterior ha hab hbT))
    (fun ha hab hbT =>
      H1PhysicalUvxxX_continuousOn_Icc_of_rep_integrand
        (hRep.uvxx_cont ha hab hbT)
        (hRep.uxx_eqInterior ha hab hbT))
    (fun ha hab hbT =>
      H1PhysicalReactX_continuousOn_Icc_of_rep_integrand
        (hRep.react_cont ha hab hbT)
        (hRep.uxx_eqInterior ha hab hbT))⟩

/-- Direct part-continuity constructor for the representative strict component
package. -/
theorem H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_parts
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {T : ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hTaxisPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalChemTaxisPart p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hUvxxPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalChemUvxxPart p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReactPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalLogisticReactionPart p u))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1PhysicalRHSComponentsContinuousStrictBefore p u v T :=
  H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_repIntegrands
    (p := p) (u := u) (v := v) (F := F) (T := T)
    (H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_parts
      (p := p) (u := u) (v := v) (T := T) (F := F)
      hF hEqInterior hTaxisPart hUvxxPart hReactPart)

/-- Representative strict-slab integrand continuity plus additive local scalar
zero-window majorants assemble the physical strict/initial route. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_repIntegrands_additiveScalarZero
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hRep : H1PhysicalRHSRepIntegrandsContinuousStrictBefore p u v T F)
    (hAdd : H1PhysicalRHSAdditiveScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_additiveScalar_zeroWindow
    hId hBounds
    (H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_repIntegrands
      hRep)
    hAdd

/-- Direct part-continuity version of the physical strict/initial route
constructor. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_strictSlab_parts_additiveScalarZero
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hTaxisPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalChemTaxisPart p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hUvxxPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalChemUvxxPart p u v))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hReactPart : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry (H1PhysicalLogisticReactionPart p u))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hAdd : H1PhysicalRHSAdditiveScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_repIntegrands_additiveScalarZero
    hId hBounds
    (H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_parts
      (p := p) (u := u) (v := v) (T := T) (F := F)
      hF hEqInterior hTaxisPart hUvxxPart hReactPart)
    hAdd

#print axioms H1PhysicalTaxisX_continuousOn_Icc_of_integrand
#print axioms H1PhysicalUvxxX_continuousOn_Icc_of_integrand
#print axioms H1PhysicalReactX_continuousOn_Icc_of_integrand
#print axioms H1PhysicalTaxisX_continuousOn_Icc_of_rep_integrand
#print axioms H1PhysicalUvxxX_continuousOn_Icc_of_rep_integrand
#print axioms H1PhysicalReactX_continuousOn_Icc_of_rep_integrand
#print axioms H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_parts
#print axioms H1PhysicalRHSComponentsContinuousStrictBefore_of_lap_integrands
#print axioms
  H1PhysicalRHSComponentsContinuousStrictBefore_of_liftDeriv2_integrands
#print axioms
  H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_integrands
#print axioms
  H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_repIntegrands
#print axioms H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_parts
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_repIntegrands_additiveScalarZero
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_strictSlab_parts_additiveScalarZero

end ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity
