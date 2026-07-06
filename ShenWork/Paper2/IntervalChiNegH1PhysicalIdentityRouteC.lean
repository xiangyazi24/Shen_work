import ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
import ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
import ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity

/-!
# Route-C physical H¹ identity interface

This file connects the finite-difference H¹ energy derivative producer to the
concrete physical RHS scalar triple, while keeping the actual substitution
equality as an explicit frontier.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC

/-- Exact substitution frontier for the Route-C derivative value into the
concrete physical scalar triple. -/
def H1PhysicalRHSRouteCSubstitutionBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    -(∫ x in (0 : ℝ)..1,
        liftDeriv2 u τ x * liftTimeDeriv u τ x) =
      H1IdentityRHSValue p u
        (H1PhysicalTaxisX p u v)
        (H1PhysicalUvxxX p u v)
        (H1PhysicalReactX p u) τ

private theorem continuousOn_slice_of_uncurry
    {F : ℝ → ℝ → ℝ} {r : ℝ} {s : Set ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc r r ×ˢ s)) :
    ContinuousOn (F r) s := by
  have hpair : ContinuousOn (fun x : ℝ => ((r, x) : ℝ × ℝ)) s :=
    continuousOn_const.prodMk continuousOn_id
  have hmaps :
      Set.MapsTo (fun x : ℝ => ((r, x) : ℝ × ℝ)) s
        (Set.Icc r r ×ˢ s) := by
    intro x hx
    exact ⟨⟨le_rfl, le_rfl⟩, hx⟩
  simpa [Function.uncurry] using hF.comp hpair hmaps

private theorem ae_uIoc_zero_one_mem_Ioo :
    ∀ᵐ x : ℝ ∂volume,
      x ∈ Set.uIoc (0 : ℝ) 1 → x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [hne1] with x hx_ne1 hxmem
  rw [Set.uIoc_of_le zero_le_one] at hxmem
  exact ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx_ne1⟩

private theorem intervalIntegral_zero_one_congr_of_eqOn_Ioo
    {f g : ℝ → ℝ}
    (hEq : Set.EqOn f g (Set.Ioo (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1, f x) =
      ∫ x in (0 : ℝ)..1, g x := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_uIoc_zero_one_mem_Ioo] with x hxIoo hxmem
  exact hEq (hxIoo hxmem)

private theorem liftDeriv2_sq_intervalIntegrable_of_rep_cont
    {u : ℝ → intervalDomainPoint → ℝ}
    {F : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Ioo (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => (liftDeriv2 u r x) ^ 2)
      volume (0 : ℝ) 1 := by
  have hSlice :
      ContinuousOn (fun x => (F r x) ^ 2) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_slice_of_uncurry
      (F := F) (r := r) (s := Set.Icc (0 : ℝ) 1) hCont).pow 2
  have hRepInt :
      IntervalIntegrable (fun x => (F r x) ^ 2) volume (0 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hSlice
  refine hRepInt.congr_ae ?_
  rw [Set.uIoc_of_le zero_le_one]
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_uIoc_zero_one_mem_Ioo] with x hxIoo hxIoc
  have hx : x ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le zero_le_one] using hxIoo (by
      simpa [Set.uIoc_of_le zero_le_one] using hxIoc)
  have hEq := hEqInterior (x := (r, x))
    (Set.mem_prod.mpr ⟨⟨le_rfl, le_rfl⟩, hx⟩)
  simp only [Function.uncurry_apply_pair] at hEq
  rw [← hEq]

private theorem liftDeriv2_mul_part_intervalIntegrable_of_rep_product_cont
    {u : ℝ → intervalDomainPoint → ℝ}
    {F part : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => F t x * part t x))
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Ioo (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => liftDeriv2 u r x * part r x)
      volume (0 : ℝ) 1 := by
  have hSlice :
      ContinuousOn (fun x => F r x * part r x) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_slice_of_uncurry
      (F := fun t x => F t x * part t x)
      (r := r) (s := Set.Icc (0 : ℝ) 1) hCont
  have hRepInt :
      IntervalIntegrable (fun x => F r x * part r x) volume (0 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hSlice
  refine hRepInt.congr_ae ?_
  rw [Set.uIoc_of_le zero_le_one]
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_uIoc_zero_one_mem_Ioo] with x hxIoo hxIoc
  have hx : x ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le zero_le_one] using hxIoo (by
      simpa [Set.uIoc_of_le zero_le_one] using hxIoc)
  have hEq := hEqInterior (x := (r, x))
    (Set.mem_prod.mpr ⟨⟨le_rfl, le_rfl⟩, hx⟩)
  simp only [Function.uncurry_apply_pair] at hEq
  rw [← hEq]

/-- Fixed-time Route-C derivative substitution into the concrete physical
scalar triple. -/
theorem H1PhysicalRHSRouteCSubstitutionAt_of_classicalSolution
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    -(∫ x in (0 : ℝ)..1,
        liftDeriv2 u τ x * liftTimeDeriv u τ x) =
      H1IdentityRHSValue p u
        (H1PhysicalTaxisX p u v)
        (H1PhysicalUvxxX p u v)
        (H1PhysicalReactX p u) τ := by
  let F : ℝ → ℝ → ℝ :=
    liftDeriv2PhysicalRHSWithChemRep p u
      (liftChemotaxisDivPhysicalRep p u v)
  have hRep :
      H1PhysicalRHSRepIntegrandsContinuousStrictBefore p u v T F :=
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol
  have hEqInterior :=
    hRep.uxx_eqInterior (a := τ) (b := τ) hτ.1 le_rfl hτ.2
  have hD2 :
      IntervalIntegrable (fun x => (liftDeriv2 u τ x) ^ 2)
        volume (0 : ℝ) 1 :=
    liftDeriv2_sq_intervalIntegrable_of_rep_cont
      (u := u) (F := F) (r := τ)
      (hRep.uxx_cont (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
      hEqInterior
  have hTaxis :
      IntervalIntegrable
        (fun x => liftDeriv2 u τ x *
          H1PhysicalChemTaxisPart p u v τ x)
        volume (0 : ℝ) 1 :=
    liftDeriv2_mul_part_intervalIntegrable_of_rep_product_cont
      (u := u) (F := F) (part := H1PhysicalChemTaxisPart p u v)
      (r := τ)
      (by
        simpa [F, H1PhysicalTaxisRepIntegrand] using
          hRep.taxis_cont (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
      hEqInterior
  have hUvxx :
      IntervalIntegrable
        (fun x => liftDeriv2 u τ x *
          H1PhysicalChemUvxxPart p u v τ x)
        volume (0 : ℝ) 1 :=
    liftDeriv2_mul_part_intervalIntegrable_of_rep_product_cont
      (u := u) (F := F) (part := H1PhysicalChemUvxxPart p u v)
      (r := τ)
      (by
        simpa [F, H1PhysicalUvxxRepIntegrand] using
          hRep.uvxx_cont (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
      hEqInterior
  have hReact :
      IntervalIntegrable
        (fun x => liftDeriv2 u τ x *
          H1PhysicalLogisticReactionPart p u τ x)
        volume (0 : ℝ) 1 :=
    liftDeriv2_mul_part_intervalIntegrable_of_rep_product_cont
      (u := u) (F := F) (part := H1PhysicalLogisticReactionPart p u)
      (r := τ)
      (by
        simpa [F, H1PhysicalReactRepIntegrand] using
          hRep.react_cont (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
      hEqInterior
  have hPoint :
      Set.EqOn
        (fun x => liftTimeDeriv u τ x)
        (fun x =>
          liftDeriv2 u τ x -
            p.χ₀ *
              (H1PhysicalChemTaxisPart p u v τ x +
                H1PhysicalChemUvxxPart p u v τ x) +
            H1PhysicalLogisticReactionPart p u τ x)
        (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    have hEq := hEqInterior (x := (τ, x))
      (Set.mem_prod.mpr ⟨⟨le_rfl, le_rfl⟩, hx⟩)
    simp only [Function.uncurry_apply_pair] at hEq
    have hChem :=
      H1PhysicalChemParts_sum_eq_liftChemotaxisDivPhysicalRep
        p u v τ x
    have hEq' :
        liftDeriv2 u τ x =
          liftTimeDeriv u τ x +
            p.χ₀ *
              (H1PhysicalChemTaxisPart p u v τ x +
                H1PhysicalChemUvxxPart p u v τ x) -
            H1PhysicalLogisticReactionPart p u τ x := by
      simpa [F, liftDeriv2PhysicalRHSWithChemRep, hChem] using hEq
    linarith
  have hIntPoint :
      (∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * liftTimeDeriv u τ x) =
        ∫ x in (0 : ℝ)..1,
          ((liftDeriv2 u τ x) ^ 2 -
            p.χ₀ *
              (liftDeriv2 u τ x *
                H1PhysicalChemTaxisPart p u v τ x) -
            p.χ₀ *
              (liftDeriv2 u τ x *
                H1PhysicalChemUvxxPart p u v τ x) +
            liftDeriv2 u τ x *
              H1PhysicalLogisticReactionPart p u τ x) := by
    refine intervalIntegral_zero_one_congr_of_eqOn_Ioo ?_
    intro x hx
    have h :
        liftTimeDeriv u τ x =
          liftDeriv2 u τ x -
            p.χ₀ *
              (H1PhysicalChemTaxisPart p u v τ x +
                H1PhysicalChemUvxxPart p u v τ x) +
            H1PhysicalLogisticReactionPart p u τ x := by
      simpa using hPoint hx
    change
      liftDeriv2 u τ x * liftTimeDeriv u τ x =
        (liftDeriv2 u τ x) ^ 2 -
          p.χ₀ *
            (liftDeriv2 u τ x *
              H1PhysicalChemTaxisPart p u v τ x) -
          p.χ₀ *
            (liftDeriv2 u τ x *
              H1PhysicalChemUvxxPart p u v τ x) +
          liftDeriv2 u τ x *
            H1PhysicalLogisticReactionPart p u τ x
    rw [h]
    ring
  have hExpanded :
      (∫ x in (0 : ℝ)..1,
          ((liftDeriv2 u τ x) ^ 2 -
            p.χ₀ *
              (liftDeriv2 u τ x *
                H1PhysicalChemTaxisPart p u v τ x) -
            p.χ₀ *
              (liftDeriv2 u τ x *
                H1PhysicalChemUvxxPart p u v τ x) +
            liftDeriv2 u τ x *
              H1PhysicalLogisticReactionPart p u τ x)) =
        (∫ x in (0 : ℝ)..1, (liftDeriv2 u τ x) ^ 2) -
          p.χ₀ *
            (∫ x in (0 : ℝ)..1,
              liftDeriv2 u τ x *
                H1PhysicalChemTaxisPart p u v τ x) -
          p.χ₀ *
            (∫ x in (0 : ℝ)..1,
              liftDeriv2 u τ x *
                H1PhysicalChemUvxxPart p u v τ x) +
          ∫ x in (0 : ℝ)..1,
            liftDeriv2 u τ x *
              H1PhysicalLogisticReactionPart p u τ x := by
    rw [show
      (fun x =>
        (liftDeriv2 u τ x) ^ 2 -
          p.χ₀ *
            (liftDeriv2 u τ x *
              H1PhysicalChemTaxisPart p u v τ x) -
          p.χ₀ *
            (liftDeriv2 u τ x *
              H1PhysicalChemUvxxPart p u v τ x) +
          liftDeriv2 u τ x *
            H1PhysicalLogisticReactionPart p u τ x) =
        (fun x =>
          (((liftDeriv2 u τ x) ^ 2 -
            p.χ₀ *
              (liftDeriv2 u τ x *
                H1PhysicalChemTaxisPart p u v τ x)) -
            p.χ₀ *
              (liftDeriv2 u τ x *
                H1PhysicalChemUvxxPart p u v τ x)) +
            liftDeriv2 u τ x *
              H1PhysicalLogisticReactionPart p u τ x) by
        funext x
        ring]
    rw [intervalIntegral.integral_add
      ((hD2.sub (hTaxis.const_mul p.χ₀)).sub
        (hUvxx.const_mul p.χ₀)) hReact]
    rw [intervalIntegral.integral_sub
      (hD2.sub (hTaxis.const_mul p.χ₀))
      (hUvxx.const_mul p.χ₀)]
    rw [intervalIntegral.integral_sub hD2 (hTaxis.const_mul p.χ₀)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
  rw [hIntPoint, hExpanded]
  simp [H1IdentityRHSValue, lapL2sq, liftDeriv2,
    H1PhysicalTaxisX, H1PhysicalUvxxX, H1PhysicalReactX]
  ring

/-- Classical solutions supply the exact Route-C substitution frontier for the
concrete physical scalar triple. -/
theorem H1PhysicalRHSRouteCSubstitutionBefore_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    H1PhysicalRHSRouteCSubstitutionBefore p u v T := by
  intro τ hτ
  exact H1PhysicalRHSRouteCSubstitutionAt_of_classicalSolution
    (p := p) (T := T) (u := u) (v := v) hsol hτ

/-- Route-C finite-difference derivative plus the exact physical substitution
gives the concrete physical H¹ identity package. -/
theorem H1PhysicalRHSIdentityBefore_of_classical_uxxL1Cont_routeCSubstitution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxx : H1UxxL1ContBefore u T)
    (hsub : H1PhysicalRHSRouteCSubstitutionBefore p u v T) :
    H1PhysicalRHSIdentityBefore p u v T := by
  refine ⟨?_⟩
  intro τ hτ
  have hUxxτ : ∀ ε > 0, ∃ δ > 0,
      ∀ s, |s - τ| < δ → s ∈ Set.Ioo (0 : ℝ) T →
        ∫ x in (0 : ℝ)..1,
          ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ ≤ ε := by
    simpa [H1UxxL1ContBefore, liftDeriv2] using hUxx τ hτ.1 hτ.2
  have hder :
      HasDerivAt (H1energy u)
        (-(∫ x in (0 : ℝ)..1,
            liftDeriv2 u τ x * liftTimeDeriv u τ x)) τ :=
    H1energy_hasDerivAt_of_uxxL1Cont hsol hτ hUxxτ
  have hsub' :
      -(∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * liftTimeDeriv u τ x) =
        -(lapL2sq u τ) +
          (-p.χ₀) * H1PhysicalTaxisX p u v τ +
          (-p.χ₀) * H1PhysicalUvxxX p u v τ +
          H1PhysicalReactX p u τ := by
    simpa [H1IdentityRHSValue] using hsub τ hτ
  unfold H1EnergyIdentity
  rw [← hsub']
  exact hder

#print axioms
  H1PhysicalRHSRouteCSubstitutionBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSIdentityBefore_of_classical_uxxL1Cont_routeCSubstitution

end ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
