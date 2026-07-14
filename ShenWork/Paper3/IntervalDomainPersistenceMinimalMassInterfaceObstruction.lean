import ShenWork.Paper3.IntervalDomainPersistenceMinimalPhysicalMass
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.P3MoserEnergyContinuity

/-!
# Zero-slice mass obstruction for the original minimal persistence statement

The classical-solution API constrains only strict positive times.  Replacing
`u 0` therefore changes `HasInitialMass` without changing the physical orbit.
This gives a concrete regression theorem showing why the corrected Part 4 uses
`HasEquilibriumMassOnPositiveTimes`.
-/

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- The original zero-slice-mass formulation of Paper 3, Theorem 2.1(4), is
false on the concrete interval for every admissible constants structure. -/
theorem not_intervalDomain_Theorem_2_1_part4_anyConstants
    (C : Paper3Constants intervalDomain theorem21Part4CounterParams) :
    ¬ Theorem_2_1_part4 intervalDomain theorem21Part4CounterParams C := by
  intro hpart
  let p := theorem21Part4CounterParams
  let g : ℝ := C.gaussianLowerConst
  have hg : 0 < g := C.gaussianLowerConst_pos
  let uStar : ℝ := 2 / g
  have huStar : 0 < uStar := div_pos (by norm_num) hg
  let uZero : intervalDomain.Point → ℝ := fun _ => uStar
  let uRaw : ℝ → intervalDomain.Point → ℝ := fun _ _ => 1
  let v : ℝ → intervalDomain.Point → ℝ := fun _ _ => 1
  let u : ℝ → intervalDomain.Point → ℝ :=
    intervalDomainWithInitialSlice uZero uRaw
  have hraw :
      IsPaper2GlobalClassicalSolution intervalDomain p uRaw v := by
    simpa [p, uRaw, v, ellipticV, theorem21Part4CounterParams] using
      (zeroReaction_isPaper2ClassicalSolution p
        (by norm_num [p, theorem21Part4CounterParams])
        (by norm_num [p, theorem21Part4CounterParams])
        1 one_pos)
  have hglobal :
      IsPaper2GlobalClassicalSolution intervalDomain p u v := by
    exact intervalDomain_globalClassical_withInitialSlice
      (u₀ := uZero) hraw
  have hbdd : IsPaper2Bounded intervalDomain u := by
    refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    change intervalDomain.supNorm
      (intervalDomainWithInitialSlice uZero uRaw t) ≤ 1
    rw [intervalDomainWithInitialSlice_eq_raw_of_pos
      (u₀ := uZero) (u := uRaw) ht]
    change intervalDomainSupNorm
      (fun _ : intervalDomainPoint => (1 : ℝ)) ≤ 1
    rw [intervalDomainSupNorm_const]
    norm_num
  have hsol : PositiveGlobalBoundedSolution intervalDomain p u v :=
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbdd
  have hmass : HasInitialMass intervalDomain u uStar := by
    unfold HasInitialMass
    change intervalDomainIntegral
      (intervalDomainWithInitialSlice uZero uRaw 0) = 1 * uStar
    rw [show intervalDomainWithInitialSlice uZero uRaw 0 = uZero by
      funext x
      simp [intervalDomainWithInitialSlice]]
    change intervalDomainIntegral
      (fun _ : intervalDomainPoint => uStar) = 1 * uStar
    calc
      intervalDomainIntegral (fun _ : intervalDomainPoint => uStar) =
          ∫ _x in (0 : ℝ)..1, uStar := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        rw [intervalDomainLift, dif_pos hx]
      _ = uStar := by simp
      _ = 1 * uStar := by ring
  have hbad := hpart
    (by norm_num [p, theorem21Part4CounterParams])
    (by norm_num [p, theorem21Part4CounterParams])
    (by norm_num [p, theorem21Part4CounterParams])
    (by norm_num [p, theorem21Part4CounterParams])
    (by norm_num [p, theorem21Part4CounterParams])
    (by norm_num [p, theorem21Part4CounterParams, chiBeta])
    uStar huStar u v hsol hmass
  have hformula :
      minimalVLowerFormula C.gaussianLowerConst p.γ uStar
          (C.eventualMinimalUBound uStar) = 2 := by
    have hg_ne : C.gaussianLowerConst ≠ 0 := ne_of_gt hg
    simp [minimalVLowerFormula, p, g, uStar, theorem21Part4CounterParams]
    field_simp [hg_ne]
  have hvlim : liminfInfValue intervalDomain v = 1 := by
    let x0 : intervalDomainPoint :=
      ⟨0, (by constructor <;> norm_num)⟩
    letI : Nonempty intervalDomainPoint := ⟨x0⟩
    have hinf :
        intervalDomain.infValue
            (fun _ : intervalDomain.Point => (1 : ℝ)) = 1 := by
      change sInf (Set.range (fun _ : intervalDomainPoint => (1 : ℝ))) = 1
      rw [Set.range_const]
      simp
    simp [liminfInfValue, v, hinf]
  rw [hformula, hvlim] at hbad
  norm_num at hbad

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.not_intervalDomain_Theorem_2_1_part4_anyConstants
