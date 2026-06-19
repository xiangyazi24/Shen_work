import ShenWork.PDE.IntervalCoupledClassicalCorePAR

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

/-- The exact slice agreement needed to apply the T6 Duhamel closed-`C²` atom to
the coupled fixed point slice.  This is the missing bridge between the fixed
point equation and the spectral Duhamel profile. -/
def CoupledDuhamelT6SliceAgreement
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t < T →
    Set.EqOn (intervalDomainLift (u t))
      (fun x => ∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s)
          (coupledChemicalSourceCoeffs p u s) x)
      (Set.Icc (0 : ℝ) 1)

/-- The full closed-slice package supplied by T6 once the source is time-`C¹`
and the fixed point slice agrees with the corresponding Duhamel profile. -/
theorem coupledDuhamel_T6_closedSlicePack
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u))
    (hagree : CoupledDuhamelT6SliceAgreement p T u) :
    ∀ t : ℝ, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) ∧
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) ∧
      deriv (intervalDomainLift (u t)) 0 = 0 ∧
      deriv (intervalDomainLift (u t)) 1 = 0 := by
  intro t ht htT
  exact duhamelProfile_closedC2_neumann_of_timeC1_source
    hsrc ht (hagree t ht htT)

/-- Continuity of each u-slice follows from the closed-interval `C²` package
produced by T6. -/
theorem coupledDuhamel_u_cont_of_T6_closedSlicePack
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hpack : ∀ t : ℝ, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) ∧
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) ∧
      deriv (intervalDomainLift (u t)) 0 = 0 ∧
      deriv (intervalDomainLift (u t)) 1 = 0) :
    ∀ t, 0 < t → t < T → Continuous (u t) := by
  intro t ht htT
  have hcontOn : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hpack t ht htT).1.continuousOn
  have hcomp := hcontOn.comp_continuous continuous_subtype_val
    (fun x : intervalDomainPoint => x.2)
  exact hcomp.congr (fun x => by
    change intervalDomainLift (u t) x.1 = u t x
    unfold intervalDomainLift
    split_ifs with hx
    · congr
    · exact False.elim (hx x.2))

/-- The residual classical-regularity atoms after T6 has supplied the u-side
closed-spatial regularity and one-sided Neumann limits. -/
structure CoupledDuhamelClassicalResidualAfterT6
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  v_interiorC2 :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2
        (intervalDomainLift (coupledChemicalConcentration p u t))
        (Set.Ioo (0 : ℝ) 1)
  timeC1 :
    ∀ x : intervalDomainPoint, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      (DifferentiableAt ℝ (fun s : ℝ => u s x) t ∧
          DifferentiableAt ℝ
            (fun s : ℝ => coupledChemicalConcentration p u s x) t) ∧
        (ContinuousOn (fun s : ℝ => deriv (fun r : ℝ => u r x) s)
            (Set.Ioo (0 : ℝ) T) ∧
          ContinuousOn
            (fun s : ℝ =>
              deriv (fun r : ℝ => coupledChemicalConcentration p u r x) s)
            (Set.Ioo (0 : ℝ) T))
  jointTimeDeriv :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv
              (fun s : ℝ =>
                intervalDomainLift (coupledChemicalConcentration p u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)
  v_neumannLimits :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      Filter.Tendsto
          (deriv (intervalDomainLift (coupledChemicalConcentration p u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift (coupledChemicalConcentration p u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  v_closedC2 :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2
          (intervalDomainLift (coupledChemicalConcentration p u t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv (intervalDomainLift (coupledChemicalConcentration p u t)) 0 = 0 ∧
        deriv (intervalDomainLift (coupledChemicalConcentration p u t)) 1 = 0
  closedJointTimeDeriv :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv
              (fun s : ℝ =>
                intervalDomainLift (coupledChemicalConcentration p u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  jointValue :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (coupledChemicalConcentration p u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)

/-- T6 plus the residual atom list reconstructs the full classical-regularity
conjunct needed by `CoupledDuhamelClassicalCore`. -/
theorem intervalDomainClassicalRegularity_of_T6_source_and_residual
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u))
    (hagree : CoupledDuhamelT6SliceAgreement p T u)
    (R : CoupledDuhamelClassicalResidualAfterT6 p T u) :
    intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u) := by
  have hpack := coupledDuhamel_T6_closedSlicePack hsrc hagree
  refine intervalDomainClassicalRegularity_of_atoms ?_
  refine
    { interiorC2 := ?_
      timeC1 := R.timeC1
      jointTimeDeriv := R.jointTimeDeriv
      neumannLimits := ?_
      closedC2 := ?_
      closedJointTimeDeriv := R.closedJointTimeDeriv
      jointValue := R.jointValue }
  · intro t ht
    exact ⟨(hpack t ht.1 ht.2).1.mono Set.Ioo_subset_Icc_self,
      R.v_interiorC2 t ht⟩
  · intro t ht
    exact ⟨⟨(hpack t ht.1 ht.2).2.1, (hpack t ht.1 ht.2).2.2.1⟩,
      R.v_neumannLimits t ht⟩
  · intro t ht
    exact ⟨⟨(hpack t ht.1 ht.2).1, (hpack t ht.1 ht.2).2.2.2.1,
        (hpack t ht.1 ht.2).2.2.2.2⟩,
      R.v_closedC2 t ht⟩

/-- The remaining non-banked data after T6 and O1 have been wired into the
coupled bootstrap constructor. -/
structure CoupledDuhamelResidualAfterBankedT6
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  u_pos : ∀ t x, 0 < t → t < T → 0 < u t x
  pde_u : ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv u t x =
      intervalDomain.laplacian (u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
            (coupledChemicalConcentration p u t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α)
  classicalResidual : CoupledDuhamelClassicalResidualAfterT6 p T u
  initialTrace : InitialTrace intervalDomain u₀ u

/-- Regularity bootstrap from the banked T6 source atom plus the exact residual
data not supplied by T6/O1.  The concrete resolver nonnegativity, elliptic PDE,
and Neumann boundary conjuncts are discharged by
`regularityBootstrap_of_coupledDuhamel_core`. -/
theorem regularityBootstrap_of_coupledDuhamel_bankedT6_source_and_residual
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u))
    (hagree : CoupledDuhamelT6SliceAgreement p T u)
    (R : CoupledDuhamelResidualAfterBankedT6 p T u₀ u) :
    RegularityBootstrap p T u₀ u := by
  have hpack := coupledDuhamel_T6_closedSlicePack hsrc hagree
  have hclassical :
      intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u) :=
    intervalDomainClassicalRegularity_of_T6_source_and_residual
      hsrc hagree R.classicalResidual
  refine regularityBootstrap_of_coupledDuhamel_core p ?_
  exact
    { u_pos := R.u_pos
      u_nonneg := coupledDuhamel_u_nonneg_of_pos R.u_pos
      u_cont := coupledDuhamel_u_cont_of_T6_closedSlicePack hpack
      u_closedC2 := fun t ht htT => (hpack t ht htT).1
      u_neumann_left := fun t ht htT => (hpack t ht htT).2.1
      u_neumann_right := fun t ht htT => (hpack t ht htT).2.2.1
      pde_u := R.pde_u
      classicalRegularity := hclassical
      initialTrace := R.initialTrace }

#print axioms coupledDuhamel_T6_closedSlicePack
#print axioms intervalDomainClassicalRegularity_of_T6_source_and_residual
#print axioms regularityBootstrap_of_coupledDuhamel_bankedT6_source_and_residual

end ShenWork.IntervalCoupledRegularityBootstrap
