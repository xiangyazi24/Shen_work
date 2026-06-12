import ShenWork.PDE.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.PDE
open scoped Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-!
This module discharges the formal parts of `CoupledDuhamelClassicalCore` that
are already contained in, or immediate consequences of,
`intervalDomainClassicalRegularity`.

The remaining reduced frontier is the genuine parabolic step: positivity, the
pointwise u-equation, `C^{2,1}` regularity for the coupled Duhamel fixed point,
and the initial trace.
-/

/-- Reduced coupled-Duhamel classical core after extracting the duplicated
closed-spatial and endpoint data from `intervalDomainClassicalRegularity`. -/
structure CoupledDuhamelReducedClassicalCore
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  u_pos : ∀ t x, 0 < t → t < T → 0 < u t x
  pde_u : ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv u t x =
      intervalDomain.laplacian (u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
            (coupledChemicalConcentration p u t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α)
  classicalRegularity :
    intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u)
  initialTrace : InitialTrace intervalDomain u₀ u

/-- Strict positivity gives the nonnegative u-field required by the core. -/
theorem coupledDuhamel_u_nonneg_of_pos
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hu_pos : ∀ t x, 0 < t → t < T → 0 < u t x) :
    ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint, 0 ≤ u t x := by
  intro t ht htT x
  exact (hu_pos t x ht htT).le

/-- The closed-spatial `C²` conjunct gives continuity of each u-slice on the
closed interval subtype. -/
theorem coupledDuhamel_u_cont_of_classicalRegularity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hreg :
      intervalDomainClassicalRegularity T u
        (coupledChemicalConcentration p u)) :
    ∀ t, 0 < t → t < T → Continuous (u t) := by
  intro t ht htT
  have hC2 := (hreg.2.2.2.2.1 t ⟨ht, htT⟩).1
  have hcontOn :
      ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    hC2.1.continuousOn
  have hcomp := hcontOn.comp_continuous continuous_subtype_val
    (fun x : intervalDomainPoint => x.2)
  exact hcomp.congr (fun x => by
    change intervalDomainLift (u t) x.1 = u t x
    unfold intervalDomainLift
    split_ifs with hx
    · congr
    · exact False.elim (hx x.2))

/-- The closed-spatial `C²` u-conjunct of classical regularity. -/
theorem coupledDuhamel_u_closedC2_of_classicalRegularity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hreg :
      intervalDomainClassicalRegularity T u
        (coupledChemicalConcentration p u)) :
    ∀ t, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT
  exact (hreg.2.2.2.2.1 t ⟨ht, htT⟩).1.1

/-- The left one-sided Neumann u-conjunct of classical regularity. -/
theorem coupledDuhamel_u_neumann_left_of_classicalRegularity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hreg :
      intervalDomainClassicalRegularity T u
        (coupledChemicalConcentration p u)) :
    ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro t ht htT
  exact (hreg.2.2.2.1 t ⟨ht, htT⟩).1.1

/-- The right one-sided Neumann u-conjunct of classical regularity. -/
theorem coupledDuhamel_u_neumann_right_of_classicalRegularity
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hreg :
      intervalDomainClassicalRegularity T u
        (coupledChemicalConcentration p u)) :
    ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht htT
  exact (hreg.2.2.2.1 t ⟨ht, htT⟩).1.2

/-- Reduced core data assemble the full `CoupledDuhamelClassicalCore`. -/
theorem coupledDuhamelClassicalCore_of_reducedClassicalCore
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (C : CoupledDuhamelReducedClassicalCore p T u₀ u) :
    CoupledDuhamelClassicalCore p T u₀ u := by
  refine
    { u_pos := C.u_pos
      u_nonneg := coupledDuhamel_u_nonneg_of_pos C.u_pos
      u_cont := coupledDuhamel_u_cont_of_classicalRegularity
        C.classicalRegularity
      u_closedC2 := coupledDuhamel_u_closedC2_of_classicalRegularity
        C.classicalRegularity
      u_neumann_left := coupledDuhamel_u_neumann_left_of_classicalRegularity
        C.classicalRegularity
      u_neumann_right := coupledDuhamel_u_neumann_right_of_classicalRegularity
        C.classicalRegularity
      pde_u := C.pde_u
      classicalRegularity := C.classicalRegularity
      initialTrace := C.initialTrace }

/-- Reduced coupled-Duhamel core data are enough for `RegularityBootstrap`. -/
theorem regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (C : CoupledDuhamelReducedClassicalCore p T u₀ u) :
    ShenWork.IntervalDomainExistence.RegularityBootstrap p T u₀ u :=
  regularityBootstrap_of_coupledDuhamel_core p
    (coupledDuhamelClassicalCore_of_reducedClassicalCore C)

end ShenWork.IntervalCoupledRegularityBootstrap
