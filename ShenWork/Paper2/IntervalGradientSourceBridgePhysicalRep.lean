import ShenWork.Paper2.IntervalGradientSourceBridgeOpen
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalGradientSourceBridgeOpen

open Set
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupNeumann
open ShenWork.Paper2.IntervalDivergenceModeIdentity
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift intervalDomainChemotaxisDiv)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

/-- The physical chem-div product-rule expression is a closed-interval
continuous representative for each positive classical slice. -/
theorem coupledChemDivPhysicalRep_continuousOn_slice_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn
      (fun x : ℝ =>
        liftChemotaxisDivPhysicalRep p u (coupledChemicalConcentration p u) s x)
      (Set.Icc (0 : ℝ) 1) := by
  have hslab :
      ContinuousOn
        (Function.uncurry
          (liftChemotaxisDivPhysicalRep p u (coupledChemicalConcentration p u)))
        (Set.Icc s s ×ˢ Set.Icc (0 : ℝ) 1) :=
    liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := coupledChemicalConcentration p u)
      (T := T) (a := s) (b := s) hsol hs.1 le_rfl hs.2
  let embed : ℝ → ℝ × ℝ := fun x => (s, x)
  have hembed_cont : Continuous embed := by
    fun_prop
  have hsub :
      Set.MapsTo embed (Set.Icc (0 : ℝ) 1)
        (Set.Icc s s ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro x hx
    exact ⟨by simp [embed], hx⟩
  simpa [embed, Function.comp_def, Function.uncurry] using
    hslab.comp hembed_cont.continuousOn hsub

/-- On the open spatial interval, the literal coupled chem-div lift agrees with
the physical product-rule representative. -/
theorem coupledChemDivSourceLift_eq_physicalRep_Ioo_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Set.EqOn (coupledChemDivSourceLift p u s)
      (fun x : ℝ =>
        liftChemotaxisDivPhysicalRep p u (coupledChemicalConcentration p u) s x)
      (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  have h :=
    lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior
      (p := p) (u := u) (v := coupledChemicalConcentration p u)
      (T := T) (t := s) (x := x) hsol hs hx
  simpa [coupledChemDivSourceLift, intervalDomain] using h

/-- A classical slice supplies the endpoint-insensitive closed representative
for `coupledChemDivSourceLift`.  The representative is the physical product-rule
expression and is only asserted equal to the literal source on `(0,1)`. -/
theorem coupledChemDivSourceLift_continuousRepresentative_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ∃ Gdiv : ℝ → ℝ,
      ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
      Set.EqOn (coupledChemDivSourceLift p u s) Gdiv (Set.Ioo (0 : ℝ) 1) := by
  refine
    ⟨fun x : ℝ =>
      liftChemotaxisDivPhysicalRep p u (coupledChemicalConcentration p u) s x,
      ?_, ?_⟩
  · exact coupledChemDivPhysicalRep_continuousOn_slice_of_classical
      (p := p) (T := T) (u := u) hsol hs
  · exact coupledChemDivSourceLift_eq_physicalRep_Ioo_of_classical
      (p := p) (T := T) (u := u) hsol hs

/-- If the closed lift of an interval-domain profile is continuous on `[0,1]`,
then the subtype profile is continuous. -/
theorem intervalDomainProfile_continuous_of_lift_continuousOn_Icc
    {w : intervalDomainPoint → ℝ}
    (hw : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)) :
    Continuous w := by
  rw [← continuousOn_univ]
  have hcomp :
      ContinuousOn (fun x : intervalDomainPoint => intervalDomainLift w x.1) Set.univ :=
    hw.comp continuous_subtype_val.continuousOn (fun x _ => x.2)
  simpa [intervalDomainLift] using hcomp

/-- Interior classical slices are continuous as subtype profiles. -/
theorem intervalDomainProfile_continuous_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Continuous (u s) := by
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 s hs).1.1
  exact intervalDomainProfile_continuous_of_lift_continuousOn_Icc hC2.continuousOn

/-- Interior classical slices are nonnegative. -/
theorem intervalDomainProfile_nonneg_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ∀ y : intervalDomainPoint, 0 ≤ u s y := by
  intro y
  exact (hsol.u_pos' hs.1 hs.2 (x := y)).le

/-- Interior classical slices are bounded on the compact interval domain. -/
theorem intervalDomainProfile_abs_bound_exists_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : intervalDomainPoint, |u s y| ≤ M := by
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 s hs).1.1
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hC2.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro y
  have hBy :
      ‖intervalDomainLift (u s) y.1‖ ≤ B := hB y.1 y.2
  have hBy_abs : |intervalDomainLift (u s) y.1| ≤ B := by
    simpa [Real.norm_eq_abs] using hBy
  have hval : intervalDomainLift (u s) y.1 = u s y := by
    simp [intervalDomainLift]
  rw [hval] at hBy_abs
  exact le_trans hBy_abs (by linarith [le_abs_self B])

/-- Classical/ball gradient-source bridge with the chem-div representative
fully discharged by the physical product-rule representative. -/
theorem gradient_source_bridge_slice_open_of_classical_ball_physicalRep
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {M r x s : ℝ} (hr : 0 < r) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hu_cont : Continuous (u s))
    (hu_nonneg : ∀ y : intervalDomainPoint, 0 ≤ u s y)
    (hM : 0 < M)
    (hu_bound : ∀ y : intervalDomainPoint, |u s y| ≤ M) :
    (-p.χ₀) *
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator r (chemFluxLifted p (u s)) z) x
      + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      =
    (-p.χ₀) *
        unitIntervalSineHeatValue r
          (sineCoeffs (coupledChemDivSourceLift p u s)) x
      + unitIntervalCosineHeatValue r
          (coupledLogisticSourceCoeffs p u s) x := by
  exact gradient_source_bridge_slice_open_of_classical_ball_representative
    (p := p) (T := T) (u := u) (M := M) (r := r) (x := x) (s := s)
    hr hx hsol hs hu_cont hu_nonneg hM hu_bound
    (Gdiv := fun x : ℝ =>
      liftChemotaxisDivPhysicalRep p u (coupledChemicalConcentration p u) s x)
    (coupledChemDivPhysicalRep_continuousOn_slice_of_classical
      (p := p) (T := T) (u := u) hsol hs)
    (coupledChemDivSourceLift_eq_physicalRep_Ioo_of_classical
      (p := p) (T := T) (u := u) hsol hs)

/-- Classical gradient-source bridge for an interior slice.  Continuity,
nonnegativity, and the bounded ball input are produced from the classical
solution itself. -/
theorem gradient_source_bridge_slice_open_of_classical_physicalRep
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {r x s : ℝ} (hr : 0 < r) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    (-p.χ₀) *
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator r (chemFluxLifted p (u s)) z) x
      + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      =
    (-p.χ₀) *
        unitIntervalSineHeatValue r
          (sineCoeffs (coupledChemDivSourceLift p u s)) x
      + unitIntervalCosineHeatValue r
          (coupledLogisticSourceCoeffs p u s) x := by
  obtain ⟨M, hM, hu_bound⟩ :=
    intervalDomainProfile_abs_bound_exists_of_classical
      (p := p) (T := T) (u := u) hsol hs
  exact gradient_source_bridge_slice_open_of_classical_ball_physicalRep
    (p := p) (T := T) (u := u) (M := M) (r := r) (x := x) (s := s)
    hr hx hsol hs
    (intervalDomainProfile_continuous_of_classical
      (p := p) (T := T) (u := u) hsol hs)
    (intervalDomainProfile_nonneg_of_classical
      (p := p) (T := T) (u := u) hsol hs)
    hM hu_bound

end ShenWork.Paper2.IntervalGradientSourceBridgeOpen
