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

end ShenWork.Paper2.IntervalGradientSourceBridgeOpen
