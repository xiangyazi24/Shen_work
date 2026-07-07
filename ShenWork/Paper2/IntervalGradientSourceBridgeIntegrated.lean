import ShenWork.Paper2.IntervalGradientSourceBridgePhysicalRep
import ShenWork.Paper2.IntervalMildToLocalExistence

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.IntervalMildToLocalExistence

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.Paper2.IntervalGradientSourceBridgeOpen

/-- A.e. in time, the classical per-slice gradient-source bridge rewrites the
weak gradient/logistic integrand as the mixed sine/cosine source integrand.

The only discarded point is the Duhamel endpoint `s = t`, where the slice
bridge would have heat time `t - s = 0`. -/
theorem gradientMildSourceIntegrand_eq_mixedSpectralSource_ae_of_classical_physicalRep
    {p : CM2Params} {T t x : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u)) :
    (fun s : ℝ =>
      (-p.χ₀) *
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) t)]
    (fun s : ℝ =>
      (-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p u s) x) := by
  rw [Set.uIoc_of_le ht0.le]
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := t) (μ := volume))]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hsIoo_t
  have hr : 0 < t - s := sub_pos.mpr hsIoo_t.2
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hsIoo_t.1, lt_trans hsIoo_t.2 htT⟩
  exact
    gradient_source_bridge_slice_open_of_classical_physicalRep
      (p := p) (T := T) (u := u) (r := t - s) (x := x) (s := s)
      hr hx hsol hsT

/-- Integrated form of the classical gradient-source bridge for the two
Duhamel source terms.

The integrability hypotheses are deliberately explicit: this theorem is the
endpoint/a.e. bridge from the per-slice identity, not a producer for the
remaining Duhamel integrability inputs. -/
theorem gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_classical_physicalRep
    {p : CM2Params} {T t x : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    (hchem_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x)
        volume (0 : ℝ) t)
    (hlog_int :
      IntervalIntegrable
        (fun s : ℝ =>
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
        volume (0 : ℝ) t) :
    gradientMildChemotaxisDuhamelTerm p u t x
      + gradientMildLogisticDuhamelTerm p u t x
      =
    ∫ s in (0 : ℝ)..t,
      ((-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p u s) x) := by
  let A : ℝ → ℝ := fun s : ℝ =>
    deriv (fun z : ℝ =>
      intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x
  let B : ℝ → ℝ := fun s : ℝ =>
    intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
  let C : ℝ → ℝ := fun s : ℝ =>
    (-p.χ₀) *
        unitIntervalSineHeatValue (t - s)
          (sineCoeffs (coupledChemDivSourceLift p u s)) x
      + unitIntervalCosineHeatValue (t - s)
          (coupledLogisticSourceCoeffs p u s) x
  have hleft :
      gradientMildChemotaxisDuhamelTerm p u t x
        + gradientMildLogisticDuhamelTerm p u t x
        = ∫ s in (0 : ℝ)..t, ((-p.χ₀) * A s + B s) := by
    rw [gradientMildChemotaxisDuhamelTerm, gradientMildLogisticDuhamelTerm]
    rw [intervalIntegral.integral_add (hchem_int.const_mul (-p.χ₀)) hlog_int]
    rw [intervalIntegral.integral_const_mul]
  calc
    gradientMildChemotaxisDuhamelTerm p u t x
        + gradientMildLogisticDuhamelTerm p u t x
        = ∫ s in (0 : ℝ)..t, ((-p.χ₀) * A s + B s) := hleft
    _ = ∫ s in (0 : ℝ)..t, C s := by
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le ht0.le]
      filter_upwards
        [(MeasureTheory.Ioo_ae_eq_Ioc
          (a := (0 : ℝ)) (b := t) (μ := volume)).symm] with s hs_ae hsIoc
      have hsIoo_t : s ∈ Set.Ioo (0 : ℝ) t := hs_ae.mp hsIoc
      have hr : 0 < t - s := sub_pos.mpr hsIoo_t.2
      have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
        ⟨hsIoo_t.1, lt_trans hsIoo_t.2 htT⟩
      simpa [A, B, C] using
        gradient_source_bridge_slice_open_of_classical_physicalRep
          (p := p) (T := T) (u := u) (r := t - s) (x := x) (s := s)
          hr hx hsol hsT
    _ = ∫ s in (0 : ℝ)..t,
        ((-p.χ₀) *
            unitIntervalSineHeatValue (t - s)
              (sineCoeffs (coupledChemDivSourceLift p u s)) x
          + unitIntervalCosineHeatValue (t - s)
              (coupledLogisticSourceCoeffs p u s) x) := rfl

end ShenWork.IntervalMildToLocalExistence
