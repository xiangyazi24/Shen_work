import ShenWork.Paper2.IntervalGradientSourceBridgePhysicalRep
import ShenWork.Paper2.IntervalMildToLocalExistence
import ShenWork.Paper2.IntervalDuhamelIntegrability

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
open ShenWork.IntervalDuhamelIntegrability
  (gradDuhamel_intervalIntegrable_of_joint_measurable
   valueDuhamel_intervalIntegrable_of_joint_measurable)

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

/-- Integrated classical gradient-source bridge with the Duhamel integrability
inputs discharged from windowed joint-measurability and uniform source bounds.

The proof uses zero cutoff source families outside `(0,t]`, applies the existing
bounded jointly-measurable Duhamel integrability atoms, and then transfers the
result back to the raw sources by `EqOn` on the integration interval. -/
theorem gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_windowBounds
    {p : CM2Params} {T t x : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    (hchem_meas :
      Measurable (Function.uncurry (fun s y => chemFluxLifted p (u s) y)))
    {Cchem : ℝ} (hCchem : 0 ≤ Cchem)
    (hchem_bound : ∀ s, 0 < s → s ≤ t → ∀ y, |chemFluxLifted p (u s) y| ≤ Cchem)
    (hlog_meas :
      Measurable (Function.uncurry (fun s y => logisticLifted p (u s) y)))
    {Clog : ℝ} (hClog : 0 ≤ Clog)
    (hlog_bound : ∀ s, 0 < s → s ≤ t → ∀ y, |logisticLifted p (u s) y| ≤ Clog) :
    gradientMildChemotaxisDuhamelTerm p u t x
      + gradientMildLogisticDuhamelTerm p u t x
      =
    ∫ s in (0 : ℝ)..t,
      ((-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p u s) x) := by
  let Q : ℝ → ℝ → ℝ :=
    fun s y => if 0 < s ∧ s ≤ t then chemFluxLifted p (u s) y else 0
  let L : ℝ → ℝ → ℝ :=
    fun s y => if 0 < s ∧ s ≤ t then logisticLifted p (u s) y else 0
  have hQ_meas : Measurable (Function.uncurry Q) := by
    have hbase : Measurable
        (fun z : ℝ × ℝ => chemFluxLifted p (u z.1) z.2) := by
      simpa [Function.uncurry] using hchem_meas
    simp only [Q]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hQ_sup : ∀ s y, |Q s y| ≤ Cchem := by
    intro s y
    simp only [Q]
    split_ifs with h
    · exact hchem_bound s h.1 h.2 y
    · simpa using hCchem
  have hL_meas : Measurable (Function.uncurry L) := by
    have hbase : Measurable
        (fun z : ℝ × ℝ => logisticLifted p (u z.1) z.2) := by
      simpa [Function.uncurry] using hlog_meas
    simp only [L]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hL_sup : ∀ s y, |L s y| ≤ Clog := by
    intro s y
    simp only [L]
    split_ifs with h
    · exact hlog_bound s h.1 h.2 y
    · simpa using hClog
  have hchem_cut_int :
      IntervalIntegrable
        (fun s : ℝ =>
          deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Q s) z) x)
        volume (0 : ℝ) t :=
    gradDuhamel_intervalIntegrable_of_joint_measurable ht0 hQ_meas hCchem hQ_sup x
  have hlog_cut_int :
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s) (L s) x)
        volume (0 : ℝ) t :=
    valueDuhamel_intervalIntegrable_of_joint_measurable ht0 hL_meas hClog hL_sup x
  have hchem_congr : Set.EqOn
      (fun s : ℝ =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (Q s) z) x)
      (fun s : ℝ =>
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht0.le] at hs
    have hmem : 0 < s ∧ s ≤ t := ⟨hs.1, hs.2⟩
    simp only [Q, if_pos hmem]
  have hlog_congr : Set.EqOn
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (L s) x)
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht0.le] at hs
    have hmem : 0 < s ∧ s ≤ t := ⟨hs.1, hs.2⟩
    simp only [L, if_pos hmem]
  exact
    gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_classical_physicalRep
      (p := p) (T := T) (u := u) (t := t) (x := x)
      ht0 htT hx hsol
      (hchem_cut_int.congr hchem_congr)
      (hlog_cut_int.congr hlog_congr)

end ShenWork.IntervalMildToLocalExistence
