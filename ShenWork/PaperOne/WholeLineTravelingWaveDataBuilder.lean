import ShenWork.PaperOne.WholeLineOrbitProperties
import ShenWork.PaperOne.WholeLineParabolicEquicontinuity
import ShenWork.PaperOne.WholeLineLongTimeContinuity
import ShenWork.PaperOne.WholeLineSchauderFixedPoint

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/--
Residual inputs left after the banked whole-line fields have been wired into
`WholeLineTravelingWaveData`.

The target auxiliary orbit in the assembled data is the all-time forward
extension `wholeLineForwardOrbitExtension (waveExponent c) raw_w`.
-/
structure WholeLineTravelingWaveResidualData
    (p : CMParams) (c κt D Λ : ℝ)
    (raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (p3 : CM2Params) where
  kappa_lt_kappat : waveExponent c < κt
  D_ge_one : 1 ≤ D
  paper3_chi_nonpos : p3.χ₀ ≤ 0
  schauder_approx_fixed_sequences :
    ShenWork.Paper1.LocalUniformApproxFixedPointSequences
      (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
  orbit_properties : WholeLineOrbitPropertiesData p c κt D raw_w
  longTime_deriv_bound_nonneg : 0 ≤ Λ
  longTime_image_differentiable :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap (waveExponent c) κt D) →
        ∀ n, Differentiable ℝ
          (longTimeMap
            (wholeLineForwardOrbitExtension (waveExponent c) raw_w)
            (seq n))
  longTime_image_deriv_bound :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap (waveExponent c) κt D) →
        ∀ n x,
          |deriv
            (longTimeMap
              (wholeLineForwardOrbitExtension (waveExponent c) raw_w)
              (seq n)) x| ≤ Λ
  semigroupTerm : ℝ → ℝ → ℝ
  chemDuhamel : ℝ → (ℝ → ℝ) → ℝ → ℝ
  reactionDuhamel : ℝ → (ℝ → ℝ) → ℝ → ℝ
  mild_decomp :
    ∀ t U x,
      wholeLineForwardOrbitExtension (waveExponent c) raw_w U t x =
        semigroupTerm t x + (-p.χ) * chemDuhamel t U x +
          reactionDuhamel t U x
  chemDuhamel_continuity :
    ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
        (chemDuhamel t)
  reactionDuhamel_continuity :
    ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
        (reactionDuhamel t)
  finite_time_slice_continuity :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t, Continuous
        (wholeLineForwardOrbitExtension (waveExponent c) raw_w U t)
  longTime_uniform_tail :
    LongTimeMapUniformTail (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) raw_w)
  longTime_stationarity :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineLongTimeStationarityData p c
        (wholeLineForwardOrbitExtension (waveExponent c) raw_w U)
        (wt U) (wx U) (wxx U)
        (wholeLineLongTimeLimit
          (wholeLineForwardOrbitExtension (waveExponent c) raw_w U))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
  fixedPoint_profile_contDiff2 :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ContDiff ℝ 2 U
  fixedPoint_signal_contDiff2 :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ContDiff ℝ 2 (frozenSignal p.γ U)
  translate_compactness :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ∀ L : ℝ, Tendsto U atBot (𝓝 L) → L < 1 →
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L
  translate_limit_identification :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ∀ L : ℝ,
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L →
          ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveLimitIdentification
            p3 L

def WholeLineTravelingWaveResidualData.longTimeContinuityFields
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveResidualData p c κt D Λ raw_w wt wx wxx p3) :
    WholeLineLongTimeContinuityFields (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) raw_w) :=
  wholeLine_longTime_continuity_fields_of_mildmap
    (κ := waveExponent c) (κt := κt) (D := D) (χ := p.χ)
    (w := wholeLineForwardOrbitExtension (waveExponent c) raw_w)
    (semigroupTerm := H.semigroupTerm)
    (chemDuhamel := H.chemDuhamel)
    (reactionDuhamel := H.reactionDuhamel)
    H.mild_decomp
    H.chemDuhamel_continuity
    H.reactionDuhamel_continuity
    H.finite_time_slice_continuity
    H.longTime_uniform_tail

def WholeLineTravelingWaveResidualData.longTimeParabolicEquicontinuity
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveResidualData p c κt D Λ raw_w wt wx wxx p3) :
    LongTimeMapParabolicEquicontinuity (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) raw_w) :=
  longTimeMap_parabolic_equicontinuity_of_uniform_deriv_bound
    (κ := waveExponent c) (κt := κt) (D := D)
    (w := wholeLineForwardOrbitExtension (waveExponent c) raw_w)
    H.longTime_deriv_bound_nonneg
    H.longTime_image_differentiable
    H.longTime_image_deriv_bound

/--
Constructor for the current whole-line traveling-wave data record after
consuming the discharged orbit, continuity, equicontinuity, Schauder, and
barrier-inequality wiring.
-/
def wholeLineTravelingWaveData_of_residual
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveResidualData p c κt D Λ raw_w wt wx wxx p3) :
    WholeLineTravelingWaveData p c (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) raw_w)
      wt wx wxx p3 where
  kappa_lt_kappat := H.kappa_lt_kappat
  D_ge_one := H.D_ge_one
  schauder_principle :=
    ShenWork.Paper1.localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences
      H.schauder_approx_fixed_sequences
  orbit_lower_bound := (wholeLine_orbit_fields H.orbit_properties).1
  orbit_upper_bound := (wholeLine_orbit_fields H.orbit_properties).2.1
  orbit_spatial_antitone := (wholeLine_orbit_fields H.orbit_properties).2.2
  longTime_image_continuity :=
    H.longTimeContinuityFields.longTime_image_continuity
  longTime_parabolic_equicontinuity :=
    H.longTimeParabolicEquicontinuity
  longTime_finite_time_continuity :=
    H.longTimeContinuityFields.longTime_finite_time_continuity
  longTime_uniform_tail :=
    H.longTimeContinuityFields.longTime_uniform_tail
  longTime_stationarity := H.longTime_stationarity
  fixedPoint_profile_contDiff2 := H.fixedPoint_profile_contDiff2
  fixedPoint_signal_contDiff2 := H.fixedPoint_signal_contDiff2
  translate_compactness := H.translate_compactness
  translate_limit_identification := H.translate_limit_identification
  paper3_chi_nonpos := H.paper3_chi_nonpos

#print axioms WholeLineTravelingWaveResidualData
#print axioms WholeLineTravelingWaveResidualData.longTimeContinuityFields
#print axioms WholeLineTravelingWaveResidualData.longTimeParabolicEquicontinuity
#print axioms wholeLineTravelingWaveData_of_residual

end ShenWork.PaperOne
