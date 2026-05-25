import ShenWork.PDE.AnalyticSemigroupGen
import ShenWork.PDE.SpectralDecay

/-!
# Physical `L²(0,1)` shifted Neumann analytic semigroup estimates

This file transports the coefficient-space sectorial/resolvent estimates from
`AnalyticSemigroupGen` through the proved cosine Hilbert-basis
diagonalization.  The resulting operators act on the genuine physical
`L²(0,1)` interval space.
-/

noncomputable section

namespace ShenWork.PDE.AnalyticSemigroupPhysical

open MeasureTheory
open ShenWork.Paper3
open ShenWork.HeatKernelGradientEstimates
open ShenWork.PDE.ResolventEstimate
open ShenWork.PDE.AnalyticSemigroupGen
open scoped ENNReal

abbrev unitIntervalL2 : Type :=
  ShenWork.PDE.SpectralDecay.unitIntervalL2

/-! ### Coefficient resolvent as a bounded `ℓ²` operator -/

/-- The shifted Neumann resolvent multiplier as a linear map on coefficients. -/
def shiftedNeumannResolventCoeffLinearMap
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : z ≠ 0) (hzre : 0 ≤ z.re) :
    ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun u := coeffLp2
    (shiftedNeumannResolventCoeff ω z (fun n : ℕ => u n))
    (shiftedNeumannResolventCoeff_l2_summable
      hω hzre hz (lp2_summable u))
  map_add' u v := by
    ext n
    change shiftedNeumannResolventCoeff ω z
        (fun n : ℕ => (u + v) n) n =
      shiftedNeumannResolventCoeff ω z (fun n : ℕ => u n) n +
        shiftedNeumannResolventCoeff ω z (fun n : ℕ => v n) n
    unfold shiftedNeumannResolventCoeff
    change (z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹ *
        (((u : ℕ → ℂ) + (v : ℕ → ℂ)) n) =
      (z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹ * (u : ℕ → ℂ) n +
        (z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹ * (v : ℕ → ℂ) n
    rw [Pi.add_apply, mul_add]
  map_smul' c u := by
    ext n
    change shiftedNeumannResolventCoeff ω z
        (fun n : ℕ => (c • u) n) n =
      c * shiftedNeumannResolventCoeff ω z (fun n : ℕ => u n) n
    unfold shiftedNeumannResolventCoeff
    change (z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹ *
        ((c • (u : ℕ → ℂ)) n) =
      c * ((z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹ *
        (u : ℕ → ℂ) n)
    rw [Pi.smul_apply]
    simp [smul_eq_mul]
    ring

/-- Operator-vector form of the shifted Neumann resolvent estimate on
coefficient `ℓ²`. -/
theorem shiftedNeumannResolventCoeffLinearMap_norm_le
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : z ≠ 0) (hzre : 0 ≤ z.re)
    (u : ℓ²(ℕ, ℂ)) :
    ‖shiftedNeumannResolventCoeffLinearMap ω hω z hz hzre u‖ ≤
      ((1 : ℝ) / ‖z‖) * ‖u‖ := by
  have henergy :=
    shiftedNeumannResolventCoeff_l2_energy_le
      (ω := ω) hω (z := z) hzre hz (lp2_summable u)
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hfactor_nonneg : 0 ≤ (1 : ℝ) / ‖z‖ :=
    div_nonneg zero_le_one hzpos.le
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le (E := fun _ : ℕ => ℂ)
    (p := (2 : ℝ≥0∞)) hp
    (mul_nonneg hfactor_nonneg (norm_nonneg u)) ?_
  have hsq := lp2_norm_sq u
  have htarget :
      coeffL2Energy
          (shiftedNeumannResolventCoeff ω z (fun n : ℕ => u n)) ≤
        (((1 : ℝ) / ‖z‖) * ‖u‖) ^ 2 := by
    have henergy' :
        coeffL2Energy
            (shiftedNeumannResolventCoeff ω z (fun n : ℕ => u n)) ≤
          ((1 : ℝ) / ‖z‖) ^ 2 *
            coeffL2Energy (fun n : ℕ => u n) := by
      simpa [one_div] using henergy
    calc
      coeffL2Energy
          (shiftedNeumannResolventCoeff ω z (fun n : ℕ => u n))
          ≤ ((1 : ℝ) / ‖z‖) ^ 2 *
              coeffL2Energy (fun n : ℕ => u n) := henergy'
      _ = (((1 : ℝ) / ‖z‖) * ‖u‖) ^ 2 := by
            rw [← hsq]
            ring
  simpa [shiftedNeumannResolventCoeffLinearMap, coeffLp2,
    coeffL2Energy] using htarget

/-- The shifted Neumann resolvent multiplier as a continuous linear map on
coefficient `ℓ²`. -/
def shiftedNeumannResolventCoeffCLM
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : z ≠ 0) (hzre : 0 ≤ z.re) :
    ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  (shiftedNeumannResolventCoeffLinearMap ω hω z hz hzre).mkContinuous
    ((1 : ℝ) / ‖z‖) (by
      intro u
      exact shiftedNeumannResolventCoeffLinearMap_norm_le
        ω hω z hz hzre u)

theorem shiftedNeumannResolventCoeffCLM_apply
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : z ≠ 0) (hzre : 0 ≤ z.re)
    (u : ℓ²(ℕ, ℂ)) (n : ℕ) :
    shiftedNeumannResolventCoeffCLM ω hω z hz hzre u n =
      shiftedNeumannResolventCoeff ω z (fun n : ℕ => u n) n := by
  simp [shiftedNeumannResolventCoeffCLM,
    shiftedNeumannResolventCoeffLinearMap, coeffLp2]

/-- Operator norm form of the coefficient resolvent estimate. -/
theorem shiftedNeumannResolventCoeffCLM_opNorm_le
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : z ≠ 0) (hzre : 0 ≤ z.re) :
    ‖shiftedNeumannResolventCoeffCLM ω hω z hz hzre‖ ≤ (1 : ℝ) / ‖z‖ := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg zero_le_one hzpos.le) ?_
  intro u
  simpa [shiftedNeumannResolventCoeffCLM] using
    shiftedNeumannResolventCoeffLinearMap_norm_le ω hω z hz hzre u

/-! ### Physical `L²(0,1)` transported operators -/

/-- Physical shifted heat semigroup on `L²(0,1)`, obtained by conjugating the
diagonal coefficient multiplier by the cosine Hilbert basis. -/
def shiftedUnitIntervalNeumannHeatSemigroup
    (ω t : ℝ) (ht : 0 ≤ t) : unitIntervalL2 →L[ℂ] unitIntervalL2 :=
  unitIntervalCosineHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((shiftedNeumannHeatCoeffCLM ω t ht).comp
      unitIntervalCosineHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Cosine-basis diagonalization of the physical shifted heat semigroup. -/
theorem shiftedUnitIntervalNeumannHeatSemigroup_diagonal
    {ω t : ℝ} (ht : 0 ≤ t) (f : unitIntervalL2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (shiftedUnitIntervalNeumannHeatSemigroup ω t ht f) n =
      (Real.exp (-(shiftedNeumannEigenvalue ω n * t)) : ℂ) *
        unitIntervalCosineHilbertBasis.repr f n := by
  simp [shiftedUnitIntervalNeumannHeatSemigroup,
    shiftedNeumannHeatCoeffCLM_apply, shiftedNeumannHeatCoeff]

/-- Physical spectral-bound decay
`‖e^{-t(-Δ_N+ω)}‖_{L²→L²} ≤ exp (-ω t)`. -/
theorem shiftedUnitIntervalNeumannHeatSemigroup_opNorm_decay
    (ω t : ℝ) (ht : 0 ≤ t) :
    ‖shiftedUnitIntervalNeumannHeatSemigroup ω t ht‖ ≤
      Real.exp (-(ω * t)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _) ?_
  intro f
  have hcoeff :=
    shiftedNeumannHeatCoeffLinearMap_norm_decay
      ω t ht (unitIntervalCosineHilbertBasis.repr f)
  simpa [shiftedUnitIntervalNeumannHeatSemigroup,
    shiftedNeumannHeatCoeffCLM] using hcoeff

/-- Complex-time physical shifted heat operator on the closed right half-plane. -/
def shiftedUnitIntervalNeumannAnalyticHeatSemigroup
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : 0 ≤ z.re) :
    unitIntervalL2 →L[ℂ] unitIntervalL2 :=
  unitIntervalCosineHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((shiftedNeumannAnalyticHeatCoeffCLM ω hω z hz).comp
      unitIntervalCosineHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Cosine-basis diagonalization of the physical complex-time shifted heat
operator. -/
theorem shiftedUnitIntervalNeumannAnalyticHeatSemigroup_diagonal
    {ω : ℝ} (hω : 0 ≤ ω) {z : ℂ} (hz : 0 ≤ z.re)
    (f : unitIntervalL2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (shiftedUnitIntervalNeumannAnalyticHeatSemigroup ω hω z hz f) n =
      Complex.exp (-((shiftedNeumannEigenvalue ω n : ℂ) * z)) *
        unitIntervalCosineHilbertBasis.repr f n := by
  simp [shiftedUnitIntervalNeumannAnalyticHeatSemigroup,
    shiftedNeumannAnalyticHeatCoeffCLM_apply,
    shiftedNeumannAnalyticHeatCoeff]

/-- Right-half-plane physical boundedness of the analytic shifted heat
operator. -/
theorem shiftedUnitIntervalNeumannAnalyticHeatSemigroup_opNorm_le
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖shiftedUnitIntervalNeumannAnalyticHeatSemigroup ω hω z hz‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro f
  have hcoeff :=
    shiftedNeumannAnalyticHeatCoeffLinearMap_norm_le
      ω hω z hz (unitIntervalCosineHilbertBasis.repr f)
  simpa [shiftedUnitIntervalNeumannAnalyticHeatSemigroup,
    shiftedNeumannAnalyticHeatCoeffCLM] using hcoeff

/-- The physical complex-time operator restricts to the real-time shifted heat
semigroup on the positive real axis. -/
theorem shiftedUnitIntervalNeumannAnalyticHeatSemigroup_ofReal
    {ω t : ℝ} (hω : 0 ≤ ω) (ht : 0 ≤ t) :
    shiftedUnitIntervalNeumannAnalyticHeatSemigroup
        ω hω (t : ℂ) (by simpa using ht) =
      shiftedUnitIntervalNeumannHeatSemigroup ω t ht := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitIntervalCosineHilbertBasis.repr.injective
  ext n
  simp [shiftedUnitIntervalNeumannAnalyticHeatSemigroup_diagonal,
    shiftedUnitIntervalNeumannHeatSemigroup_diagonal]

/-- Physical shifted resolvent on `L²(0,1)`, transported from the diagonal
coefficient resolvent. -/
def shiftedUnitIntervalNeumannResolvent
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : z ≠ 0) (hzre : 0 ≤ z.re) :
    unitIntervalL2 →L[ℂ] unitIntervalL2 :=
  unitIntervalCosineHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((shiftedNeumannResolventCoeffCLM ω hω z hz hzre).comp
      unitIntervalCosineHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Cosine-basis diagonalization of the physical shifted resolvent. -/
theorem shiftedUnitIntervalNeumannResolvent_diagonal
    {ω : ℝ} (hω : 0 ≤ ω) {z : ℂ} (hz : z ≠ 0) (hzre : 0 ≤ z.re)
    (f : unitIntervalL2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (shiftedUnitIntervalNeumannResolvent ω hω z hz hzre f) n =
      (z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹ *
        unitIntervalCosineHilbertBasis.repr f n := by
  simp [shiftedUnitIntervalNeumannResolvent,
    shiftedNeumannResolventCoeffCLM_apply,
    shiftedNeumannResolventCoeff]

/-- Physical resolvent estimate
`‖(z + (-Δ_N+ω))^{-1}‖_{L²→L²} ≤ 1 / ‖z‖` in the closed right half-plane. -/
theorem shiftedUnitIntervalNeumannResolvent_opNorm_le
    (ω : ℝ) (hω : 0 ≤ ω) (z : ℂ) (hz : z ≠ 0) (hzre : 0 ≤ z.re) :
    ‖shiftedUnitIntervalNeumannResolvent ω hω z hz hzre‖ ≤
      (1 : ℝ) / ‖z‖ := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg zero_le_one hzpos.le) ?_
  intro f
  have hcoeff :=
    shiftedNeumannResolventCoeffLinearMap_norm_le
      ω hω z hz hzre (unitIntervalCosineHilbertBasis.repr f)
  simpa [shiftedUnitIntervalNeumannResolvent,
    shiftedNeumannResolventCoeffCLM] using hcoeff

/-- The unshifted physical operator above is the previously diagonalized
unit-interval Neumann heat semigroup. -/
theorem shiftedUnitIntervalNeumannHeatSemigroup_zeroShift_eq
    {t : ℝ} (ht : 0 ≤ t) :
    shiftedUnitIntervalNeumannHeatSemigroup 0 t ht =
      ShenWork.PDE.SpectralDecay.unitIntervalNeumannHeatSemigroup t ht := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitIntervalCosineHilbertBasis.repr.injective
  ext n
  have heig :
      shiftedNeumannEigenvalue 0 n =
        (ShenWork.PDE.SpectralDecay.intervalNeumannSpectrum 1).eigenvalue n := by
    simp [shiftedNeumannEigenvalue, unitIntervalNeumannSpectrum,
      ShenWork.PDE.SpectralDecay.intervalNeumannSpectrum,
      ShenWork.PDE.SpectralDecay.intervalNeumannEigenvalue]
    ring
  rw [shiftedUnitIntervalNeumannHeatSemigroup_diagonal,
    ShenWork.PDE.SpectralDecay.unitIntervalNeumannHeatSemigroup_diagonal]
  rw [heig]
  ring_nf

end ShenWork.PDE.AnalyticSemigroupPhysical
