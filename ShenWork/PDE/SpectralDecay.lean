/-
  ShenWork/PDE/SpectralDecay.lean

  H3.1 spectral-gap subblock for the Neumann heat semigroup on an interval.

  This file builds the diagonal coefficient semigroup for the interval
  Neumann spectrum and transports the unit-interval case to physical
  `L²(0,1)` by the cosine Hilbert basis already proved in
  `HeatKernelGradientEstimates`.  The resulting `e^{tA} (I - P₀)` operator
  has the sharp spectral-gap bound with first eigenvalue `(π/L)^2`
  in coefficient form, and with `L = 1` on physical `L²`.
-/
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.Paper3.Statements

noncomputable section

namespace ShenWork.PDE.SpectralDecay

open MeasureTheory
open ShenWork.Paper3
open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates
open scoped ENNReal

/-! ### Interval Neumann spectrum -/

/-- Neumann eigenvalue `λ_n = (nπ/L)^2` on the interval of length `L`. -/
def intervalNeumannEigenvalue (L : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.pi / L) ^ 2

/-- The first nonzero Neumann eigenvalue on an interval of length `L`. -/
def intervalNeumannFirstNonzero (L : ℝ) : ℝ :=
  (Real.pi / L) ^ 2

/-- Spectral data for the one-dimensional Neumann interval of length `L`. -/
def intervalNeumannSpectrum (L : ℝ) : SpectralData where
  eigenvalue := intervalNeumannEigenvalue L
  firstNonzero := intervalNeumannFirstNonzero L

theorem intervalNeumannSpectrum_firstNonzero (L : ℝ) :
    (intervalNeumannSpectrum L).firstNonzero = (Real.pi / L) ^ 2 := by
  rfl

theorem intervalNeumannSpectrum_eigenvalue (L : ℝ) (n : ℕ) :
    (intervalNeumannSpectrum L).eigenvalue n =
      ((n : ℝ) * Real.pi / L) ^ 2 := by
  rfl

/-- For `0 < L`, the interval spectrum has first nonzero eigenvalue
`(π/L)^2`. -/
theorem intervalNeumannSpectrum_hasNeumannSpectrum {L : ℝ} (hL : 0 < L) :
    HasNeumannSpectrum (intervalNeumannSpectrum L) := by
  have hfreq_pos : 0 < Real.pi / L := div_pos Real.pi_pos hL
  refine
    { zero_eigenvalue := ?_
      eigenvalue_nonneg := ?_
      eigenvalue_pos_of_ne_zero := ?_
      firstNonzero_pos := ?_
      firstNonzero_le_eigenvalue := ?_ }
  · simp [intervalNeumannSpectrum, intervalNeumannEigenvalue]
  · intro n
    exact sq_nonneg _
  · intro n hn
    have hn_real : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have hmul_ne : (n : ℝ) * Real.pi / L ≠ 0 := by
      exact div_ne_zero (mul_ne_zero hn_real (ne_of_gt Real.pi_pos)) (ne_of_gt hL)
    exact sq_pos_of_ne_zero hmul_ne
  · exact sq_pos_of_ne_zero (ne_of_gt hfreq_pos)
  · intro n hn
    have hn_nat : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hn_real : (1 : ℝ) ≤ n := by
      exact_mod_cast hn_nat
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hle_freq :
        Real.pi / L ≤ (n : ℝ) * (Real.pi / L) :=
      calc
        Real.pi / L = (1 : ℝ) * (Real.pi / L) := by ring
        _ ≤ (n : ℝ) * (Real.pi / L) :=
          mul_le_mul_of_nonneg_right hn_real hfreq_pos.le
    have hright_nonneg : 0 ≤ (n : ℝ) * (Real.pi / L) :=
      mul_nonneg hn_nonneg hfreq_pos.le
    have hsquare :
        (Real.pi / L) ^ 2 ≤ ((n : ℝ) * (Real.pi / L)) ^ 2 :=
      (sq_le_sq₀ hfreq_pos.le hright_nonneg).mpr hle_freq
    simpa [intervalNeumannSpectrum, intervalNeumannEigenvalue,
      intervalNeumannFirstNonzero, mul_div_assoc] using hsquare

/-! ### Coefficient `ℓ²` semigroup estimate -/

/-- Coefficient `ℓ²` energy. -/
def coeffL2Energy (a : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ ^ 2

/-- Coefficient `ℓ²` norm. -/
def coeffL2Norm (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (coeffL2Energy a)

/-- Coefficient model of the projection `I - P₀`: remove the constant mode. -/
def removeZeroMode (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else a n

/-- Coefficient model of `e^{tA}`, where `A` has eigenvalues `-λ_n`. -/
def neumannSemigroupCoeff (S : SpectralData) (t : ℝ)
    (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-(S.eigenvalue n) * t) : ℂ) * a n

theorem coeffL2Energy_nonneg (a : ℕ → ℂ) :
    0 ≤ coeffL2Energy a := by
  exact tsum_nonneg fun n => sq_nonneg _

theorem coeffL2Norm_nonneg (a : ℕ → ℂ) :
    0 ≤ coeffL2Norm a := by
  exact Real.sqrt_nonneg _

theorem coeffL2Norm_sq (a : ℕ → ℂ) :
    coeffL2Norm a ^ 2 = coeffL2Energy a := by
  simpa [coeffL2Norm, pow_two] using Real.sq_sqrt (coeffL2Energy_nonneg a)

/-! ### Packaging coefficient sequences as `ℓ²` vectors -/

/-- Package a square-summable coefficient sequence as an element of `ℓ²`. -/
def coeffLp2 (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) : ℓ²(ℕ, ℂ) := by
  refine ⟨a, ?_⟩
  change Memℓp (a : PreLp (fun _ : ℕ => ℂ)) (2 : ℝ≥0∞)
  simpa [Memℓp] using ha

/-- The defining square summability of an `ℓ²` vector. -/
theorem lp2_summable (u : ℓ²(ℕ, ℂ)) :
    Summable fun n : ℕ => ‖u n‖ ^ 2 := by
  have hu : Memℓp (u : PreLp (fun _ : ℕ => ℂ)) (2 : ℝ≥0∞) := u.2
  simpa [Memℓp] using hu

/-- The `ℓ²` norm squared is the coefficient energy. -/
theorem lp2_norm_sq (u : ℓ²(ℕ, ℂ)) :
    ‖u‖ ^ 2 = coeffL2Energy (fun n : ℕ => u n) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum (E := fun _ : ℕ => ℂ)
    (p := (2 : ℝ≥0∞)) hp u
  simpa [coeffL2Energy] using h

theorem removeZeroMode_zero (a : ℕ → ℂ) :
    removeZeroMode a 0 = 0 := by
  simp [removeZeroMode]

theorem removeZeroMode_of_ne_zero {a : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) :
    removeZeroMode a n = a n := by
  simp [removeZeroMode, hn]

theorem removeZeroMode_sq_le (a : ℕ → ℂ) (n : ℕ) :
    ‖removeZeroMode a n‖ ^ 2 ≤ ‖a n‖ ^ 2 := by
  by_cases hn : n = 0
  · simp [removeZeroMode, hn]
  · simp [removeZeroMode, hn]

theorem removeZeroMode_l2_summable {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    ha
  intro n
  exact removeZeroMode_sq_le a n

theorem removeZeroMode_l2_energy_le {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (removeZeroMode a) ≤ coeffL2Energy a := by
  have hremove := removeZeroMode_l2_summable ha
  have hle : ∀ n : ℕ, ‖removeZeroMode a n‖ ^ 2 ≤ ‖a n‖ ^ 2 :=
    removeZeroMode_sq_le a
  have htsum := hremove.tsum_le_tsum hle ha
  simpa [coeffL2Energy] using htsum

theorem removeZeroMode_l2_norm_le {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (removeZeroMode a) ≤ coeffL2Norm a := by
  have henergy := removeZeroMode_l2_energy_le ha
  refine (sq_le_sq₀ (coeffL2Norm_nonneg _) (coeffL2Norm_nonneg _)).mp ?_
  simpa [coeffL2Norm_sq] using henergy

/-! ### Full coefficient semigroup as a bounded `ℓ²` map -/

/-- Pointwise squared multiplier estimate for the full Neumann semigroup. -/
theorem neumannSemigroupCoeff_sq_le_one
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖neumannSemigroupCoeff S t a n‖ ^ 2 ≤ ‖a n‖ ^ 2 := by
  have hmul_nonneg : 0 ≤ S.eigenvalue n * t :=
    mul_nonneg (H.eigenvalue_nonneg n) ht
  have hmul : -(S.eigenvalue n) * t ≤ 0 := by
    linarith
  have hexp_le : Real.exp (-(S.eigenvalue n) * t) ≤ 1 := by
    have h := Real.exp_le_exp.mpr hmul
    simpa using h
  have hexp_nonneg : 0 ≤ Real.exp (-(S.eigenvalue n) * t) :=
    Real.exp_nonneg _
  have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
  have hle :
      Real.exp (-(S.eigenvalue n) * t) * ‖a n‖ ≤ 1 * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hexp_le hnorm_nonneg
  calc
    ‖neumannSemigroupCoeff S t a n‖ ^ 2
        = (Real.exp (-(S.eigenvalue n) * t) * ‖a n‖) ^ 2 := by
            rw [neumannSemigroupCoeff, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
    _ ≤ (1 * ‖a n‖) ^ 2 := by
          exact
            (sq_le_sq₀
              (mul_nonneg hexp_nonneg hnorm_nonneg)
              (mul_nonneg zero_le_one hnorm_nonneg)).mpr hle
    _ = ‖a n‖ ^ 2 := by ring

/-- The full Neumann semigroup preserves coefficient square-summability. -/
theorem neumannSemigroupCoeff_l2_summable
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖neumannSemigroupCoeff S t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    ha
  intro n
  exact neumannSemigroupCoeff_sq_le_one H ht a n

/-- Squared `ℓ²`-energy contraction for the full Neumann semigroup. -/
theorem neumannSemigroupCoeff_l2_energy_le
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (neumannSemigroupCoeff S t a) ≤ coeffL2Energy a := by
  have hs := neumannSemigroupCoeff_l2_summable H ht ha
  have hle :
      ∀ n : ℕ,
        ‖neumannSemigroupCoeff S t a n‖ ^ 2 ≤ ‖a n‖ ^ 2 :=
    neumannSemigroupCoeff_sq_le_one H ht a
  have htsum := hs.tsum_le_tsum hle ha
  simpa [coeffL2Energy] using htsum

/-- The diagonal heat multiplier as a linear map on coefficient `ℓ²`. -/
def neumannHeatCoeffLinearMap
    (S : SpectralData) (H : HasNeumannSpectrum S) (t : ℝ) (ht : 0 ≤ t) :
    ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun u := coeffLp2 (neumannSemigroupCoeff S t (fun n : ℕ => u n))
    (neumannSemigroupCoeff_l2_summable H ht (lp2_summable u))
  map_add' u v := by
    ext n
    change neumannSemigroupCoeff S t (fun n : ℕ => (u + v) n) n =
      neumannSemigroupCoeff S t (fun n : ℕ => u n) n +
        neumannSemigroupCoeff S t (fun n : ℕ => v n) n
    unfold neumannSemigroupCoeff
    change (Real.exp (-S.eigenvalue n * t) : ℂ) *
        (((u : ℕ → ℂ) + (v : ℕ → ℂ)) n) =
      (Real.exp (-S.eigenvalue n * t) : ℂ) * (u : ℕ → ℂ) n +
        (Real.exp (-S.eigenvalue n * t) : ℂ) * (v : ℕ → ℂ) n
    rw [Pi.add_apply]
    rw [mul_add]
  map_smul' c u := by
    ext n
    change neumannSemigroupCoeff S t (fun n : ℕ => (c • u) n) n =
      c * neumannSemigroupCoeff S t (fun n : ℕ => u n) n
    unfold neumannSemigroupCoeff
    change (Real.exp (-S.eigenvalue n * t) : ℂ) *
        ((c • (u : ℕ → ℂ)) n) =
      c * ((Real.exp (-S.eigenvalue n * t) : ℂ) * (u : ℕ → ℂ) n)
    rw [Pi.smul_apply]
    simp [smul_eq_mul]
    ring_nf

/-- The coefficient heat multiplier is a contraction on `ℓ²`. -/
theorem neumannHeatCoeffLinearMap_norm_le
    (S : SpectralData) (H : HasNeumannSpectrum S) (t : ℝ) (ht : 0 ≤ t)
    (u : ℓ²(ℕ, ℂ)) :
    ‖neumannHeatCoeffLinearMap S H t ht u‖ ≤ ‖u‖ := by
  have henergy :=
    neumannSemigroupCoeff_l2_energy_le (S := S) H ht (lp2_summable u)
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le (E := fun _ : ℕ => ℂ)
    (p := (2 : ℝ≥0∞)) hp (norm_nonneg u) ?_
  have hsq := lp2_norm_sq u
  simpa [neumannHeatCoeffLinearMap, coeffLp2, coeffL2Energy, hsq] using henergy

/-- The diagonal heat multiplier as a continuous linear map on coefficient
`ℓ²`. -/
def neumannHeatCoeffCLM
    (S : SpectralData) (H : HasNeumannSpectrum S) (t : ℝ) (ht : 0 ≤ t) :
    ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  (neumannHeatCoeffLinearMap S H t ht).mkContinuous 1 (by
    intro u
    simpa using neumannHeatCoeffLinearMap_norm_le S H t ht u)

theorem neumannHeatCoeffCLM_apply
    (S : SpectralData) (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    (u : ℓ²(ℕ, ℂ)) (n : ℕ) :
    neumannHeatCoeffCLM S H t ht u n =
      neumannSemigroupCoeff S t (fun n : ℕ => u n) n := by
  simp [neumannHeatCoeffCLM, neumannHeatCoeffLinearMap, coeffLp2]

/-- The coefficient model of `I - P₀` as a linear map on `ℓ²`. -/
def removeZeroModeCoeffLinearMap : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun u := coeffLp2 (removeZeroMode (fun n : ℕ => u n))
    (removeZeroMode_l2_summable (lp2_summable u))
  map_add' u v := by
    ext n
    change removeZeroMode (fun n : ℕ => (u + v) n) n =
      removeZeroMode (fun n : ℕ => u n) n +
        removeZeroMode (fun n : ℕ => v n) n
    by_cases hn : n = 0
    · simp [removeZeroMode, hn]
    · rw [removeZeroMode_of_ne_zero
          (a := fun n : ℕ => (u + v) n) hn,
        removeZeroMode_of_ne_zero (a := fun n : ℕ => u n) hn,
        removeZeroMode_of_ne_zero (a := fun n : ℕ => v n) hn]
      exact Pi.add_apply (u : ℕ → ℂ) (v : ℕ → ℂ) n
  map_smul' c u := by
    ext n
    change removeZeroMode (fun n : ℕ => (c • u) n) n =
      c * removeZeroMode (fun n : ℕ => u n) n
    by_cases hn : n = 0
    · simp [removeZeroMode, hn]
    · simp [removeZeroMode, hn]

/-- The coefficient model of `I - P₀` as a contraction on `ℓ²`. -/
theorem removeZeroModeCoeffLinearMap_norm_le (u : ℓ²(ℕ, ℂ)) :
    ‖removeZeroModeCoeffLinearMap u‖ ≤ ‖u‖ := by
  have henergy :=
    removeZeroMode_l2_energy_le (a := fun n : ℕ => u n) (lp2_summable u)
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le (E := fun _ : ℕ => ℂ)
    (p := (2 : ℝ≥0∞)) hp (norm_nonneg u) ?_
  have hsq := lp2_norm_sq u
  simpa [removeZeroModeCoeffLinearMap, coeffLp2, coeffL2Energy, hsq] using henergy

/-- The coefficient projection complement `I - P₀` as a continuous linear map. -/
def removeZeroModeCoeffCLM : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  removeZeroModeCoeffLinearMap.mkContinuous 1 (by
    intro u
    simpa using removeZeroModeCoeffLinearMap_norm_le u)

theorem removeZeroModeCoeffCLM_apply (u : ℓ²(ℕ, ℂ)) (n : ℕ) :
    removeZeroModeCoeffCLM u n = removeZeroMode (fun n : ℕ => u n) n := by
  simp [removeZeroModeCoeffCLM, removeZeroModeCoeffLinearMap, coeffLp2]

/-- Pointwise squared multiplier estimate on the zero-mean subspace. -/
theorem neumannSemigroupCoeff_removeZero_sq_le
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 ≤
      (Real.exp (-S.firstNonzero * t)) ^ 2 * ‖removeZeroMode a n‖ ^ 2 := by
  by_cases hn : n = 0
  · simp [neumannSemigroupCoeff, removeZeroMode, hn]
  · have hLambda : S.firstNonzero ≤ S.eigenvalue n :=
      H.firstNonzero_le_eigenvalue n hn
    have hmul0 : S.firstNonzero * t ≤ S.eigenvalue n * t :=
      mul_le_mul_of_nonneg_right hLambda ht
    have hmul : -(S.eigenvalue n) * t ≤ -S.firstNonzero * t := by
      linarith
    have hexp_le :
        Real.exp (-(S.eigenvalue n) * t) ≤
          Real.exp (-S.firstNonzero * t) :=
      Real.exp_le_exp.mpr hmul
    have hexp_nonneg : 0 ≤ Real.exp (-(S.eigenvalue n) * t) :=
      Real.exp_nonneg _
    have hfirst_nonneg : 0 ≤ Real.exp (-S.firstNonzero * t) :=
      Real.exp_nonneg _
    have hnorm_nonneg : 0 ≤ ‖removeZeroMode a n‖ := norm_nonneg _
    have hle :
        Real.exp (-(S.eigenvalue n) * t) * ‖removeZeroMode a n‖ ≤
          Real.exp (-S.firstNonzero * t) * ‖removeZeroMode a n‖ :=
      mul_le_mul_of_nonneg_right hexp_le hnorm_nonneg
    calc
      ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2
          =
            (Real.exp (-(S.eigenvalue n) * t) *
              ‖removeZeroMode a n‖) ^ 2 := by
              rw [neumannSemigroupCoeff, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
      _ ≤ (Real.exp (-S.firstNonzero * t) *
              ‖removeZeroMode a n‖) ^ 2 := by
            exact
              (sq_le_sq₀
                (mul_nonneg hexp_nonneg hnorm_nonneg)
                (mul_nonneg hfirst_nonneg hnorm_nonneg)).mpr hle
      _ =
          (Real.exp (-S.firstNonzero * t)) ^ 2 *
            ‖removeZeroMode a n‖ ^ 2 := by
            ring

/-- The zero-mean Neumann semigroup preserves coefficient square-summability. -/
theorem neumannSemigroupCoeff_removeZero_l2_summable
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left ((Real.exp (-S.firstNonzero * t)) ^ 2))
  intro n
  exact neumannSemigroupCoeff_removeZero_sq_le H ht a n

/-- Squared `ℓ²`-energy decay for `e^{tA} (I-P₀)`. -/
theorem neumannSemigroupCoeff_removeZero_l2_energy_le
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Energy (neumannSemigroupCoeff S t (removeZeroMode a)) ≤
      (Real.exp (-S.firstNonzero * t)) ^ 2 *
        coeffL2Energy (removeZeroMode a) := by
  have hs :
      Summable fun n : ℕ =>
        ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 :=
    neumannSemigroupCoeff_removeZero_l2_summable H ht ha
  have hmajor :
      Summable fun n : ℕ =>
        (Real.exp (-S.firstNonzero * t)) ^ 2 *
          ‖removeZeroMode a n‖ ^ 2 :=
    ha.mul_left ((Real.exp (-S.firstNonzero * t)) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖neumannSemigroupCoeff S t (removeZeroMode a) n‖ ^ 2 ≤
          (Real.exp (-S.firstNonzero * t)) ^ 2 *
            ‖removeZeroMode a n‖ ^ 2 :=
    neumannSemigroupCoeff_removeZero_sq_le H ht a
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- `ℓ²`-norm decay for `e^{tA} (I-P₀)` on coefficients, with sharp constant
`C = 1`. -/
theorem neumannSemigroupCoeff_removeZero_l2_norm_le
    {S : SpectralData} (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Norm (neumannSemigroupCoeff S t (removeZeroMode a)) ≤
      Real.exp (-S.firstNonzero * t) * coeffL2Norm (removeZeroMode a) := by
  have henergy :=
    neumannSemigroupCoeff_removeZero_l2_energy_le H ht ha
  have hleft_nonneg :
      0 ≤ coeffL2Norm (neumannSemigroupCoeff S t (removeZeroMode a)) :=
    coeffL2Norm_nonneg _
  have hright_nonneg :
      0 ≤ Real.exp (-S.firstNonzero * t) *
        coeffL2Norm (removeZeroMode a) :=
    mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg _)
  refine (sq_le_sq₀ hleft_nonneg hright_nonneg).mp ?_
  calc
    coeffL2Norm (neumannSemigroupCoeff S t (removeZeroMode a)) ^ 2
        = coeffL2Energy (neumannSemigroupCoeff S t (removeZeroMode a)) :=
      coeffL2Norm_sq _
    _ ≤ (Real.exp (-S.firstNonzero * t)) ^ 2 *
          coeffL2Energy (removeZeroMode a) :=
      henergy
    _ = (Real.exp (-S.firstNonzero * t) *
          coeffL2Norm (removeZeroMode a)) ^ 2 := by
      rw [← coeffL2Norm_sq (removeZeroMode a)]
      ring

/-! ### `e^{tA} (I - P₀)` as a bounded coefficient operator -/

/-- Coefficient model of `e^{tA} (I - P₀)` as a linear map on `ℓ²`. -/
def neumannHeatP0ComplCoeffLinearMap
    (S : SpectralData) (H : HasNeumannSpectrum S) (t : ℝ) (ht : 0 ≤ t) :
    ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) :=
  (neumannHeatCoeffLinearMap S H t ht).comp removeZeroModeCoeffLinearMap

/-- Coefficient operator norm bound for `e^{tA} (I - P₀)`. -/
theorem neumannHeatP0ComplCoeffLinearMap_norm_le
    (S : SpectralData) (H : HasNeumannSpectrum S) (t : ℝ) (ht : 0 ≤ t)
    (u : ℓ²(ℕ, ℂ)) :
    ‖neumannHeatP0ComplCoeffLinearMap S H t ht u‖ ≤
      Real.exp (-S.firstNonzero * t) * ‖u‖ := by
  have hremove :
      Summable fun n : ℕ => ‖removeZeroMode (fun n : ℕ => u n) n‖ ^ 2 :=
    removeZeroMode_l2_summable (lp2_summable u)
  have henergy₁ :=
    neumannSemigroupCoeff_removeZero_l2_energy_le
      (S := S) H ht (a := fun n : ℕ => u n) hremove
  have hproj :=
    removeZeroMode_l2_energy_le (a := fun n : ℕ => u n) (lp2_summable u)
  have henergy :
      coeffL2Energy
          (neumannSemigroupCoeff S t (removeZeroMode (fun n : ℕ => u n))) ≤
        (Real.exp (-S.firstNonzero * t)) ^ 2 *
          coeffL2Energy (fun n : ℕ => u n) := by
    calc
      coeffL2Energy
          (neumannSemigroupCoeff S t (removeZeroMode (fun n : ℕ => u n)))
          ≤ (Real.exp (-S.firstNonzero * t)) ^ 2 *
              coeffL2Energy (removeZeroMode (fun n : ℕ => u n)) := henergy₁
      _ ≤ (Real.exp (-S.firstNonzero * t)) ^ 2 *
              coeffL2Energy (fun n : ℕ => u n) := by
            exact mul_le_mul_of_nonneg_left hproj (sq_nonneg _)
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le (E := fun _ : ℕ => ℂ)
    (p := (2 : ℝ≥0∞)) hp
    (mul_nonneg (Real.exp_nonneg _) (norm_nonneg u)) ?_
  have hsq := lp2_norm_sq u
  have htarget :
      coeffL2Energy
          (neumannSemigroupCoeff S t (removeZeroMode (fun n : ℕ => u n))) ≤
        (Real.exp (-S.firstNonzero * t) * ‖u‖) ^ 2 := by
    calc
      coeffL2Energy
          (neumannSemigroupCoeff S t (removeZeroMode (fun n : ℕ => u n)))
          ≤ (Real.exp (-S.firstNonzero * t)) ^ 2 *
              coeffL2Energy (fun n : ℕ => u n) := henergy
      _ = (Real.exp (-S.firstNonzero * t) * ‖u‖) ^ 2 := by
            rw [← hsq]
            ring
  simpa [neumannHeatP0ComplCoeffLinearMap, neumannHeatCoeffLinearMap,
    removeZeroModeCoeffLinearMap, coeffLp2, coeffL2Energy] using htarget

/-- Coefficient model of `e^{tA} (I - P₀)` as a continuous linear map. -/
def neumannHeatP0ComplCoeffCLM
    (S : SpectralData) (H : HasNeumannSpectrum S) (t : ℝ) (ht : 0 ≤ t) :
    ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  (neumannHeatP0ComplCoeffLinearMap S H t ht).mkContinuous
    (Real.exp (-S.firstNonzero * t)) (by
      intro u
      exact neumannHeatP0ComplCoeffLinearMap_norm_le S H t ht u)

theorem neumannHeatP0ComplCoeffCLM_apply
    (S : SpectralData) (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t)
    (u : ℓ²(ℕ, ℂ)) (n : ℕ) :
    neumannHeatP0ComplCoeffCLM S H t ht u n =
      neumannSemigroupCoeff S t (removeZeroMode (fun n : ℕ => u n)) n := by
  simp [neumannHeatP0ComplCoeffCLM, neumannHeatP0ComplCoeffLinearMap,
    neumannHeatCoeffLinearMap, removeZeroModeCoeffLinearMap, coeffLp2]

/-- Operator norm form of the coefficient spectral-gap estimate. -/
theorem neumannHeatP0ComplCoeffCLM_opNorm_le
    (S : SpectralData) (H : HasNeumannSpectrum S) {t : ℝ} (ht : 0 ≤ t) :
    ‖neumannHeatP0ComplCoeffCLM S H t ht‖ ≤
      Real.exp (-S.firstNonzero * t) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _) ?_
  intro u
  simpa [neumannHeatP0ComplCoeffCLM] using
    neumannHeatP0ComplCoeffLinearMap_norm_le S H t ht u

/-! ### Concrete unit-interval `L²` heat semigroup by cosine diagonalization -/

/-- Physical `L²(0,1)` space with the interval measure used by the heat-kernel
development. -/
abbrev unitIntervalL2 : Type :=
  Lp ℂ 2 (intervalMeasure 1)

/-- Concrete unit-interval Neumann heat semigroup, obtained by conjugating the
coefficient heat multiplier by the proved cosine Hilbert basis. -/
def unitIntervalNeumannHeatSemigroup (t : ℝ) (ht : 0 ≤ t) :
    unitIntervalL2 →L[ℂ] unitIntervalL2 :=
  unitIntervalCosineHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((neumannHeatCoeffCLM (intervalNeumannSpectrum 1)
        (intervalNeumannSpectrum_hasNeumannSpectrum zero_lt_one) t ht).comp
      unitIntervalCosineHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Cosine-basis diagonalization of the concrete unit-interval Neumann heat
semigroup. -/
theorem unitIntervalNeumannHeatSemigroup_diagonal
    {t : ℝ} (ht : 0 ≤ t) (f : unitIntervalL2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (unitIntervalNeumannHeatSemigroup t ht f) n =
      (Real.exp (-((intervalNeumannSpectrum 1).eigenvalue n) * t) : ℂ) *
        unitIntervalCosineHilbertBasis.repr f n := by
  simp [unitIntervalNeumannHeatSemigroup, neumannHeatCoeffCLM_apply,
    neumannSemigroupCoeff]

/-- Concrete unit-interval operator `e^{tA} (I - P₀)` on physical `L²`. -/
def unitIntervalNeumannHeatSemigroupP0Compl (t : ℝ) (ht : 0 ≤ t) :
    unitIntervalL2 →L[ℂ] unitIntervalL2 :=
  unitIntervalCosineHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((neumannHeatP0ComplCoeffCLM (intervalNeumannSpectrum 1)
        (intervalNeumannSpectrum_hasNeumannSpectrum zero_lt_one) t ht).comp
      unitIntervalCosineHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Cosine-basis diagonalization of `e^{tA} (I - P₀)` on physical `L²(0,1)`. -/
theorem unitIntervalNeumannHeatSemigroupP0Compl_diagonal
    {t : ℝ} (ht : 0 ≤ t) (f : unitIntervalL2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (unitIntervalNeumannHeatSemigroupP0Compl t ht f) n =
      (Real.exp (-((intervalNeumannSpectrum 1).eigenvalue n) * t) : ℂ) *
        removeZeroMode
          (fun n : ℕ => unitIntervalCosineHilbertBasis.repr f n) n := by
  simp [unitIntervalNeumannHeatSemigroupP0Compl,
    neumannHeatP0ComplCoeffCLM_apply, neumannSemigroupCoeff]

/-- Physical operator norm bound
`‖e^{tA} (I - P₀)‖ ≤ exp (-π² t)` on `L²(0,1)`. -/
theorem unitIntervalNeumannHeatSemigroupP0Compl_opNorm_le
    {t : ℝ} (ht : 0 ≤ t) :
    ‖unitIntervalNeumannHeatSemigroupP0Compl t ht‖ ≤
      Real.exp (-(Real.pi ^ 2) * t) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _) ?_
  intro f
  have hcoeff :=
    neumannHeatP0ComplCoeffLinearMap_norm_le
      (S := intervalNeumannSpectrum 1)
      (intervalNeumannSpectrum_hasNeumannSpectrum zero_lt_one)
      t ht (unitIntervalCosineHilbertBasis.repr f)
  simpa [unitIntervalNeumannHeatSemigroupP0Compl,
    neumannHeatP0ComplCoeffCLM, intervalNeumannSpectrum,
    intervalNeumannFirstNonzero] using hcoeff

/-- Same physical bound with any sectorial prefactor `C ≥ 1`. -/
theorem unitIntervalNeumannHeatSemigroupP0Compl_opNorm_le_with_constant
    {C t : ℝ} (hC : 1 ≤ C) (ht : 0 ≤ t) :
    ‖unitIntervalNeumannHeatSemigroupP0Compl t ht‖ ≤
      C * Real.exp (-(Real.pi ^ 2) * t) := by
  have hbase := unitIntervalNeumannHeatSemigroupP0Compl_opNorm_le ht
  have hnonneg : 0 ≤ Real.exp (-(Real.pi ^ 2) * t) := Real.exp_nonneg _
  exact hbase.trans (by simpa using mul_le_mul_of_nonneg_right hC hnonneg)

/-! ### The interval-length form used by H3.1 -/

/-- Coefficient `ℓ²` operator `e^{tA} (I - P₀)` for an interval of length `L`. -/
def intervalNeumannHeatP0ComplCoeffCLM
    (L : ℝ) (hL : 0 < L) (t : ℝ) (ht : 0 ≤ t) :
    ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  neumannHeatP0ComplCoeffCLM (intervalNeumannSpectrum L)
    (intervalNeumannSpectrum_hasNeumannSpectrum hL) t ht

/-- Coefficient operator-norm form:
`‖e^{tA} (I-P₀)‖ ≤ exp (-(π/L)^2 t)` on `ℓ²`. -/
theorem intervalNeumannHeatP0ComplCoeffCLM_opNorm_le
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) :
    ‖intervalNeumannHeatP0ComplCoeffCLM L hL t ht‖ ≤
      Real.exp (-((Real.pi / L) ^ 2) * t) := by
  simpa [intervalNeumannHeatP0ComplCoeffCLM, intervalNeumannSpectrum,
    intervalNeumannFirstNonzero] using
    neumannHeatP0ComplCoeffCLM_opNorm_le
      (S := intervalNeumannSpectrum L)
      (intervalNeumannSpectrum_hasNeumannSpectrum hL) ht

/-- Same coefficient operator-norm bound with a sectorial prefactor `C ≥ 1`. -/
theorem intervalNeumannHeatP0ComplCoeffCLM_opNorm_le_with_constant
    {C L t : ℝ} (hC : 1 ≤ C) (hL : 0 < L) (ht : 0 ≤ t) :
    ‖intervalNeumannHeatP0ComplCoeffCLM L hL t ht‖ ≤
      C * Real.exp (-((Real.pi / L) ^ 2) * t) := by
  have hbase := intervalNeumannHeatP0ComplCoeffCLM_opNorm_le hL ht
  have hnonneg : 0 ≤ Real.exp (-((Real.pi / L) ^ 2) * t) :=
    Real.exp_nonneg _
  exact hbase.trans (by simpa using mul_le_mul_of_nonneg_right hC hnonneg)

/-- Coefficient `ℓ²` norm form of
`‖e^{tA}(I-P₀)‖ ≤ exp (-(π/L)^2 t)` for the Neumann heat semigroup on an
interval of length `L`. -/
theorem intervalNeumann_semigroup_removeZero_l2_norm_le
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) := by
  simpa [intervalNeumannSpectrum, intervalNeumannFirstNonzero] using
    neumannSemigroupCoeff_removeZero_l2_norm_le
      (S := intervalNeumannSpectrum L)
      (intervalNeumannSpectrum_hasNeumannSpectrum hL) ht ha

/-- Same estimate with any prefactor `C ≥ 1`, matching the usual sectorial
semigroup notation. -/
theorem intervalNeumann_semigroup_removeZero_l2_norm_le_with_constant
    {C L t : ℝ} (hC : 1 ≤ C) (hL : 0 < L) (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖removeZeroMode a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      C * Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) := by
  have hbase :=
    intervalNeumann_semigroup_removeZero_l2_norm_le hL ht ha
  have hnonneg :
      0 ≤ Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) :=
    mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg _)
  calc
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a))
        ≤ Real.exp (-((Real.pi / L) ^ 2) * t) *
            coeffL2Norm (removeZeroMode a) := hbase
    _ ≤ C *
        (Real.exp (-((Real.pi / L) ^ 2) * t) *
          coeffL2Norm (removeZeroMode a)) := by
        simpa using mul_le_mul_of_nonneg_right hC hnonneg
    _ = C * Real.exp (-((Real.pi / L) ^ 2) * t) *
        coeffL2Norm (removeZeroMode a) := by
        ring

/-- Coefficient operator-norm form:
`e^{tA} (I-P₀)` is bounded by `exp (-(π/L)^2 t)` on `ℓ²`. -/
theorem intervalNeumann_semigroup_I_sub_P0_l2_norm_le
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a := by
  have hbase :=
    intervalNeumann_semigroup_removeZero_l2_norm_le
      (L := L) (t := t) hL ht (removeZeroMode_l2_summable ha)
  have hproj := removeZeroMode_l2_norm_le ha
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hproj (Real.exp_nonneg _))

/-- Coefficient operator-norm form with a sectorial prefactor `C ≥ 1`. -/
theorem intervalNeumann_semigroup_I_sub_P0_l2_norm_le_with_constant
    {C L t : ℝ} (hC : 1 ≤ C) (hL : 0 < L) (ht : 0 ≤ t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a)) ≤
      C * Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a := by
  have hbase :=
    intervalNeumann_semigroup_I_sub_P0_l2_norm_le
      (L := L) (t := t) hL ht ha
  have hnonneg :
      0 ≤ Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a :=
    mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg _)
  calc
    coeffL2Norm
        (neumannSemigroupCoeff (intervalNeumannSpectrum L) t
          (removeZeroMode a))
        ≤ Real.exp (-((Real.pi / L) ^ 2) * t) *
            coeffL2Norm a := hbase
    _ ≤ C * (Real.exp (-((Real.pi / L) ^ 2) * t) *
          coeffL2Norm a) := by
        simpa using mul_le_mul_of_nonneg_right hC hnonneg
    _ = C * Real.exp (-((Real.pi / L) ^ 2) * t) * coeffL2Norm a := by
        ring

end ShenWork.PDE.SpectralDecay
