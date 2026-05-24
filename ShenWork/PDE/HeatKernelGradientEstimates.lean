import ShenWork.PDE.HeatKernelLpEstimates
import ShenWork.PDE.CosineParsevalBridge
import Mathlib.Analysis.PSeries

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.HeatKernelGradientEstimates

open ShenWork.IntervalDomain
open ShenWork.CosineParsevalBridge

/-! ## Unit-interval Neumann spectral heat-gradient estimates -/

/-- Raw, unnormalized cosine coefficient on the unit interval. -/
def unitIntervalCosineRawCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x

/-- Bessel inequality for the positive-frequency raw cosine coefficients,
transported from AddCircle Fourier Parseval through the even-reflection
bridge. -/
theorem unitIntervalCosineRawCoeff_tsum_sq_le_integral
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    Summable (fun n : ℕ => ‖unitIntervalCosineRawCoeff f n‖ ^ 2) ∧
      (∑' n : ℕ, ‖unitIntervalCosineRawCoeff f n‖ ^ 2) ≤
        ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  let cZ : ℤ → ℝ := fun k =>
    ‖fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
      (unitIntervalEvenReflection f) k‖ ^ 2
  have hsumZ : Summable cZ := by
    exact (hasSum_sq_fourierCoeffOn
      (hab := show (-1 : ℝ) < 1 by norm_num)
      (f := unitIntervalEvenReflection f) hL2).summable
  have hnonneg : ∀ k : ℤ, 0 ≤ cZ k := by
    intro k
    exact sq_nonneg _
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro m n hmn
    exact Int.ofNat.inj hmn
  have hraw_eq :
      (fun n : ℕ => ‖unitIntervalCosineRawCoeff f n‖ ^ 2) =
        fun n : ℕ => cZ (n : ℤ) := by
    funext n
    have hcoeff :=
      unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff
        (f := f) hf (n : ℤ)
    simpa [unitIntervalCosineRawCoeff, cZ] using
      congrArg (fun z : ℂ => ‖z‖) hcoeff.symm
  have hsumNat : Summable (fun n : ℕ => cZ (n : ℤ)) :=
    hsumZ.comp_injective hinj
  refine ⟨?_, ?_⟩
  · simpa [hraw_eq] using hsumNat
  · rw [hraw_eq]
    calc
      (∑' n : ℕ, cZ (n : ℤ)) ≤ ∑' k : ℤ, cZ k :=
        tsum_comp_le_tsum_of_inj hsumZ hnonneg hinj
      _ = ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 :=
        unitIntervalEvenReflection_fourier_parseval_unit_mass hL2 hf_sq

/-- Neumann cosine coefficients normalized for the unnormalized basis
`1, cos(πx), cos(2πx), ...`.  The zeroth mode is unscaled and all positive
cosine modes carry the usual factor `2`. -/
def unitIntervalNeumannCosineCoeff (f : ℝ → ℂ) (n : ℕ) : ℝ :=
  if n = 0 then (unitIntervalCosineRawCoeff f 0).re
  else 2 * (unitIntervalCosineRawCoeff f n).re

/-- The normalized Neumann cosine coefficient map is bounded from interval
`L²` mass to coefficient `ℓ²`, with a nonsharp factor `2`. -/
theorem unitIntervalNeumannCosineCoeff_l2_bound
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    Summable (fun n : ℕ => (unitIntervalNeumannCosineCoeff f n) ^ 2) ∧
      unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f) ≤
        2 * Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := by
  obtain ⟨hraw_sum, hraw_le⟩ :=
    unitIntervalCosineRawCoeff_tsum_sq_le_integral
      (f := f) hf hL2 hf_sq
  let I : ℝ := ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact intervalIntegral.integral_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun x _hx => sq_nonneg _)
  have hre_sq_le_norm_sq :
      ∀ z : ℂ, z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    intro z
    simpa [sq] using
      (Complex.re_sq_le_normSq z).trans_eq (Complex.normSq_eq_norm_sq z)
  have hcoeff_sq_le :
      ∀ n : ℕ,
        (unitIntervalNeumannCosineCoeff f n) ^ 2 ≤
          4 * ‖unitIntervalCosineRawCoeff f n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hle := hre_sq_le_norm_sq (unitIntervalCosineRawCoeff f 0)
      have hnonneg : 0 ≤ ‖unitIntervalCosineRawCoeff f 0‖ ^ 2 := sq_nonneg _
      simp [unitIntervalNeumannCosineCoeff]
      nlinarith
    · have hle := hre_sq_le_norm_sq (unitIntervalCosineRawCoeff f n)
      simp [unitIntervalNeumannCosineCoeff, hn]
      nlinarith
  have hcoeff_sum :
      Summable fun n : ℕ => (unitIntervalNeumannCosineCoeff f n) ^ 2 :=
    Summable.of_nonneg_of_le
      (fun n => sq_nonneg (unitIntervalNeumannCosineCoeff f n))
      hcoeff_sq_le
      (hraw_sum.mul_left 4)
  have henergy_le :
      unitIntervalCosineL2TsumEnergy (unitIntervalNeumannCosineCoeff f) ≤
        4 * I := by
    calc
      unitIntervalCosineL2TsumEnergy (unitIntervalNeumannCosineCoeff f)
          = ∑' n : ℕ, (unitIntervalNeumannCosineCoeff f n) ^ 2 := rfl
      _ ≤ ∑' n : ℕ, 4 * ‖unitIntervalCosineRawCoeff f n‖ ^ 2 :=
          hcoeff_sum.tsum_le_tsum hcoeff_sq_le (hraw_sum.mul_left 4)
      _ = 4 * (∑' n : ℕ, ‖unitIntervalCosineRawCoeff f n‖ ^ 2) :=
          Summable.tsum_mul_left 4 hraw_sum
      _ ≤ 4 * I :=
          mul_le_mul_of_nonneg_left (by simpa [I] using hraw_le) (by norm_num)
  refine ⟨hcoeff_sum, ?_⟩
  calc
    unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f)
        = Real.sqrt
            (unitIntervalCosineL2TsumEnergy (unitIntervalNeumannCosineCoeff f)) := rfl
    _ ≤ Real.sqrt (4 * I) := Real.sqrt_le_sqrt henergy_le
    _ = 2 * Real.sqrt I := by
          rw [Real.sqrt_mul (show 0 ≤ (4 : ℝ) by norm_num)]
          norm_num
    _ = 2 * Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := rfl

/-- The pointwise cosine heat-gradient `L² → L∞` estimate as an `LpSeminorm`
bound on the unit interval. -/
theorem unitIntervalCosineHeatGradientValue_L2_Linfty_lpNorm_smoothing
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    lpNorm (fun x => unitIntervalCosineHeatGradientValue t a x)
        ∞ (intervalMeasure 1) ≤
      (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        unitIntervalCosineL2TsumNorm a := by
  let g : ℝ → ℝ := fun x => unitIntervalCosineHeatGradientValue t a x
  let C : ℝ :=
    (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
      unitIntervalCosineL2TsumNorm a
  have hpoint_abs :
      ∀ x, |g x| ≤ C := by
    intro x
    exact unitIntervalCosineHeatGradientValue_L2_Linfty_smoothing
      (t := t) ht hrecip ha x
  have hpoint_norm : ∀ x, ‖g x‖ ≤ C := by
    intro x
    simpa [g, Real.norm_eq_abs] using hpoint_abs x
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (div_nonneg (Real.sqrt_nonneg _) ht.le)
      (Real.sqrt_nonneg _)
  by_cases hg_meas : AEStronglyMeasurable g (intervalMeasure 1)
  · have hess :
        eLpNormEssSup g (intervalMeasure 1) ≤ ENNReal.ofReal C :=
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hpoint_norm)
    calc
      lpNorm g ∞ (intervalMeasure 1)
          = (eLpNorm g ∞ (intervalMeasure 1)).toReal := by
            exact (toReal_eLpNorm hg_meas).symm
      _ = (eLpNormEssSup g (intervalMeasure 1)).toReal := by
            rw [eLpNorm_exponent_top]
      _ ≤ (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
      _ = C := ENNReal.toReal_ofReal hC_nonneg
      _ =
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            unitIntervalCosineL2TsumNorm a := rfl
  · have hlp_zero : lpNorm g ∞ (intervalMeasure 1) = 0 := by
      simp [lpNorm, hg_meas]
    calc
      lpNorm g ∞ (intervalMeasure 1) = 0 := hlp_zero
      _ ≤ C := hC_nonneg
      _ =
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            unitIntervalCosineL2TsumNorm a := rfl

/-- The nonzero Neumann reciprocal eigenvalue trace on the unit interval is
summable. -/
theorem unitIntervalCosineReciprocalEigenvalueTerm_summable :
    Summable unitIntervalCosineReciprocalEigenvalueTerm := by
  have hterm :
      ∀ n : ℕ,
        unitIntervalCosineReciprocalEigenvalueTerm n =
          (1 / Real.pi ^ 2) * (1 / (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [unitIntervalCosineReciprocalEigenvalueTerm]
    · have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      simp [unitIntervalCosineReciprocalEigenvalueTerm, hn,
        unitIntervalCosineEigenvalue]
      field_simp [hnR, hpi]
  have hs :
      Summable
        (fun n : ℕ => (1 / Real.pi ^ 2) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left
      (1 / Real.pi ^ 2)
  exact hs.congr fun n => (hterm n).symm

/-- Unit-interval spectral Neumann heat-gradient estimate from interval `L²`
mass to `L∞`, stated for the derivative coefficient series.  This is the
Parseval-connected version of the coefficient-space estimate. -/
theorem unitIntervalNeumannSpectralHeatGradient_L2_Linfty_bound
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := by
  obtain ⟨hcoeff_sum, hcoeff_norm⟩ :=
    unitIntervalNeumannCosineCoeff_l2_bound
      (f := f) hf hL2 hf_sq
  have hbase :=
    unitIntervalCosineHeatGradientValue_L2_Linfty_lpNorm_smoothing
      (t := t) ht hrecip
      (a := unitIntervalNeumannCosineCoeff f) hcoeff_sum
  have hfactor_nonneg :
      0 ≤ unitIntervalCosineHeatGradientL2LinftyConstant / t := by
    exact div_nonneg (Real.sqrt_nonneg _) ht.le
  calc
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        ∞ (intervalMeasure 1)
        ≤
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f) :=
          hbase
    _ ≤
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            (2 * Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hcoeff_norm hfactor_nonneg
    _ =
          2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := by
          ring

/-- Unit-interval spectral Neumann heat semigroup derivative estimate,
with the derivative identified by term-by-term differentiation of the cosine
series. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L2_Linfty_bound
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := by
  obtain ⟨hcoeff_sum, _hcoeff_norm⟩ :=
    unitIntervalNeumannCosineCoeff_l2_bound
      (f := f) hf hL2 hf_sq
  have hderiv :
      (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        =
        fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x := by
    funext x
    exact unitIntervalCosineHeatValue_deriv_of_l2
      (t := t) (x := x) ht hrecip
      (a := unitIntervalNeumannCosineCoeff f) hcoeff_sum
  rw [hderiv]
  exact unitIntervalNeumannSpectralHeatGradient_L2_Linfty_bound
    (t := t) ht hrecip (f := f) hf hL2 hf_sq

/-- Unit-interval spectral Neumann heat-gradient estimate with the reciprocal
eigenvalue summability discharged by the p-series theorem. -/
theorem unitIntervalNeumannSpectralHeatGradient_L2_Linfty_bound'
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) :=
  unitIntervalNeumannSpectralHeatGradient_L2_Linfty_bound
    (t := t) ht unitIntervalCosineReciprocalEigenvalueTerm_summable
    (f := f) hf hL2 hf_sq

/-- Unit-interval spectral Neumann heat semigroup derivative estimate with the
reciprocal eigenvalue summability discharged by the p-series theorem. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L2_Linfty_bound'
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) :=
  unitIntervalNeumannSpectralHeat_deriv_L2_Linfty_bound
    (t := t) ht unitIntervalCosineReciprocalEigenvalueTerm_summable
    (f := f) hf hL2 hf_sq

/-- The half-open unit-interval Lebesgue restriction used by interval
integrals agrees with `intervalMeasure 1`; endpoints are null. -/
theorem unitIntervalIocMeasure_eq_intervalMeasure :
    volume.restrict (Set.Ioc (0 : ℝ) 1) = intervalMeasure 1 := by
  unfold intervalMeasure intervalSet
  exact restrict_Ioc_eq_restrict_Icc

/-- The concrete unit interval has total restricted measure one. -/
theorem unitIntervalMeasure_univ :
    intervalMeasure 1 Set.univ = (1 : ℝ≥0∞) := by
  unfold intervalMeasure intervalSet
  simp [Real.volume_Icc]

/-- The interval-integral `L²` mass on `[0,1]` is the square of the Mathlib
`lpNorm` at exponent `2`, stated in square-root form. -/
theorem unitInterval_sqrt_integral_norm_sq_eq_lpNorm_two
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
    Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) =
      lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  rw [← unitIntervalIocMeasure_eq_intervalMeasure]
  rw [lpNorm_eq_integral_norm_rpow_toReal]
  · rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    simp [Real.sqrt_eq_rpow]
  · norm_num
  · simp
  · simpa using hf.aestronglyMeasurable

/-- Unit-interval `L²` membership gives interval integrability of the input. -/
theorem unitInterval_memLp_two_intervalIntegrable
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1)) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)]
  change Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1))
  rw [unitIntervalIocMeasure_eq_intervalMeasure]
  exact hf_mem.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num)

/-- Unit-interval `L²` membership gives interval integrability of `‖f‖²`. -/
theorem unitInterval_memLp_two_norm_sq_intervalIntegrable
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1)) :
    IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)]
  change Integrable (fun x : ℝ => ‖f x‖ ^ 2)
    (volume.restrict (Set.Ioc (0 : ℝ) 1))
  rw [unitIntervalIocMeasure_eq_intervalMeasure]
  exact hf_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

/-- The absolute-value map sends Lebesgue measure on `(-1,1]` to a measure
dominated by twice the unit-interval measure.  This is the measure-theoretic
input for transporting `L²` membership through the even reflection. -/
theorem unitInterval_abs_map_restrict_le_two_intervalMeasure :
    Measure.map (fun x : ℝ => |x|)
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)) ≤
      (2 : ℝ≥0∞) • intervalMeasure 1 := by
  refine Measure.le_iff.2 ?_
  intro s hs
  rw [Measure.map_apply continuous_abs.measurable hs]
  rw [Measure.restrict_apply (continuous_abs.measurable hs)]
  let A : Set ℝ := (fun x : ℝ => |x|) ⁻¹' s ∩ Set.Ioc (-1 : ℝ) 1
  let P : Set ℝ := s ∩ Set.Icc (0 : ℝ) 1
  let B : Set ℝ := s ∩ Set.Ioo (0 : ℝ) 1
  let N : Set ℝ := (fun x : ℝ => -x) ⁻¹' B
  change volume A ≤ ((2 : ℝ≥0∞) • intervalMeasure 1) s
  have hsubset : A ⊆ P ∪ N := by
    intro x hx
    rcases hx with ⟨hxs, hxI⟩
    by_cases hx0 : 0 ≤ x
    · left
      refine ⟨?_, ?_⟩
      · simpa [abs_of_nonneg hx0] using hxs
      · exact ⟨hx0, hxI.2⟩
    · right
      have hxlt : x < 0 := lt_of_not_ge hx0
      have hnegpos : 0 < -x := neg_pos.mpr hxlt
      have hneglt : -x < 1 := by linarith [hxI.1]
      refine ⟨?_, ?_⟩
      · simpa [abs_of_neg hxlt] using hxs
      · exact ⟨hnegpos, hneglt⟩
  have hA_le_union : volume A ≤ volume (P ∪ N) :=
    measure_mono hsubset
  have hB_meas : MeasurableSet B := by
    exact hs.inter (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))
  have hN_eq_B : volume N = volume B := by
    have hmap :=
      Measure.map_apply (μ := (volume : Measure ℝ))
        (f := fun x : ℝ => -x) continuous_neg.measurable
        (s := B) hB_meas
    rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at hmap
    change volume ((fun x : ℝ => -x) ⁻¹' B) = volume B
    exact hmap.symm
  have hP_le : volume P ≤ intervalMeasure 1 s := by
    unfold intervalMeasure intervalSet P
    rw [Measure.restrict_apply hs]
  have hB_le : volume B ≤ intervalMeasure 1 s := by
    have hB_subset : B ⊆ s ∩ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact ⟨hx.1, ⟨hx.2.1.le, hx.2.2.le⟩⟩
    calc
      volume B ≤ volume (s ∩ Set.Icc (0 : ℝ) 1) :=
        measure_mono hB_subset
      _ = intervalMeasure 1 s := by
        unfold intervalMeasure intervalSet
        rw [Measure.restrict_apply hs]
  calc
    volume A ≤ volume (P ∪ N) := hA_le_union
    _ ≤ volume P + volume N := measure_union_le P N
    _ = volume P + volume B := by rw [hN_eq_B]
    _ ≤ intervalMeasure 1 s + intervalMeasure 1 s :=
      add_le_add hP_le hB_le
    _ = ((2 : ℝ≥0∞) • intervalMeasure 1) s := by
      rw [Measure.smul_apply]
      simp [two_mul]

/-- Unit-interval `L²` membership is stable under even reflection to
`(-1,1]`. -/
theorem unitIntervalEvenReflection_memLp_two
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1)) :
    MemLp (unitIntervalEvenReflection f) 2
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (-1 : ℝ) 1)
  have hmap :
      MemLp f (2 : ℝ≥0∞) (Measure.map (fun x : ℝ => |x|) μ) := by
    exact hf_mem.of_measure_le_smul
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (by
        simpa [μ] using unitInterval_abs_map_restrict_le_two_intervalMeasure)
  have hcomp :
      MemLp (f ∘ fun x : ℝ => |x|) (2 : ℝ≥0∞) μ := by
    exact hmap.comp_of_map continuous_abs.aemeasurable
  simpa [unitIntervalEvenReflection, Function.comp_def, μ] using hcomp

/-- Unit-interval spectral Neumann heat-gradient estimate in Mathlib
`LpSeminorm` form, from interval `L²` to `L∞`. -/
theorem unitIntervalNeumannSpectralHeatGradient_L2_Linfty_lpNorm_bound
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  simpa [unitInterval_sqrt_integral_norm_sq_eq_lpNorm_two hf] using
    unitIntervalNeumannSpectralHeatGradient_L2_Linfty_bound'
      (t := t) ht (f := f) hf hL2 hf_sq

/-- Unit-interval spectral Neumann heat semigroup derivative estimate in
Mathlib `LpSeminorm` form, from interval `L²` to `L∞`. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L2_Linfty_lpNorm_bound
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  simpa [unitInterval_sqrt_integral_norm_sq_eq_lpNorm_two hf] using
    unitIntervalNeumannSpectralHeat_deriv_L2_Linfty_bound'
      (t := t) ht (f := f) hf hL2 hf_sq

/-- On the unit interval, a pointwise norm bound controls every finite
Mathlib `lpNorm`. -/
theorem unitInterval_lpNorm_le_of_forall_norm_le
    {g : ℝ → ℝ} {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) :
    lpNorm g (ENNReal.ofReal q) (intervalMeasure 1) ≤ C := by
  by_cases hg : AEStronglyMeasurable g (intervalMeasure 1)
  · have hELp :
        eLpNorm g (ENNReal.ofReal q) (intervalMeasure 1) ≤ ENNReal.ofReal C := by
      have hbase :=
        eLpNorm_le_of_ae_bound
          (p := ENNReal.ofReal q) (μ := intervalMeasure 1)
          (f := g) (Filter.Eventually.of_forall hbound)
      simpa [unitIntervalMeasure_univ, ENNReal.toReal_ofReal hq.le] using hbase
    calc
      lpNorm g (ENNReal.ofReal q) (intervalMeasure 1)
          = (eLpNorm g (ENNReal.ofReal q) (intervalMeasure 1)).toReal := by
            exact (toReal_eLpNorm hg).symm
      _ ≤ (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hELp
      _ = C := ENNReal.toReal_ofReal hC
  · simp [lpNorm, hg, hC]

/-- Unit-interval spectral Neumann heat-gradient estimate in Mathlib
`LpSeminorm` form, from interval `L²` to finite `L^q`. -/
theorem unitIntervalNeumannSpectralHeatGradient_L2_Lq_lpNorm_bound
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  let C : ℝ :=
    2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
      lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1)
  obtain ⟨hcoeff_sum, hcoeff_norm⟩ :=
    unitIntervalNeumannCosineCoeff_l2_bound (f := f) hf hL2 hf_sq
  have hcoeff_norm_lp :
      unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f) ≤
        2 * lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) := by
    simpa [unitInterval_sqrt_integral_norm_sq_eq_lpNorm_two hf] using hcoeff_norm
  have hfactor_nonneg :
      0 ≤ unitIntervalCosineHeatGradientL2LinftyConstant / t := by
    exact div_nonneg (Real.sqrt_nonneg _) ht.le
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) hfactor_nonneg) lpNorm_nonneg
  have hpoint :
      ∀ x,
        ‖unitIntervalCosineHeatGradientValue t
          (unitIntervalNeumannCosineCoeff f) x‖ ≤ C := by
    intro x
    have hbase_abs :=
      unitIntervalCosineHeatGradientValue_L2_Linfty_smoothing
        (t := t) ht unitIntervalCosineReciprocalEigenvalueTerm_summable
        (a := unitIntervalNeumannCosineCoeff f) hcoeff_sum x
    have hbase_norm :
        ‖unitIntervalCosineHeatGradientValue t
          (unitIntervalNeumannCosineCoeff f) x‖ ≤
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            unitIntervalCosineL2TsumNorm
              (unitIntervalNeumannCosineCoeff f) := by
      simpa [Real.norm_eq_abs] using hbase_abs
    have hstep :
        (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            unitIntervalCosineL2TsumNorm
              (unitIntervalNeumannCosineCoeff f) ≤
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            (2 * lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1)) :=
      mul_le_mul_of_nonneg_left hcoeff_norm_lp hfactor_nonneg
    exact hbase_norm.trans (hstep.trans_eq (by
      dsimp [C]
      ring))
  exact unitInterval_lpNorm_le_of_forall_norm_le hq hC_nonneg hpoint

/-- Unit-interval spectral Neumann heat semigroup derivative estimate in
Mathlib `LpSeminorm` form, from interval `L²` to finite `L^q`. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L2_Lq_lpNorm_bound
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  obtain ⟨hcoeff_sum, _hcoeff_norm⟩ :=
    unitIntervalNeumannCosineCoeff_l2_bound (f := f) hf hL2 hf_sq
  have hderiv :
      (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        =
        fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x := by
    funext x
    exact unitIntervalCosineHeatValue_deriv_of_l2
      (t := t) (x := x) ht unitIntervalCosineReciprocalEigenvalueTerm_summable
      (a := unitIntervalNeumannCosineCoeff f) hcoeff_sum
  rw [hderiv]
  exact unitIntervalNeumannSpectralHeatGradient_L2_Lq_lpNorm_bound
    (t := t) (q := q) ht hq (f := f) hf hL2 hf_sq

/-- Unit-interval spectral Neumann heat-gradient estimate from `L²` to `L∞`,
with all interval/even-reflection side conditions derived from the single
Mathlib `MemLp` hypothesis. -/
theorem unitIntervalNeumannSpectralHeatGradient_L2_Linfty_lpNorm_bound_from_memLp
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) :=
  unitIntervalNeumannSpectralHeatGradient_L2_Linfty_lpNorm_bound
    (t := t) ht
    (f := f)
    (unitInterval_memLp_two_intervalIntegrable hf_mem)
    (unitIntervalEvenReflection_memLp_two hf_mem)
    (unitInterval_memLp_two_norm_sq_intervalIntegrable hf_mem)

/-- Unit-interval spectral Neumann heat semigroup derivative estimate from
`L²` to `L∞`, with all interval/even-reflection side conditions derived from
the single Mathlib `MemLp` hypothesis. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L2_Linfty_lpNorm_bound_from_memLp
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        ∞ (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) :=
  unitIntervalNeumannSpectralHeat_deriv_L2_Linfty_lpNorm_bound
    (t := t) ht
    (f := f)
    (unitInterval_memLp_two_intervalIntegrable hf_mem)
    (unitIntervalEvenReflection_memLp_two hf_mem)
    (unitInterval_memLp_two_norm_sq_intervalIntegrable hf_mem)

/-- Unit-interval spectral Neumann heat-gradient estimate from `L²` to finite
`L^q`, with all interval/even-reflection side conditions derived from the
single Mathlib `MemLp` hypothesis. -/
theorem unitIntervalNeumannSpectralHeatGradient_L2_Lq_lpNorm_bound_from_memLp
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) :=
  unitIntervalNeumannSpectralHeatGradient_L2_Lq_lpNorm_bound
    (t := t) (q := q) ht hq
    (f := f)
    (unitInterval_memLp_two_intervalIntegrable hf_mem)
    (unitIntervalEvenReflection_memLp_two hf_mem)
    (unitInterval_memLp_two_norm_sq_intervalIntegrable hf_mem)

/-- Unit-interval spectral Neumann heat semigroup derivative estimate from
`L²` to finite `L^q`, with all interval/even-reflection side conditions
derived from the single Mathlib `MemLp` hypothesis. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L2_Lq_lpNorm_bound_from_memLp
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      2 * (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        lpNorm f (2 : ℝ≥0∞) (intervalMeasure 1) :=
  unitIntervalNeumannSpectralHeat_deriv_L2_Lq_lpNorm_bound
    (t := t) (q := q) ht hq
    (f := f)
    (unitInterval_memLp_two_intervalIntegrable hf_mem)
    (unitIntervalEvenReflection_memLp_two hf_mem)
    (unitInterval_memLp_two_norm_sq_intervalIntegrable hf_mem)

end ShenWork.HeatKernelGradientEstimates
