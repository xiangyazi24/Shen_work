import ShenWork.PDE.HeatKernelLpEstimates
import ShenWork.PDE.CosineParsevalBridge
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

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

/-- Reciprocal cubic trace used for absolute convergence of the differentiated
cosine heat series.  The zeroth term is harmless because `0⁻¹ = 0` in Lean's
field convention. -/
def unitIntervalCosineReciprocalCubeTerm (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 3

/-- The reciprocal cubic trace over positive cosine modes. -/
def unitIntervalCosineReciprocalCubeTrace : ℝ :=
  ∑' n, unitIntervalCosineReciprocalCubeTerm n

/-- The reciprocal cubic trace is summable. -/
theorem unitIntervalCosineReciprocalCubeTerm_summable :
    Summable unitIntervalCosineReciprocalCubeTerm := by
  change Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3)
  exact Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)

/-- The reciprocal cubic summand is nonnegative. -/
theorem unitIntervalCosineReciprocalCubeTerm_nonneg (n : ℕ) :
    0 ≤ unitIntervalCosineReciprocalCubeTerm n := by
  dsimp [unitIntervalCosineReciprocalCubeTerm]
  positivity

/-- Elementary Gaussian-tail estimate used to dominate the differentiated
cosine heat kernel by a reciprocal-cubic trace. -/
lemma real_sq_mul_exp_neg_le_four {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 := by
  have hbase : (x / 2) * Real.exp (-(x / 2)) ≤ 1 :=
    real_mul_exp_neg_le_one (by positivity)
  have hbase_nonneg : 0 ≤ (x / 2) * Real.exp (-(x / 2)) := by
    positivity
  have hsq :
      ((x / 2) * Real.exp (-(x / 2))) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hbase 2
  calc
    x ^ 2 * Real.exp (-x)
        = 4 * (((x / 2) * Real.exp (-(x / 2))) ^ 2) := by
          rw [mul_pow]
          have hexp_sq :
              Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
            rw [sq, ← Real.exp_add]
            ring_nf
          rw [hexp_sq]
          ring
    _ ≤ 4 * (1 : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 4 := by norm_num

/-- Pointwise absolute bound for the differentiated cosine heat weight. -/
lemma unitIntervalCosineHeatGradientPointWeight_abs_le_reciprocal_cube
    {t : ℝ} (ht : 0 < t) (x : ℝ) (n : ℕ) :
    |unitIntervalCosineHeatGradientPointWeight t x n| ≤
      (4 / (t ^ 2 * Real.pi ^ 3)) *
        unitIntervalCosineReciprocalCubeTerm n := by
  by_cases hn : n = 0
  · subst n
    simp [unitIntervalCosineHeatGradientPointWeight,
      unitIntervalCosineReciprocalCubeTerm, unitIntervalCosineEigenvalue]
  · have hnpos_real : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    let lambda : ℝ := unitIntervalCosineEigenvalue n
    have hlambda_pos : 0 < lambda := by
      dsimp [lambda, unitIntervalCosineEigenvalue]
      exact sq_pos_of_pos (mul_pos hnpos_real hpi_pos)
    let z : ℝ := t * lambda
    have hz_nonneg : 0 ≤ z := by
      dsimp [z]
      positivity
    have hgauss : z ^ 2 * Real.exp (-z) ≤ 4 :=
      real_sq_mul_exp_neg_le_four hz_nonneg
    have hden_pos : 0 < t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3 := by
      positivity
    have hscale_nonneg :
        0 ≤ 1 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3) := by
      positivity
    have hmain :
        (n : ℝ) * Real.pi * Real.exp (-t * lambda) ≤
          4 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3) := by
      calc
        (n : ℝ) * Real.pi * Real.exp (-t * lambda)
            =
              (1 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3)) *
                (z ^ 2 * Real.exp (-z)) := by
              dsimp [z, lambda, unitIntervalCosineEigenvalue]
              field_simp [ne_of_gt ht, ne_of_gt hpi_pos,
                ne_of_gt hnpos_real]
        _ ≤
              (1 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3)) * 4 :=
              mul_le_mul_of_nonneg_left hgauss hscale_nonneg
        _ = 4 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3) := by ring
    have hweight :
        |unitIntervalCosineHeatGradientPointWeight t x n| ≤
          (n : ℝ) * Real.pi * Real.exp (-t * lambda) := by
      dsimp [unitIntervalCosineHeatGradientPointWeight, lambda,
        unitIntervalCosineEigenvalue]
      rw [abs_mul, abs_mul, abs_neg]
      have hfreq_nonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
      rw [abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg hfreq_nonneg]
      calc
        Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2) *
            ((n : ℝ) * Real.pi *
              |Real.sin ((n : ℝ) * Real.pi * x)|)
            ≤
              Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2) *
                ((n : ℝ) * Real.pi * 1) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (Real.abs_sin_le_one _) hfreq_nonneg)
                (Real.exp_nonneg _)
        _ = (n : ℝ) * Real.pi *
              Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2) := by ring
    calc
      |unitIntervalCosineHeatGradientPointWeight t x n|
          ≤ (n : ℝ) * Real.pi * Real.exp (-t * lambda) := hweight
      _ ≤ 4 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3) := hmain
      _ =
          (4 / (t ^ 2 * Real.pi ^ 3)) *
            unitIntervalCosineReciprocalCubeTerm n := by
          dsimp [unitIntervalCosineReciprocalCubeTerm]
          field_simp [ne_of_gt ht, ne_of_gt hpi_pos,
            ne_of_gt hnpos_real]

/-- Raw cosine coefficients are controlled by the interval `L¹` mass. -/
theorem unitIntervalCosineRawCoeff_norm_le_integral_norm
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) (n : ℕ) :
    ‖unitIntervalCosineRawCoeff f n‖ ≤
      ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  unfold unitIntervalCosineRawCoeff
  have hbound :
      ∀ᵐ x ∂(volume : Measure ℝ),
        x ∈ Set.Ioc (0 : ℝ) 1 →
          ‖(Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x‖ ≤ ‖f x‖ := by
    exact Filter.Eventually.of_forall fun x _hx => by
      calc
        ‖(Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x‖
            = ‖(Real.cos ((n : ℝ) * Real.pi * x) : ℂ)‖ * ‖f x‖ := by
              rw [norm_mul]
        _ ≤ 1 * ‖f x‖ := by
              exact mul_le_mul_of_nonneg_right
                (by
                  rw [Complex.norm_real, Real.norm_eq_abs]
                  exact
                    Real.abs_cos_le_one ((n : ℝ) * Real.pi * x))
                (norm_nonneg _)
        _ = ‖f x‖ := by ring
  exact intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ =>
      (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x)
    (g := fun x : ℝ => ‖f x‖)
    (show (0 : ℝ) ≤ 1 by norm_num) hbound hf.norm

/-- Normalized Neumann cosine coefficients are controlled by twice the
interval `L¹` mass. -/
theorem unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) (n : ℕ) :
    |unitIntervalNeumannCosineCoeff f n| ≤
      2 * ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  let I : ℝ := ∫ x in (0 : ℝ)..1, ‖f x‖
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact intervalIntegral.integral_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun x _hx => norm_nonneg (f x))
  have hraw :=
    unitIntervalCosineRawCoeff_norm_le_integral_norm
      (f := f) hf n
  have hre :
      |(unitIntervalCosineRawCoeff f n).re| ≤ I := by
    exact (RCLike.abs_re_le_norm (unitIntervalCosineRawCoeff f n)).trans
      (by simpa [I] using hraw)
  by_cases hn : n = 0
  · subst n
    simp [unitIntervalNeumannCosineCoeff]
    exact hre.trans (by nlinarith)
  · simp [unitIntervalNeumannCosineCoeff, hn, abs_mul]
    exact hre

/-- Absolute-convergence constant for the spectral Neumann heat-gradient
`L¹ → L∞` bound on the unit interval. -/
def unitIntervalCosineGradientL1LinftyConstant : ℝ :=
  (8 / Real.pi ^ 3) * unitIntervalCosineReciprocalCubeTrace

/-- The `L¹ → L∞` gradient constant is nonnegative. -/
theorem unitIntervalCosineGradientL1LinftyConstant_nonneg :
    0 ≤ unitIntervalCosineGradientL1LinftyConstant := by
  dsimp [unitIntervalCosineGradientL1LinftyConstant,
    unitIntervalCosineReciprocalCubeTrace]
  exact mul_nonneg (by positivity)
    (tsum_nonneg unitIntervalCosineReciprocalCubeTerm_nonneg)

/-- The single-exponential cosine heat trace is summable at positive time. -/
lemma unitIntervalCosineHeatTrace_single_exp_summable {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) := by
  have ht2 : 0 < t / 2 := by positivity
  have h :=
    unitIntervalCosineHeatTrace_summable
      (t := t / 2) ht2 unitIntervalCosineReciprocalEigenvalueTerm_summable
  refine h.congr ?_
  intro n
  congr 1
  ring

/-- Pointwise absolute bound for one heat-weighted cosine mode. -/
lemma unitIntervalCosineHeatPointWeight_abs_le_exp
    (t x : ℝ) (n : ℕ) :
    |unitIntervalCosineHeatPointWeight t x n| ≤
      Real.exp (-t * unitIntervalCosineEigenvalue n) := by
  dsimp [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode]
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_of_le_one_right (Real.exp_nonneg _)
    (Real.abs_cos_le_one ((n : ℝ) * Real.pi * x))

/-- Absolute summable majorant for one differentiated Neumann spectral heat
term with `L¹` input data. -/
lemma unitIntervalNeumannSpectralHeatGradient_L1_term_norm_bound
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1)
    (y : ℝ) (n : ℕ) :
    ‖unitIntervalCosineHeatGradientPointWeight t y n *
        unitIntervalNeumannCosineCoeff f n‖ ≤
      (8 * (∫ z in (0 : ℝ)..1, ‖f z‖) /
          (t ^ 2 * Real.pi ^ 3)) *
        unitIntervalCosineReciprocalCubeTerm n := by
  let I : ℝ := ∫ z in (0 : ℝ)..1, ‖f z‖
  have hw :=
    unitIntervalCosineHeatGradientPointWeight_abs_le_reciprocal_cube
      (t := t) ht y n
  have ha :=
    unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm
      (f := f) hf n
  have hfactor_nonneg :
      0 ≤ (4 / (t ^ 2 * Real.pi ^ 3)) *
        unitIntervalCosineReciprocalCubeTerm n := by
    exact mul_nonneg (by positivity)
      (unitIntervalCosineReciprocalCubeTerm_nonneg n)
  calc
    ‖unitIntervalCosineHeatGradientPointWeight t y n *
        unitIntervalNeumannCosineCoeff f n‖
        =
          |unitIntervalCosineHeatGradientPointWeight t y n| *
            |unitIntervalNeumannCosineCoeff f n| := by
          rw [Real.norm_eq_abs, abs_mul]
    _ ≤
          ((4 / (t ^ 2 * Real.pi ^ 3)) *
              unitIntervalCosineReciprocalCubeTerm n) *
            |unitIntervalNeumannCosineCoeff f n| :=
          mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    _ ≤
          ((4 / (t ^ 2 * Real.pi ^ 3)) *
              unitIntervalCosineReciprocalCubeTerm n) *
            (2 * I) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [I] using ha) hfactor_nonneg
    _ =
          (8 * (∫ z in (0 : ℝ)..1, ‖f z‖) /
              (t ^ 2 * Real.pi ^ 3)) *
            unitIntervalCosineReciprocalCubeTerm n := by
          dsimp [I]
          ring

/-- Pointwise `L¹ → L∞` smoothing for the spectral Neumann heat-gradient
series on the unit interval. -/
theorem unitIntervalNeumannSpectralHeatGradient_L1_Linfty_pointwise_bound
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) (x : ℝ) :
    |unitIntervalCosineHeatGradientValue t
        (unitIntervalNeumannCosineCoeff f) x| ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        ∫ y in (0 : ℝ)..1, ‖f y‖ := by
  let I : ℝ := ∫ y in (0 : ℝ)..1, ‖f y‖
  let B : ℝ := 8 * I / (t ^ 2 * Real.pi ^ 3)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact intervalIntegral.integral_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun y _hy => norm_nonneg (f y))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmajor_summable :
      Summable fun n : ℕ =>
        B * unitIntervalCosineReciprocalCubeTerm n :=
    unitIntervalCosineReciprocalCubeTerm_summable.mul_left B
  have hterm_bound :
      ∀ n : ℕ,
        ‖unitIntervalCosineHeatGradientPointWeight t x n *
            unitIntervalNeumannCosineCoeff f n‖ ≤
          B * unitIntervalCosineReciprocalCubeTerm n := by
    intro n
    have hw :=
      unitIntervalCosineHeatGradientPointWeight_abs_le_reciprocal_cube
        (t := t) ht x n
    have ha :=
      unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm
        (f := f) hf n
    have hfactor_nonneg :
        0 ≤ (4 / (t ^ 2 * Real.pi ^ 3)) *
          unitIntervalCosineReciprocalCubeTerm n := by
      exact mul_nonneg (by positivity)
        (unitIntervalCosineReciprocalCubeTerm_nonneg n)
    calc
      ‖unitIntervalCosineHeatGradientPointWeight t x n *
          unitIntervalNeumannCosineCoeff f n‖
          =
            |unitIntervalCosineHeatGradientPointWeight t x n| *
              |unitIntervalNeumannCosineCoeff f n| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤
            ((4 / (t ^ 2 * Real.pi ^ 3)) *
                unitIntervalCosineReciprocalCubeTerm n) *
              |unitIntervalNeumannCosineCoeff f n| :=
            mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ ≤
            ((4 / (t ^ 2 * Real.pi ^ 3)) *
                unitIntervalCosineReciprocalCubeTerm n) *
              (2 * I) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [I] using ha) hfactor_nonneg
      _ = B * unitIntervalCosineReciprocalCubeTerm n := by
            dsimp [B]
            ring
  have hnorm_summable :
      Summable fun n : ℕ =>
        ‖unitIntervalCosineHeatGradientPointWeight t x n *
            unitIntervalNeumannCosineCoeff f n‖ :=
    Summable.of_nonneg_of_le
      (fun n => norm_nonneg _)
      hterm_bound hmajor_summable
  calc
    |unitIntervalCosineHeatGradientValue t
        (unitIntervalNeumannCosineCoeff f) x|
        =
          ‖∑' n : ℕ,
            unitIntervalCosineHeatGradientPointWeight t x n *
              unitIntervalNeumannCosineCoeff f n‖ := by
          rw [Real.norm_eq_abs]
          rfl
    _ ≤
          ∑' n : ℕ,
            ‖unitIntervalCosineHeatGradientPointWeight t x n *
              unitIntervalNeumannCosineCoeff f n‖ :=
          norm_tsum_le_tsum_norm hnorm_summable
    _ ≤
          ∑' n : ℕ,
            B * unitIntervalCosineReciprocalCubeTerm n :=
          hnorm_summable.tsum_le_tsum hterm_bound hmajor_summable
    _ =
          B * unitIntervalCosineReciprocalCubeTrace := by
          dsimp [unitIntervalCosineReciprocalCubeTrace]
          exact Summable.tsum_mul_left B
            unitIntervalCosineReciprocalCubeTerm_summable
    _ =
          (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
            ∫ y in (0 : ℝ)..1, ‖f y‖ := by
          dsimp [B, I, unitIntervalCosineGradientL1LinftyConstant]
          field_simp [ne_of_gt ht, Real.pi_ne_zero]

/-- Term-by-term differentiation for the Neumann spectral heat series with
`L¹` input data. -/
theorem unitIntervalNeumannSpectralHeat_deriv_eq_gradient_of_L1
    {t x : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
    deriv
        (fun z =>
          unitIntervalCosineHeatValue t
            (unitIntervalNeumannCosineCoeff f) z) x =
      unitIntervalCosineHeatGradientValue t
        (unitIntervalNeumannCosineCoeff f) x := by
  let I : ℝ := ∫ z in (0 : ℝ)..1, ‖f z‖
  let B : ℝ := 8 * I / (t ^ 2 * Real.pi ^ 3)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact intervalIntegral.integral_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun z _hz => norm_nonneg (f z))
  have hu :
      Summable fun n : ℕ =>
        B * unitIntervalCosineReciprocalCubeTerm n :=
    unitIntervalCosineReciprocalCubeTerm_summable.mul_left B
  have hbound :
      ∀ n y,
        ‖unitIntervalCosineHeatGradientPointWeight t y n *
            unitIntervalNeumannCosineCoeff f n‖ ≤
          B * unitIntervalCosineReciprocalCubeTerm n := by
    intro n y
    simpa [B, I] using
      unitIntervalNeumannSpectralHeatGradient_L1_term_norm_bound
        (t := t) ht (f := f) hf y n
  have htrace :=
    unitIntervalCosineHeatTrace_single_exp_summable (t := t) ht
  have hvalue_major :
      Summable fun n : ℕ =>
        (2 * I) * Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    htrace.mul_left (2 * I)
  have hvalue_bound :
      ∀ n : ℕ,
        ‖unitIntervalCosineHeatPointWeight t 0 n *
            unitIntervalNeumannCosineCoeff f n‖ ≤
          (2 * I) * Real.exp (-t * unitIntervalCosineEigenvalue n) := by
    intro n
    have hw := unitIntervalCosineHeatPointWeight_abs_le_exp t 0 n
    have ha :=
      unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm
        (f := f) hf n
    calc
      ‖unitIntervalCosineHeatPointWeight t 0 n *
          unitIntervalNeumannCosineCoeff f n‖
          =
            |unitIntervalCosineHeatPointWeight t 0 n| *
              |unitIntervalNeumannCosineCoeff f n| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤
            Real.exp (-t * unitIntervalCosineEigenvalue n) *
              |unitIntervalNeumannCosineCoeff f n| :=
            mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ ≤
            Real.exp (-t * unitIntervalCosineEigenvalue n) * (2 * I) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [I] using ha) (Real.exp_nonneg _)
      _ =
            (2 * I) * Real.exp (-t * unitIntervalCosineEigenvalue n) := by
            ring
  have h₀ :
      Summable fun n : ℕ =>
        unitIntervalCosineHeatPointWeight t 0 n *
          unitIntervalNeumannCosineCoeff f n :=
    Summable.of_norm_bounded hvalue_major hvalue_bound
  exact unitIntervalCosineHeatValue_deriv_of_summable_bound
    (t := t) (x := x) (x₀ := 0)
    (a := unitIntervalNeumannCosineCoeff f)
    (u := fun n : ℕ => B * unitIntervalCosineReciprocalCubeTerm n)
    hu hbound h₀

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

/-! ## L² cosine totality on the unit interval -/

/-- Each raw unit-interval cosine mode belongs to the concrete interval
`L²` space. -/
theorem unitIntervalCosine_memLp_two (n : ℕ) :
    MemLp
      (fun x : ℝ => (Real.cos ((n : ℝ) * Real.pi * x) : ℂ))
      (2 : ℝ≥0∞) (intervalMeasure 1) := by
  refine MemLp.of_bound ?_ (1 : ℝ) ?_
  · have hcont :
        Continuous
          (fun x : ℝ => (Real.cos ((n : ℝ) * Real.pi * x) : ℂ)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real]
      simpa [Real.norm_eq_abs] using
        Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)

/-- The raw cosine mode as an element of interval `L²`. -/
def unitIntervalCosineLp (n : ℕ) :
    Lp ℂ 2 (intervalMeasure 1) :=
  MemLp.toLp
    (fun x : ℝ => (Real.cos ((n : ℝ) * Real.pi * x) : ℂ))
    (unitIntervalCosine_memLp_two n)

/-- The `Lp` representative of the raw cosine mode is the pointwise cosine
mode almost everywhere. -/
theorem unitIntervalCosineLp_coeFn (n : ℕ) :
    unitIntervalCosineLp n
      =ᵐ[intervalMeasure 1]
        fun x : ℝ => (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) := by
  exact MemLp.coeFn_toLp (unitIntervalCosine_memLp_two n)

/-- Inner products against the raw `L²` cosine modes are exactly the raw
cosine coefficients used in the Fourier-to-cosine Parseval bridge. -/
theorem unitIntervalCosineLp_inner_eq_coeff
    (n : ℕ) (g : Lp ℂ 2 (intervalMeasure 1)) :
    inner ℂ (unitIntervalCosineLp n) g =
      ∫ x in (0 : ℝ)..1,
        (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * g x := by
  calc
    inner ℂ (unitIntervalCosineLp n) g
        = ∫ x : ℝ, inner ℂ (unitIntervalCosineLp n x) (g x)
            ∂ intervalMeasure 1 := by
          simpa using (L2.inner_def (unitIntervalCosineLp n) g)
    _ = ∫ x : ℝ,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * g x
            ∂ intervalMeasure 1 := by
          apply integral_congr_ae
          filter_upwards [unitIntervalCosineLp_coeFn n] with x hx
          rw [hx]
          rw [RCLike.inner_apply']
          have hstar :
              (starRingEnd ℂ)
                  ((Real.cos ((n : ℝ) * Real.pi * x) : ℂ)) =
                (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) := by
            simpa using
              Complex.conj_ofReal ((Real.cos ((n : ℝ) * Real.pi * x)))
          rw [hstar]
    _ = ∫ x : ℝ,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * g x
            ∂ volume.restrict (Set.Ioc (0 : ℝ) 1) := by
          rw [unitIntervalIocMeasure_eq_intervalMeasure]
    _ = ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * g x := by
          rw [intervalIntegral.integral_of_le
            (show (0 : ℝ) ≤ 1 by norm_num)]

/-- The raw cosine modes are total in interval `L²`: their closed linear span
has trivial orthogonal complement. -/
theorem unitIntervalCosineLp_span_orthogonal_eq_bot :
    (Submodule.span ℂ
      (Set.range unitIntervalCosineLp :
        Set (Lp ℂ 2 (intervalMeasure 1))))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  have hg_mem : MemLp (fun x : ℝ => g x) (2 : ℝ≥0∞) (intervalMeasure 1) :=
    Lp.memLp g
  have hcoeff :
      ∀ n : ℕ,
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * g x = 0 := by
    intro n
    have hcos_mem :
        unitIntervalCosineLp n ∈
          Submodule.span ℂ
            (Set.range unitIntervalCosineLp :
              Set (Lp ℂ 2 (intervalMeasure 1))) :=
      Submodule.subset_span (Set.mem_range_self n)
    have hinner :
        inner ℂ (unitIntervalCosineLp n) g = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (K := Submodule.span ℂ
          (Set.range unitIntervalCosineLp :
            Set (Lp ℂ 2 (intervalMeasure 1))))
        hcos_mem hg
    simpa [unitIntervalCosineLp_inner_eq_coeff n g] using hinner
  have hae :
      (fun x : ℝ => g x)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 :=
    unitIntervalCosine_nat_total_ae_zero
      (f := fun x : ℝ => g x)
      (unitInterval_memLp_two_intervalIntegrable hg_mem)
      (unitIntervalEvenReflection_memLp_two hg_mem)
      (unitInterval_memLp_two_norm_sq_intervalIntegrable hg_mem)
      hcoeff
  rw [unitIntervalIocMeasure_eq_intervalMeasure] at hae
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr hae

/-- Inner products of raw interval `L²` cosine modes are the corresponding
complex interval integrals. -/
theorem unitIntervalCosineLp_inner_eq_integral (m n : ℕ) :
    inner ℂ (unitIntervalCosineLp m) (unitIntervalCosineLp n) =
      ∫ x in (0 : ℝ)..1,
        (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) := by
  rw [unitIntervalCosineLp_inner_eq_coeff]
  apply intervalIntegral.integral_congr_ae_restrict
  have hcoe := unitIntervalCosineLp_coeFn n
  have hle :
      volume.restrict (Set.uIoc (0 : ℝ) 1) ≤ intervalMeasure 1 := by
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    unfold intervalMeasure intervalSet
    exact Measure.restrict_mono (by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩) le_rfl
  have hcoeI :
      (fun x : ℝ => unitIntervalCosineLp n x)
        =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) 1)]
          fun x : ℝ => (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) := by
    exact ae_mono hle hcoe
  filter_upwards [hcoeI] with x hx
  rw [hx]

/-- The complex cosine-product integral is the complexification of the real
cosine-product integral from `CosineSpectrum`. -/
theorem unitIntervalCosine_complex_integral_eq_real (m n : ℕ) :
    (∫ x in (0 : ℝ)..1,
        (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ)) =
      ((∫ x in (0 : ℝ)..1,
            ShenWork.CosineSpectrum.cosineMode m x *
            ShenWork.CosineSpectrum.cosineMode n x : ℝ) : ℂ) := by
  calc
    (∫ x in (0 : ℝ)..1,
        (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) *
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ))
        = ∫ x in (0 : ℝ)..1,
            ((ShenWork.CosineSpectrum.cosineMode m x *
              ShenWork.CosineSpectrum.cosineMode n x : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          simp [ShenWork.CosineSpectrum.cosineMode]
    _ = ((∫ x in (0 : ℝ)..1,
          ShenWork.CosineSpectrum.cosineMode m x *
            ShenWork.CosineSpectrum.cosineMode n x : ℝ) : ℂ) := by
          simpa using
            (intervalIntegral.integral_ofReal
              (a := (0 : ℝ)) (b := 1) (μ := volume)
              (f := fun x : ℝ =>
                ShenWork.CosineSpectrum.cosineMode m x *
                  ShenWork.CosineSpectrum.cosineMode n x))

theorem unitIntervalCosineLp_inner_eq_zero_of_ne {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (unitIntervalCosineLp m) (unitIntervalCosineLp n) = 0 := by
  rw [unitIntervalCosineLp_inner_eq_integral,
    unitIntervalCosine_complex_integral_eq_real,
    ShenWork.CosineSpectrum.cosineMode_orthogonal hmn]
  norm_num

theorem unitIntervalCosineLp_inner_self_zero :
    inner ℂ (unitIntervalCosineLp 0) (unitIntervalCosineLp 0) = 1 := by
  rw [unitIntervalCosineLp_inner_eq_integral,
    unitIntervalCosine_complex_integral_eq_real,
    ShenWork.CosineSpectrum.cosineMode_self_integral_zero]
  norm_num

theorem unitIntervalCosineLp_inner_self_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    inner ℂ (unitIntervalCosineLp n) (unitIntervalCosineLp n) = 1 / 2 := by
  rw [unitIntervalCosineLp_inner_eq_integral,
    unitIntervalCosine_complex_integral_eq_real,
    ShenWork.CosineSpectrum.cosineMode_self_integral_of_ne_zero hn]
  norm_num

/-- The normalized Neumann cosine modes in interval `L²`: constant mode
`1`, and positive modes `sqrt 2 * cos(nπx)`. -/
def unitIntervalNormalizedCosineLp (n : ℕ) :
    Lp ℂ 2 (intervalMeasure 1) :=
  if n = 0 then unitIntervalCosineLp 0
  else (Real.sqrt 2 : ℂ) • unitIntervalCosineLp n

theorem unitIntervalNormalizedCosineLp_orthonormal :
    Orthonormal ℂ unitIntervalNormalizedCosineLp := by
  classical
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    by_cases hm0 : m = 0
    · subst m
      simpa [unitIntervalNormalizedCosineLp] using
        unitIntervalCosineLp_inner_self_zero
    · have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← sq]
        exact Real.sq_sqrt (by norm_num)
      have hsqrt_star :
          (starRingEnd ℂ) (Real.sqrt 2 : ℂ) =
            (Real.sqrt 2 : ℂ) := by
        simpa using Complex.conj_ofReal (Real.sqrt 2)
      have hsqrt_sq_complex :
          (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
        norm_num [← Complex.ofReal_mul, hsqrt_sq]
      have hnorm :
          unitIntervalNormalizedCosineLp m =
            (Real.sqrt 2 : ℂ) • unitIntervalCosineLp m := by
        simp [unitIntervalNormalizedCosineLp, hm0]
      have hinner_norm :
          inner ℂ (unitIntervalNormalizedCosineLp m)
              (unitIntervalNormalizedCosineLp m) = 1 := by
        calc
          inner ℂ (unitIntervalNormalizedCosineLp m)
              (unitIntervalNormalizedCosineLp m)
              = (Real.sqrt 2 : ℂ) *
                  ((Real.sqrt 2 : ℂ) * (1 / 2 : ℂ)) := by
                rw [hnorm, inner_smul_left, inner_smul_right, hsqrt_star,
                  unitIntervalCosineLp_inner_self_of_ne_zero hm0]
          _ = (1 : ℂ) := by
                rw [← mul_assoc, hsqrt_sq_complex]
                norm_num
      simpa using hinner_norm
  · have hraw :
        inner ℂ (unitIntervalCosineLp m) (unitIntervalCosineLp n) = 0 :=
      unitIntervalCosineLp_inner_eq_zero_of_ne hmn
    by_cases hm0 : m = 0
    · subst m
      have hn0 : n ≠ 0 := by
        intro hn
        exact hmn hn.symm
      have hnormn :
          unitIntervalNormalizedCosineLp n =
            (Real.sqrt 2 : ℂ) • unitIntervalCosineLp n := by
        simp [unitIntervalNormalizedCosineLp, hn0]
      have hnorm0 :
          unitIntervalNormalizedCosineLp 0 = unitIntervalCosineLp 0 := by
        simp [unitIntervalNormalizedCosineLp]
      rw [hnorm0, hnormn, inner_smul_right, hraw]
      simpa [hmn]
    · by_cases hn0 : n = 0
      · subst n
        have hnormm :
            unitIntervalNormalizedCosineLp m =
              (Real.sqrt 2 : ℂ) • unitIntervalCosineLp m := by
          simp [unitIntervalNormalizedCosineLp, hm0]
        have hnorm0 :
            unitIntervalNormalizedCosineLp 0 = unitIntervalCosineLp 0 := by
          simp [unitIntervalNormalizedCosineLp]
        rw [hnormm, hnorm0, inner_smul_left, hraw]
        simpa [hmn]
      · have hnormm :
            unitIntervalNormalizedCosineLp m =
              (Real.sqrt 2 : ℂ) • unitIntervalCosineLp m := by
          simp [unitIntervalNormalizedCosineLp, hm0]
        have hnormn :
            unitIntervalNormalizedCosineLp n =
              (Real.sqrt 2 : ℂ) • unitIntervalCosineLp n := by
          simp [unitIntervalNormalizedCosineLp, hn0]
        rw [hnormm, hnormn, inner_smul_left, inner_smul_right, hraw]
        simpa [hmn]

/-- The normalized cosine modes are complete in interval `L²`. -/
theorem unitIntervalNormalizedCosineLp_span_orthogonal_eq_bot :
    (Submodule.span ℂ
      (Set.range unitIntervalNormalizedCosineLp :
        Set (Lp ℂ 2 (intervalMeasure 1))))ᗮ = ⊥ := by
  let rawSpan : Submodule ℂ (Lp ℂ 2 (intervalMeasure 1)) :=
    Submodule.span ℂ
      (Set.range unitIntervalCosineLp :
        Set (Lp ℂ 2 (intervalMeasure 1)))
  let normSpan : Submodule ℂ (Lp ℂ 2 (intervalMeasure 1)) :=
    Submodule.span ℂ
      (Set.range unitIntervalNormalizedCosineLp :
        Set (Lp ℂ 2 (intervalMeasure 1)))
  have hle : rawSpan ≤ normSpan := by
    refine Submodule.span_le.mpr ?_
    intro v hv
    rcases hv with ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst n
      have hnorm : unitIntervalNormalizedCosineLp 0 = unitIntervalCosineLp 0 := by
        simp [unitIntervalNormalizedCosineLp]
      rw [← hnorm]
      exact Submodule.subset_span (Set.mem_range_self 0)
    · have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
        exact_mod_cast
          (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
      have hnorm :
          unitIntervalNormalizedCosineLp n =
            (Real.sqrt 2 : ℂ) • unitIntervalCosineLp n := by
        simp [unitIntervalNormalizedCosineLp, hn]
      have hmem :
          unitIntervalNormalizedCosineLp n ∈ normSpan :=
        Submodule.subset_span (Set.mem_range_self n)
      have heq :
          unitIntervalCosineLp n =
            ((Real.sqrt 2 : ℂ)⁻¹) • unitIntervalNormalizedCosineLp n := by
        calc
          unitIntervalCosineLp n =
              (1 : ℂ) • unitIntervalCosineLp n := by simp
          _ = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) •
                unitIntervalCosineLp n := by
              rw [inv_mul_cancel₀ hsqrt_ne]
          _ = ((Real.sqrt 2 : ℂ)⁻¹) •
                ((Real.sqrt 2 : ℂ) • unitIntervalCosineLp n) := by
              rw [smul_smul]
          _ = ((Real.sqrt 2 : ℂ)⁻¹) • unitIntervalNormalizedCosineLp n := by
              rw [← hnorm]
      rw [heq]
      exact Submodule.smul_mem normSpan _ hmem
  apply le_antisymm
  · rw [← unitIntervalCosineLp_span_orthogonal_eq_bot]
    exact Submodule.orthogonal_le hle
  · exact bot_le

/-- The complete Hilbert basis of interval `L²` formed by the normalized
Neumann cosine modes. -/
def unitIntervalCosineHilbertBasis :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (intervalMeasure 1)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    unitIntervalNormalizedCosineLp_orthonormal
    unitIntervalNormalizedCosineLp_span_orthogonal_eq_bot

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

/-! ## Absolute-convergence `L¹ → Lq` endpoint for the spectral gradient -/

/-- On the unit interval, the interval integral of the norm is the Mathlib
`L¹` seminorm. -/
theorem unitInterval_integral_norm_eq_lpNorm_one
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
    (∫ x in (0 : ℝ)..1, ‖f x‖) =
      lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) := by
  rw [← unitIntervalIocMeasure_eq_intervalMeasure]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [lpNorm_one_eq_integral_norm]
  simpa using hf.aestronglyMeasurable

/-- Unit-interval `L^p`, `1 ≤ p < ∞`, gives interval integrability. -/
theorem unitInterval_memLp_ofReal_intervalIntegrable
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    IntervalIntegrable f volume 0 1 := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)]
  change Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1))
  rw [unitIntervalIocMeasure_eq_intervalMeasure]
  exact hf_mem.integrable hp1

/-- On the unit interval, `L^p` controls `L¹` for `1 ≤ p < ∞`. -/
theorem unitInterval_lpNorm_one_le_lpNorm_of_one_le
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) ≤
      lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hle :
      eLpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) ≤
        eLpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
    have hbase :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := intervalMeasure 1) (f := f) hp1
        hf_mem.aestronglyMeasurable
    simpa [unitIntervalMeasure_univ] using hbase
  have hreal := ENNReal.toReal_mono hf_mem.eLpNorm_ne_top hle
  simpa [toReal_eLpNorm hf_mem.aestronglyMeasurable] using hreal

/-- Complexifying a real function preserves its Mathlib `LpSeminorm`, under
the corresponding `MemLp` hypothesis. -/
theorem unitInterval_lpNorm_complex_ofReal_eq
    {p : ℝ≥0∞} {f : ℝ → ℝ}
    (hf_mem : MemLp f p (intervalMeasure 1)) :
    lpNorm (fun x => (f x : ℂ)) p (intervalMeasure 1) =
      lpNorm f p (intervalMeasure 1) := by
  have hfc_mem : MemLp (fun x => (f x : ℂ)) p (intervalMeasure 1) :=
    hf_mem.ofReal
  calc
    lpNorm (fun x => (f x : ℂ)) p (intervalMeasure 1)
        = (eLpNorm (fun x => (f x : ℂ)) p (intervalMeasure 1)).toReal := by
          exact (toReal_eLpNorm hfc_mem.aestronglyMeasurable).symm
    _ = (eLpNorm f p (intervalMeasure 1)).toReal := by
          congr 1
          exact eLpNorm_congr_norm_ae
            (Filter.Eventually.of_forall fun x => by simp)
    _ = lpNorm f p (intervalMeasure 1) :=
          toReal_eLpNorm hf_mem.aestronglyMeasurable

/-- On the unit interval, a pointwise norm bound controls the Mathlib
`L∞` seminorm. -/
theorem unitInterval_lpNorm_top_le_of_forall_norm_le
    {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) :
    lpNorm g ∞ (intervalMeasure 1) ≤ C := by
  by_cases hg : AEStronglyMeasurable g (intervalMeasure 1)
  · have hess :
        eLpNormEssSup g (intervalMeasure 1) ≤ ENNReal.ofReal C :=
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hbound)
    calc
      lpNorm g ∞ (intervalMeasure 1)
          = (eLpNorm g ∞ (intervalMeasure 1)).toReal := by
            exact (toReal_eLpNorm hg).symm
      _ = (eLpNormEssSup g (intervalMeasure 1)).toReal := by
            rw [eLpNorm_exponent_top]
      _ ≤ (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
      _ = C := ENNReal.toReal_ofReal hC
  · simp [lpNorm, hg, hC]

/-- Unit-interval spectral Neumann heat-gradient estimate from `L¹` to
`L∞`, in Mathlib `LpSeminorm` form. -/
theorem unitIntervalNeumannSpectralHeatGradient_L1_Linfty_lpNorm_bound
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        ∞ (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) := by
  let C : ℝ :=
    (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
      lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1)
  have hfactor_nonneg :
      0 ≤ unitIntervalCosineGradientL1LinftyConstant / t ^ 2 := by
    exact div_nonneg unitIntervalCosineGradientL1LinftyConstant_nonneg
      (sq_nonneg t)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hfactor_nonneg lpNorm_nonneg
  have hpoint :
      ∀ x,
        ‖unitIntervalCosineHeatGradientValue t
          (unitIntervalNeumannCosineCoeff f) x‖ ≤ C := by
    intro x
    have h :=
      unitIntervalNeumannSpectralHeatGradient_L1_Linfty_pointwise_bound
        (t := t) ht (f := f) hf x
    simpa [C, Real.norm_eq_abs,
      unitInterval_integral_norm_eq_lpNorm_one hf] using h
  exact unitInterval_lpNorm_top_le_of_forall_norm_le hC_nonneg hpoint

/-- Unit-interval spectral Neumann heat-gradient estimate from `L¹` to finite
`L^q`, in Mathlib `LpSeminorm` form. -/
theorem unitIntervalNeumannSpectralHeatGradient_L1_Lq_lpNorm_bound
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
    lpNorm
        (fun x =>
          unitIntervalCosineHeatGradientValue t
            (unitIntervalNeumannCosineCoeff f) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) := by
  let C : ℝ :=
    (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
      lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1)
  have hfactor_nonneg :
      0 ≤ unitIntervalCosineGradientL1LinftyConstant / t ^ 2 := by
    exact div_nonneg unitIntervalCosineGradientL1LinftyConstant_nonneg
      (sq_nonneg t)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hfactor_nonneg lpNorm_nonneg
  have hpoint :
      ∀ x,
        ‖unitIntervalCosineHeatGradientValue t
          (unitIntervalNeumannCosineCoeff f) x‖ ≤ C := by
    intro x
    have h :=
      unitIntervalNeumannSpectralHeatGradient_L1_Linfty_pointwise_bound
        (t := t) ht (f := f) hf x
    simpa [C, Real.norm_eq_abs,
      unitInterval_integral_norm_eq_lpNorm_one hf] using h
  exact unitInterval_lpNorm_le_of_forall_norm_le hq hC_nonneg hpoint

/-- Unit-interval spectral Neumann heat semigroup derivative estimate from
`L¹` to finite `L^q`, in Mathlib `LpSeminorm` form. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L1_Lq_lpNorm_bound
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) := by
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
    exact unitIntervalNeumannSpectralHeat_deriv_eq_gradient_of_L1
      (t := t) (x := x) ht (f := f) hf
  rw [hderiv]
  exact unitIntervalNeumannSpectralHeatGradient_L1_Lq_lpNorm_bound
    (t := t) (q := q) ht hq (f := f) hf

/-- Unit-interval spectral Neumann heat semigroup derivative estimate from
`L¹` to `L∞`, in Mathlib `LpSeminorm` form. -/
theorem unitIntervalNeumannSpectralHeat_deriv_L1_Linfty_lpNorm_bound
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        ∞ (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) := by
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
    exact unitIntervalNeumannSpectralHeat_deriv_eq_gradient_of_L1
      (t := t) (x := x) ht (f := f) hf
  rw [hderiv]
  exact unitIntervalNeumannSpectralHeatGradient_L1_Linfty_lpNorm_bound
    (t := t) ht (f := f) hf

/-- Unit-interval spectral Neumann heat semigroup derivative estimate from
finite `L^p`, `1 ≤ p`, to finite `L^q`.  This is an absolute-convergence
endpoint bound with a nonsharp `t⁻²` singularity. -/
theorem unitIntervalNeumannSpectralHeat_deriv_Lp_Lq_lpNorm_bound_from_memLp
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hf_int :=
    unitInterval_memLp_ofReal_intervalIntegrable
      (p := p) hp (f := f) hf_mem
  have hbase :=
    unitIntervalNeumannSpectralHeat_deriv_L1_Lq_lpNorm_bound
      (t := t) (q := q) ht hq (f := f) hf_int
  have hLp :=
    unitInterval_lpNorm_one_le_lpNorm_of_one_le
      (p := p) hp (f := f) hf_mem
  have hfactor_nonneg :
      0 ≤ unitIntervalCosineGradientL1LinftyConstant / t ^ 2 := by
    exact div_nonneg unitIntervalCosineGradientL1LinftyConstant_nonneg
      (sq_nonneg t)
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hLp hfactor_nonneg)

/-- Unit-interval spectral Neumann heat semigroup derivative estimate from
finite `L^p`, `1 ≤ p`, to `L∞`.  This is the `q = ∞` companion to
`unitIntervalNeumannSpectralHeat_deriv_Lp_Lq_lpNorm_bound_from_memLp`. -/
theorem unitIntervalNeumannSpectralHeat_deriv_Lp_Linfty_lpNorm_bound_from_memLp
    {t p : ℝ} (ht : 0 < t) (hp : 1 ≤ p)
    {f : ℝ → ℂ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalCosineHeatValue t
                (unitIntervalNeumannCosineCoeff f) z) x)
        ∞ (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hf_int :=
    unitInterval_memLp_ofReal_intervalIntegrable
      (p := p) hp (f := f) hf_mem
  have hbase :=
    unitIntervalNeumannSpectralHeat_deriv_L1_Linfty_lpNorm_bound
      (t := t) ht (f := f) hf_int
  have hLp :=
    unitInterval_lpNorm_one_le_lpNorm_of_one_le
      (p := p) hp (f := f) hf_mem
  have hfactor_nonneg :
      0 ≤ unitIntervalCosineGradientL1LinftyConstant / t ^ 2 := by
    exact div_nonneg unitIntervalCosineGradientL1LinftyConstant_nonneg
      (sq_nonneg t)
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hLp hfactor_nonneg)

/-! ## Real-valued spectral Neumann heat semigroup wrappers -/

/-- The unit-interval Neumann heat semigroup defined by the cosine spectral
series.  This is the spectral semigroup model, not the zeroth-reflection
helper operator from `IntervalDomain.lean`. -/
def unitIntervalNeumannHeatSemigroup
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  unitIntervalCosineHeatValue t
    (unitIntervalNeumannCosineCoeff (fun y => (f y : ℂ))) x

/-- Real-valued unit-interval spectral Neumann heat-gradient estimate from
finite `L^p`, `1 ≤ p`, to finite `L^q`.  This is the current proved spectral
endpoint with nonsharp `t⁻²` singularity. -/
theorem unitIntervalNeumannHeatSemigroup_grad_Lp_Lq_bound
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {f : ℝ → ℝ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalNeumannHeatSemigroup t f z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hfc_mem :
      MemLp (fun x => (f x : ℂ)) (ENNReal.ofReal p)
        (intervalMeasure 1) :=
    hf_mem.ofReal
  have hbase :=
    unitIntervalNeumannSpectralHeat_deriv_Lp_Lq_lpNorm_bound_from_memLp
      (t := t) (p := p) (q := q) ht hp hq
      (f := fun x => (f x : ℂ)) hfc_mem
  simpa [unitIntervalNeumannHeatSemigroup,
    unitInterval_lpNorm_complex_ofReal_eq hf_mem] using hbase

/-- Real-valued unit-interval spectral Neumann heat-gradient estimate from
finite `L^p`, `1 ≤ p`, to `L∞`.  This is the `q = ∞` companion to
`unitIntervalNeumannHeatSemigroup_grad_Lp_Lq_bound`. -/
theorem unitIntervalNeumannHeatSemigroup_grad_Lp_Linfty_bound
    {t p : ℝ} (ht : 0 < t) (hp : 1 ≤ p)
    {f : ℝ → ℝ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              unitIntervalNeumannHeatSemigroup t f z) x)
        ∞ (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hfc_mem :
      MemLp (fun x => (f x : ℂ)) (ENNReal.ofReal p)
        (intervalMeasure 1) :=
    hf_mem.ofReal
  have hbase :=
    unitIntervalNeumannSpectralHeat_deriv_Lp_Linfty_lpNorm_bound_from_memLp
      (t := t) (p := p) ht hp
      (f := fun x => (f x : ℂ)) hfc_mem
  simpa [unitIntervalNeumannHeatSemigroup,
    unitInterval_lpNorm_complex_ofReal_eq hf_mem] using hbase

/-- The interval Neumann heat semigroup on `[0,L]` obtained by scaling the
unit-interval spectral Neumann semigroup.  For `L > 0`, this is the cosine
spectral model with eigenvalues `(nπ/L)^2`. -/
def intervalHeatSemigroup
    (L t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  unitIntervalNeumannHeatSemigroup (t / L ^ 2) (fun y => f (L * y))
    ((1 / L) * x)

theorem intervalHeatSemigroup_one (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalHeatSemigroup 1 t f x =
      unitIntervalNeumannHeatSemigroup t f x := by
  simp [intervalHeatSemigroup]

/-- Derivatives of the scaled interval spectral semigroup reduce to the
unit-interval derivative with the expected `1/L` factor. -/
theorem intervalHeatSemigroup_deriv_eq_scaled_unit
    (L t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun z : ℝ => intervalHeatSemigroup L t f z) x =
      (1 / L) *
        deriv
          (fun y : ℝ =>
            unitIntervalNeumannHeatSemigroup (t / L ^ 2)
              (fun u => f (L * u)) y)
          ((1 / L) * x) := by
  simpa [intervalHeatSemigroup, smul_eq_mul] using
    (deriv_comp_mul_left (c := 1 / L)
      (f := fun y : ℝ =>
        unitIntervalNeumannHeatSemigroup (t / L ^ 2)
          (fun u => f (L * u)) y)
      (x := x))

/-- The scaled interval spectral semigroup has the already-proved unit
gradient estimate when `L = 1`. -/
theorem intervalHeatSemigroup_unit_grad_Lp_Lq_bound
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {f : ℝ → ℝ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv
            (fun z =>
              intervalHeatSemigroup 1 t f z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  simpa [intervalHeatSemigroup_one] using
    unitIntervalNeumannHeatSemigroup_grad_Lp_Lq_bound
      (t := t) (p := p) (q := q) ht hp hq (f := f) hf_mem

/-! ## Zeroth-reflection helper-operator gradient bounds -/

/-- Full-line `L¹ → L∞` heat-gradient factor used by the helper-operator
bound below. -/
def heatGradientL1LinftyFactor (t : ℝ) : ℝ :=
  ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
    (Real.sqrt (1 / (4 * t)))⁻¹

theorem heatGradientL1LinftyFactor_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ heatGradientL1LinftyFactor t := by
  dsimp [heatGradientL1LinftyFactor]
  positivity

/-- A translated heat-kernel term times an interval-integrable input is
integrable against the interval measure. -/
lemma interval_heatKernel_sub_mul_integrable
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    Integrable (fun y => heatKernel t (x - y) * f y)
      (intervalMeasure L) := by
  have hkernel_meas :
      AEStronglyMeasurable (fun y : ℝ => heatKernel t (x - y))
        (intervalMeasure L) := by
    have hcont : Continuous (fun y : ℝ => heatKernel t (x - y)) := by
      unfold heatKernel
      fun_prop
    exact hcont.aestronglyMeasurable
  have hkernel_bound :
      ∀ y : ℝ, ‖heatKernel t (x - y)‖ ≤
        1 / Real.sqrt (4 * Real.pi * t) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht (x - y))]
    exact _root_.heatKernel_pointwise_bound ht (x - y)
  simpa [mul_comm] using
    hf_int.mul_bdd hkernel_meas
      (Filter.Eventually.of_forall hkernel_bound)

/-- A reflected translated heat-kernel term times an interval-integrable input
is integrable against the interval measure. -/
lemma interval_heatKernel_add_mul_integrable
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    Integrable (fun y => heatKernel t (x + y) * f y)
      (intervalMeasure L) := by
  have hkernel_meas :
      AEStronglyMeasurable (fun y : ℝ => heatKernel t (x + y))
        (intervalMeasure L) := by
    have hcont : Continuous (fun y : ℝ => heatKernel t (x + y)) := by
      unfold heatKernel
      fun_prop
    exact hcont.aestronglyMeasurable
  have hkernel_bound :
      ∀ y : ℝ, ‖heatKernel t (x + y)‖ ≤
        1 / Real.sqrt (4 * Real.pi * t) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht (x + y))]
    exact _root_.heatKernel_pointwise_bound ht (x + y)
  simpa [mul_comm] using
    hf_int.mul_bdd hkernel_meas
      (Filter.Eventually.of_forall hkernel_bound)

/-- Zero extension from `[0,L]` is integrable on the line when the original
function is integrable against `intervalMeasure L`. -/
lemma interval_indicator_integrable_of_integrable
    {L : ℝ} {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) :
    Integrable (Set.indicator (intervalSet L) f) volume := by
  have hf_on : IntegrableOn f (intervalSet L) volume := by
    simpa [IntegrableOn, intervalMeasure] using hf_int
  exact hf_on.integrable_indicator
    (show MeasurableSet (intervalSet L) by simp [intervalSet])

/-- The `L¹` mass of the zero extension is the interval `L¹` mass. -/
theorem interval_indicator_abs_integral_eq
    (L : ℝ) (f : ℝ → ℝ) :
    (∫ y : ℝ, |Set.indicator (intervalSet L) f y|) =
      ∫ y, |f y| ∂ intervalMeasure L := by
  rw [intervalMeasure]
  have hfun :
      (fun y : ℝ => |Set.indicator (intervalSet L) f y|) =
        Set.indicator (intervalSet L) (fun y : ℝ => |f y|) := by
    funext y
    by_cases hy : y ∈ intervalSet L
    · simp [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp
  rw [hfun]
  rw [MeasureTheory.integral_indicator
    (show MeasurableSet (intervalSet L) by simp [intervalSet])]

/-- The restricted zeroth-reflection helper operator is the average of two
full-line heat semigroups applied to the zero extension. -/
theorem intervalSemigroupOperator_eq_half_heatSemigroup_add_reflected
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    intervalSemigroupOperator L t f x =
      (1 / 2) * heatSemigroup t (Set.indicator (intervalSet L) f) x +
        (1 / 2) * heatSemigroup t (Set.indicator (intervalSet L) f) (-x) := by
  have hleft_int :=
    interval_heatKernel_sub_mul_integrable
      (L := L) (t := t) ht hf_int x
  have hright_int :=
    interval_heatKernel_add_mul_integrable
      (L := L) (t := t) ht hf_int x
  have hleft_rhs :
      (∫ y : ℝ,
          heatKernel t (x - y) * Set.indicator (intervalSet L) f y) =
        ∫ y, heatKernel t (x - y) * f y ∂ intervalMeasure L := by
    rw [intervalMeasure]
    have hfun :
        (fun y : ℝ =>
            heatKernel t (x - y) * Set.indicator (intervalSet L) f y) =
          Set.indicator (intervalSet L)
            (fun y : ℝ => heatKernel t (x - y) * f y) := by
      funext y
      by_cases hy : y ∈ intervalSet L
      · simp [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
        ring
    rw [hfun]
    rw [MeasureTheory.integral_indicator
      (show MeasurableSet (intervalSet L) by simp [intervalSet])]
  have hright_rhs :
      (∫ y : ℝ,
          heatKernel t (-x - y) * Set.indicator (intervalSet L) f y) =
        ∫ y, heatKernel t (x + y) * f y ∂ intervalMeasure L := by
    rw [intervalMeasure]
    have hfun :
        (fun y : ℝ =>
            heatKernel t (-x - y) * Set.indicator (intervalSet L) f y) =
          Set.indicator (intervalSet L)
            (fun y : ℝ => heatKernel t (x + y) * f y) := by
      funext y
      by_cases hy : y ∈ intervalSet L
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        rw [show -x - y = -(x + y) by ring, heatKernel_neg]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
        ring
    rw [hfun]
    rw [MeasureTheory.integral_indicator
      (show MeasurableSet (intervalSet L) by simp [intervalSet])]
  unfold intervalSemigroupOperator normalizedZerothReflectionKernel
    neumannHeatKernel_zerothReflection heatSemigroup
  rw [hleft_rhs, hright_rhs]
  calc
    ∫ y,
        1 / 2 * (heatKernel t (x - y) + heatKernel t (x + y)) * f y
        ∂ intervalMeasure L
        =
          ∫ y,
            ((1 / 2) * (heatKernel t (x - y) * f y) +
              (1 / 2) * (heatKernel t (x + y) * f y))
            ∂ intervalMeasure L := by
          congr 1
          ext y
          ring
    _ =
          ∫ y, (1 / 2) * (heatKernel t (x - y) * f y)
            ∂ intervalMeasure L +
          ∫ y, (1 / 2) * (heatKernel t (x + y) * f y)
            ∂ intervalMeasure L := by
          rw [MeasureTheory.integral_add
            (hleft_int.const_mul (1 / 2))
            (hright_int.const_mul (1 / 2))]
    _ =
          (1 / 2) *
            ∫ y, heatKernel t (x - y) * f y ∂ intervalMeasure L +
          (1 / 2) *
            ∫ y, heatKernel t (x + y) * f y ∂ intervalMeasure L := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]

/-- Derivative algebra for the averaged full-line representation. -/
lemma deriv_half_heatSemigroup_add_reflected
    {t x : ℝ} (ht : 0 < t) {g : ℝ → ℝ} (hg : Integrable g) :
    deriv
        (fun z : ℝ =>
          (1 / 2 : ℝ) * heatSemigroup t g z +
            (1 / 2 : ℝ) * heatSemigroup t g (-z)) x =
      (1 / 2 : ℝ) * deriv (fun z : ℝ => heatSemigroup t g z) x -
        (1 / 2 : ℝ) * deriv (fun z : ℝ => heatSemigroup t g z) (-x) := by
  have h1 := (heatSemigroup_hasDerivAt (f := g) ht x hg).const_mul
    (1 / 2 : ℝ)
  have h2 :=
    ((heatSemigroup_hasDerivAt (f := g) ht (-x) hg).comp x
      (hasDerivAt_neg x)).const_mul (1 / 2 : ℝ)
  have h := (h1.add h2).deriv
  rw [deriv_heatSemigroup (f := g) ht x hg,
    deriv_heatSemigroup (f := g) ht (-x) hg]
  simpa [sub_eq_add_neg, mul_neg] using h

/-- Pointwise `L¹ → L∞` gradient smoothing for the restricted
zeroth-reflection helper operator. -/
theorem intervalSemigroupOperator_deriv_L1_Linfty_pointwise
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    |deriv (fun z : ℝ => intervalSemigroupOperator L t f z) x| ≤
      heatGradientL1LinftyFactor t *
        ∫ y, |f y| ∂ intervalMeasure L := by
  let g : ℝ → ℝ := Set.indicator (intervalSet L) f
  have hg_int : Integrable g volume :=
    interval_indicator_integrable_of_integrable (L := L) (f := f) hf_int
  have hrepr :
      (fun z : ℝ => intervalSemigroupOperator L t f z) =
        fun z : ℝ =>
          (1 / 2 : ℝ) * heatSemigroup t g z +
            (1 / 2 : ℝ) * heatSemigroup t g (-z) := by
    funext z
    exact intervalSemigroupOperator_eq_half_heatSemigroup_add_reflected
      (L := L) (t := t) ht (f := f) hf_int z
  have hderiv :
      deriv (fun z : ℝ => intervalSemigroupOperator L t f z) x =
        (1 / 2 : ℝ) * deriv (fun z : ℝ => heatSemigroup t g z) x -
          (1 / 2 : ℝ) * deriv (fun z : ℝ => heatSemigroup t g z) (-x) := by
    rw [hrepr]
    exact deriv_half_heatSemigroup_add_reflected (t := t) (x := x) ht hg_int
  have hD1 :=
    deriv_heatSemigroup_L1_Linfty_smoothing_abs
      (f := g) (t := t) ht x hg_int
  have hD2 :=
    deriv_heatSemigroup_L1_Linfty_smoothing_abs
      (f := g) (t := t) ht (-x) hg_int
  let Ig : ℝ := ∫ y : ℝ, |g y|
  have hIg_nonneg : 0 ≤ Ig := by
    dsimp [Ig]
    exact integral_nonneg fun y => abs_nonneg (g y)
  have hC_nonneg : 0 ≤ heatGradientL1LinftyFactor t :=
    heatGradientL1LinftyFactor_nonneg ht
  have hD1' :
      |deriv (fun z : ℝ => heatSemigroup t g z) x| ≤
        heatGradientL1LinftyFactor t * Ig := by
    simpa [heatGradientL1LinftyFactor, Ig] using hD1
  have hD2' :
      |deriv (fun z : ℝ => heatSemigroup t g z) (-x)| ≤
        heatGradientL1LinftyFactor t * Ig := by
    simpa [heatGradientL1LinftyFactor, Ig] using hD2
  have hIg_eq :
      Ig = ∫ y, |f y| ∂ intervalMeasure L := by
    dsimp [Ig, g]
    exact interval_indicator_abs_integral_eq L f
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  calc
    |deriv (fun z : ℝ => intervalSemigroupOperator L t f z) x|
        =
          |(1 / 2 : ℝ) * deriv (fun z : ℝ => heatSemigroup t g z) x -
            (1 / 2 : ℝ) * deriv (fun z : ℝ => heatSemigroup t g z) (-x)| := by
          rw [hderiv]
    _ ≤
          |(1 / 2 : ℝ) * deriv (fun z : ℝ => heatSemigroup t g z) x| +
            |(1 / 2 : ℝ) *
              deriv (fun z : ℝ => heatSemigroup t g z) (-x)| :=
          abs_sub _ _
    _ =
          (1 / 2 : ℝ) * |deriv (fun z : ℝ => heatSemigroup t g z) x| +
            (1 / 2 : ℝ) *
              |deriv (fun z : ℝ => heatSemigroup t g z) (-x)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hhalf_nonneg]
    _ ≤
          (1 / 2 : ℝ) * (heatGradientL1LinftyFactor t * Ig) +
            (1 / 2 : ℝ) * (heatGradientL1LinftyFactor t * Ig) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hD1' hhalf_nonneg)
            (mul_le_mul_of_nonneg_left hD2' hhalf_nonneg)
    _ =
          heatGradientL1LinftyFactor t * Ig := by ring
    _ =
          heatGradientL1LinftyFactor t *
            ∫ y, |f y| ∂ intervalMeasure L := by
          rw [hIg_eq]

/-- On the unit interval, real `L^p` controls real `L¹` for `1 ≤ p < ∞`. -/
theorem unitInterval_lpNorm_one_le_lpNorm_of_one_le_real
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) ≤
      lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hle :
      eLpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) ≤
        eLpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
    have hbase :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := intervalMeasure 1) (f := f) hp1
        hf_mem.aestronglyMeasurable
    simpa [unitIntervalMeasure_univ] using hbase
  have hreal := ENNReal.toReal_mono hf_mem.eLpNorm_ne_top hle
  simpa [toReal_eLpNorm hf_mem.aestronglyMeasurable] using hreal

/-- Unit-interval `LpSeminorm` form of the helper-operator
`L¹ → L∞` gradient smoothing estimate. -/
theorem unitIntervalSemigroupOperator_grad_L1_Linfty_lpNorm_bound
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x)
        ∞ (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) := by
  let C : ℝ :=
    heatGradientL1LinftyFactor t *
      lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (heatGradientL1LinftyFactor_nonneg ht) lpNorm_nonneg
  have hpoint :
      ∀ x,
        ‖deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x‖ ≤ C := by
    intro x
    have h :=
      intervalSemigroupOperator_deriv_L1_Linfty_pointwise
        (L := 1) (t := t) ht (f := f) hf_int x
    simpa [C, Real.norm_eq_abs,
      lpNorm_one_eq_integral_norm hf_int.aestronglyMeasurable] using h
  exact unitInterval_lpNorm_top_le_of_forall_norm_le hC_nonneg hpoint

/-- Unit-interval `LpSeminorm` form of the helper-operator
`L¹ → L^q` gradient smoothing estimate for finite `q`. -/
theorem unitIntervalSemigroupOperator_grad_L1_Lq_lpNorm_bound
    {t q : ℝ} (ht : 0 < t) (hq : 0 < q) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1) := by
  let C : ℝ :=
    heatGradientL1LinftyFactor t *
      lpNorm f (1 : ℝ≥0∞) (intervalMeasure 1)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (heatGradientL1LinftyFactor_nonneg ht) lpNorm_nonneg
  have hpoint :
      ∀ x,
        ‖deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x‖ ≤ C := by
    intro x
    have h :=
      intervalSemigroupOperator_deriv_L1_Linfty_pointwise
        (L := 1) (t := t) ht (f := f) hf_int x
    simpa [C, Real.norm_eq_abs,
      lpNorm_one_eq_integral_norm hf_int.aestronglyMeasurable] using h
  exact unitInterval_lpNorm_le_of_forall_norm_le hq hC_nonneg hpoint

/-- Unit-interval helper-operator gradient estimate from finite `L^p`,
`1 ≤ p`, to finite `L^q`.  This is for the zeroth-reflection helper operator,
not the spectral Neumann semigroup. -/
theorem unitIntervalSemigroupOperator_grad_Lp_Lq_lpNorm_bound
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {f : ℝ → ℝ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hf_int : Integrable f (intervalMeasure 1) :=
    hf_mem.integrable hp1
  have hbase :=
    unitIntervalSemigroupOperator_grad_L1_Lq_lpNorm_bound
      (t := t) (q := q) ht hq (f := f) hf_int
  have hLp :=
    unitInterval_lpNorm_one_le_lpNorm_of_one_le_real
      (p := p) hp (f := f) hf_mem
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hLp
      (heatGradientL1LinftyFactor_nonneg ht))

/-- Unit-interval helper-operator gradient estimate from finite `L^p`,
`1 ≤ p`, to `L∞`. -/
theorem unitIntervalSemigroupOperator_grad_Lp_Linfty_lpNorm_bound
    {t p : ℝ} (ht : 0 < t) (hp : 1 ≤ p)
    {f : ℝ → ℝ}
    (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x =>
          deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x)
        ∞ (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hf_int : Integrable f (intervalMeasure 1) :=
    hf_mem.integrable hp1
  have hbase :=
    unitIntervalSemigroupOperator_grad_L1_Linfty_lpNorm_bound
      (t := t) ht (f := f) hf_int
  have hLp :=
    unitInterval_lpNorm_one_le_lpNorm_of_one_le_real
      (p := p) hp (f := f) hf_mem
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hLp
      (heatGradientL1LinftyFactor_nonneg ht))

end ShenWork.HeatKernelGradientEstimates
