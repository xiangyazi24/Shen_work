/-
  Phase-0 atom (R2′ gate, DESIGN_F2_CONSENSUS.md): QUANTITATIVE cosine
  coefficient decay for weak-H²ₙ sources.

  `intervalWeakH2Neumann_cosineCoeff_quadratic_decay` exposes its constant
  only existentially (`∃ C`), which is useless for the n-UNIFORM iterate
  bounds the R2′ induction needs (the constant must be tracked explicitly
  through the Picard iteration).  This file restates it with the constant
  `2·B` exposed, where `B` is any explicit bound on `∫₀¹ |f''|`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalMildSourceDecayHelper

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.IntervalSourceDecayQuantitative

open ShenWork.PDE.IntervalMildSourceDecayHelper

/-- Quantitative weak-Laplacian coefficient bound: for every mode `k`,
`|∫₀¹ cos(kπx)·f''(x) dx| ≤ B` whenever `∫₀¹ |f''| ≤ B`. -/
theorem weak_laplacianCoeff_abs_le_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {B : ℝ}
    (hB : (∫ x in (0:ℝ)..1, |hf.secondDeriv x|) ≤ B) (k : ℕ) :
    |∫ x in (0:ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x| ≤ B := by
  have hsecond_abs_int : IntervalIntegrable
      (fun x => |hf.secondDeriv x|) volume (0:ℝ) 1 := by
    simpa [Real.norm_eq_abs] using hf.second_intervalIntegrable.norm
  have hcos_cont :
      ContinuousOn (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x))
        (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hmul_int : IntervalIntegrable
      (fun x => Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x)
      volume (0:ℝ) 1 :=
    hf.second_intervalIntegrable.continuousOn_mul hcos_cont
  have hmul_abs_int : IntervalIntegrable
      (fun x => |Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x|)
      volume (0:ℝ) 1 := by
    simpa [Real.norm_eq_abs] using hmul_int.norm
  calc
    |∫ x in (0:ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x|
        ≤ ∫ x in (0:ℝ)..1,
            |Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x| :=
          intervalIntegral.abs_integral_le_integral_abs
            (by norm_num : (0:ℝ) ≤ 1)
    _ ≤ ∫ x in (0:ℝ)..1, |hf.secondDeriv x| := by
        refine intervalIntegral.integral_mono_on
          (by norm_num : (0:ℝ) ≤ 1) hmul_abs_int hsecond_abs_int ?_
        intro x _hx
        rw [abs_mul]
        calc |Real.cos ((k : ℝ) * Real.pi * x)| * |hf.secondDeriv x|
            ≤ 1 * |hf.secondDeriv x| :=
              mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
                (abs_nonneg _)
          _ = |hf.secondDeriv x| := one_mul _
    _ ≤ B := hB

/-- **Quantitative weak-H²ₙ cosine coefficient decay.**  If `∫₀¹|f''| ≤ B`
then `|f̂ₖ| ≤ 2B/(kπ)²` for every `k ≥ 1` — the constant is `2B`, explicit,
ready to be tracked n-uniformly through the Picard iteration. -/
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {B : ℝ}
    (hB : (∫ x in (0:ℝ)..1, |hf.secondDeriv x|) ≤ B) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2 := by
  intro k hk
  have hk_ne : k ≠ 0 := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlam_pos : 0 < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  set raw : ℝ :=
    ∫ x in (0:ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x with hraw_def
  set lap : ℝ :=
    ∫ x in (0:ℝ)..1,
      Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x with hlap_def
  have hweak : lap = -((k : ℝ) * Real.pi) ^ 2 * raw := by
    simpa [hlap_def, hraw_def] using hf.weak_cosine_laplacian k
  have hraw : raw = -(1 / ((k : ℝ) * Real.pi) ^ 2) * lap := by
    rw [hweak]
    field_simp [ne_of_gt hlam_pos]
  have hlap_bound : |lap| ≤ B :=
    weak_laplacianCoeff_abs_le_of_bound hf hB k
  have hraw_bound : |raw| ≤ B / ((k : ℝ) * Real.pi) ^ 2 := by
    rw [hraw, abs_mul, abs_neg,
      abs_of_pos (by positivity : 0 < 1 / ((k : ℝ) * Real.pi) ^ 2)]
    calc 1 / ((k : ℝ) * Real.pi) ^ 2 * |lap|
        ≤ 1 / ((k : ℝ) * Real.pi) ^ 2 * B :=
          mul_le_mul_of_nonneg_left hlap_bound (by positivity)
      _ = B / ((k : ℝ) * Real.pi) ^ 2 := by ring
  have hcoeff : cosineCoeffs f k = 2 * raw := by
    -- replicate the (private) helper identity: for k ≠ 0,
    -- `cosineCoeffs f k = 2·∫₀¹ cos(kπx)·f(x) dx`
    simp only [ShenWork.IntervalNeumannFullKernel.cosineCoeffs,
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
      if_neg hk_ne,
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
    have hcast :
        (fun x : ℝ =>
            (Real.cos ((k : ℝ) * Real.pi * x) : ℂ) * ((f x : ℝ) : ℂ)) =
          fun x : ℝ =>
            ((Real.cos ((k : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
      funext x
      push_cast
      ring
    rw [hcast, intervalIntegral.integral_ofReal, Complex.ofReal_re, hraw_def]
  rw [hcoeff, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc 2 * |raw| ≤ 2 * (B / ((k : ℝ) * Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left hraw_bound (by norm_num)
    _ = 2 * B / ((k : ℝ) * Real.pi) ^ 2 := by ring

end ShenWork.IntervalSourceDecayQuantitative
