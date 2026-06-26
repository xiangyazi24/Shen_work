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

/-! ## Depth-2 quartic decay from iterated weak H² Neumann -/

/-- **Quartic coefficient decay** from a depth-2 weak H² Neumann tower:
if `f` and `f''` both carry `IntervalWeakH2Neumann` certificates, then
`|cosineCoeffs f k| ≤ 2·B₂ / (kπ)⁴` for `k ≥ 1`, where `B₂` is an `L¹`
bound on the fourth derivative `f⁴`.

**Proof.** Depth-1 identity: `cosineCoeffs(f) k = -cosineCoeffs(f'') k / (kπ)²`.
Depth-1 quadratic decay of `f''`: `|cosineCoeffs(f'') k| ≤ 2B₂/(kπ)²`.
Substitute: `|cosineCoeffs(f) k| ≤ 2B₂/(kπ)⁴`. -/
theorem intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv)
    {B₂ : ℝ} (hB₂ : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) ≤ B₂) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4 := by
  intro k hk
  have hk_ne : k ≠ 0 := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hlam_pos : 0 < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam_ne : ((k : ℝ) * Real.pi) ^ 2 ≠ 0 := ne_of_gt hlam_pos
  -- From the weak cosine Laplacian identity:
  -- ∫ cos(kπx) f''(x) dx = -(kπ)² ∫ cos(kπx) f(x) dx
  -- For k ≥ 1, cosineCoeffs g k = 2 * ∫ cos(kπx) g(x) dx
  -- So cosineCoeffs(f'') k = -(kπ)² * cosineCoeffs(f) k
  -- Hence |cosineCoeffs f k| = |cosineCoeffs(f'') k| / (kπ)²
  have hweak := hf.weak_cosine_laplacian k
  -- Extract: cosineCoeffs f k = -cosineCoeffs(f'') k / (kπ)²
  -- Both cosineCoeffs are 2 * raw, so the factor 2 cancels
  set raw_f : ℝ := ∫ x in (0:ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
  have hraw_rel : raw_f = -(1 / ((k : ℝ) * Real.pi) ^ 2) *
      ∫ x in (0:ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x := by
    have := hweak; field_simp [hlam_ne] at this ⊢; linarith
  -- |cosineCoeffs f k| ≤ |cosineCoeffs(f'') k| / (kπ)²
  -- Since cosineCoeffs f k = 2 * raw_f = -2/(kπ)² * raw_f'' = -cosineCoeffs(f'')/( kπ)²
  -- we get |cosineCoeffs f k| = |cosineCoeffs(f'') k| / (kπ)²
  -- Quadratic decay of f'': |cosineCoeffs(f'') k| ≤ 2B₂/(kπ)²
  -- raw integral for f''
  set raw_f'' : ℝ :=
    ∫ x in (0:ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x
  -- cosineCoeffs hf.secondDeriv k = 2 * raw_f''
  have hcoeff_f'' : cosineCoeffs hf.secondDeriv k = 2 * raw_f'' := by
    simp only [cosineCoeffs,
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
      if_neg hk_ne,
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
    have hcast :
        (fun x : ℝ =>
            (Real.cos ((k : ℝ) * Real.pi * x) : ℂ) *
              ((hf.secondDeriv x : ℝ) : ℂ)) =
          fun x : ℝ =>
            ((Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x : ℝ) : ℂ) := by
      funext x; push_cast; ring
    rw [hcast, intervalIntegral.integral_ofReal, Complex.ofReal_re]
  -- cosineCoeffs f k = 2 * raw_f
  have hcoeff_f : cosineCoeffs f k = 2 * raw_f := by
    simp only [cosineCoeffs,
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
      if_neg hk_ne,
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
    have hcast :
        (fun x : ℝ =>
            (Real.cos ((k : ℝ) * Real.pi * x) : ℂ) * ((f x : ℝ) : ℂ)) =
          fun x : ℝ =>
            ((Real.cos ((k : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
      funext x; push_cast; ring
    rw [hcast, intervalIntegral.integral_ofReal, Complex.ofReal_re]
  -- Quadratic decay of f'': |cosineCoeffs(f'') k| ≤ 2B₂/(kπ)²
  have hdecay_f'' :=
    intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound hf'' hB₂ k hk
  -- |raw_f''| ≤ B₂/(kπ)²
  have hraw_f''_bound : |raw_f''| ≤ B₂ / ((k : ℝ) * Real.pi) ^ 2 := by
    -- From hf''.weak_cosine_laplacian:
    --   ∫ cos(kπx) hf''.secondDeriv(x) dx = -(kπ)² · raw_f''
    -- And |∫ cos(kπx) hf''.secondDeriv(x) dx| ≤ B₂
    -- So (kπ)² |raw_f''| ≤ B₂, hence |raw_f''| ≤ B₂/(kπ)²
    have hlap2 := hf''.weak_cosine_laplacian k
    -- From weak_laplacianCoeff_abs_le_of_bound applied to hf'':
    --   |∫ cos(kπx) hf''.secondDeriv(x) dx| ≤ B₂
    -- From hlap2: that integral = -(kπ)² · raw_f''
    -- So (kπ)² |raw_f''| ≤ B₂, hence |raw_f''| ≤ B₂/(kπ)²
    have hcoeff_bound := weak_laplacianCoeff_abs_le_of_bound hf'' hB₂ k
    rw [hlap2] at hcoeff_bound
    -- hcoeff_bound : |-(kπ)² * ∫ cos * f''| ≤ B₂
    -- The integral is definitionally raw_f'', but need to normalize the neg
    simp only [neg_mul] at hcoeff_bound
    rw [abs_neg, abs_mul, abs_of_pos hlam_pos] at hcoeff_bound
    rw [le_div_iff₀ hlam_pos, mul_comm]
    exact hcoeff_bound
  -- |raw_f| ≤ B₂/(kπ)⁴
  have hraw_f_bound : |raw_f| ≤ B₂ / ((k : ℝ) * Real.pi) ^ 4 := by
    rw [hraw_rel, abs_mul, abs_neg,
      abs_of_pos (by positivity : 0 < 1 / ((k : ℝ) * Real.pi) ^ 2)]
    calc 1 / ((k : ℝ) * Real.pi) ^ 2 * |raw_f''|
        ≤ 1 / ((k : ℝ) * Real.pi) ^ 2 * (B₂ / ((k : ℝ) * Real.pi) ^ 2) :=
          mul_le_mul_of_nonneg_left hraw_f''_bound (by positivity)
      _ = B₂ / ((k : ℝ) * Real.pi) ^ 4 := by ring
  rw [hcoeff_f, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc 2 * |raw_f| ≤ 2 * (B₂ / ((k : ℝ) * Real.pi) ^ 4) :=
        mul_le_mul_of_nonneg_left hraw_f_bound (by norm_num)
    _ = 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4 := by ring

/-- **Eigenvalue-weighted L¹ summability** from depth-2 weak H² Neumann tower.
Feeds `resolverCoeff_eigenSq_summable_of_sourceEigenL1` for resolver C⁴. -/
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|) := by
  obtain ⟨B₂, _, hB₂⟩ := hf''.second_abs_integral_bound
  have hdecay := intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound hf hf'' hB₂
  -- For k ≥ 1: λ_k |c_k| = (kπ)² |c_k| ≤ (kπ)² · 2B₂/(kπ)⁴ = 2B₂/(kπ)²
  --   = (2B₂/π²) · (1/k²).  The series ∑ (2B₂/π²)(1/k²) converges.
  refine Summable.of_nonneg_of_le
    (fun _ => by unfold unitIntervalCosineEigenvalue; positivity) (fun k => ?_)
    (((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).mul_left
      (2 * B₂ / Real.pi ^ 2))
  by_cases hk : k = 0
  · subst hk; simp [unitIntervalCosineEigenvalue]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk1
    change unitIntervalCosineEigenvalue k * |cosineCoeffs f k| ≤
        2 * B₂ / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2)
    simp only [unitIntervalCosineEigenvalue]
    calc ((k : ℝ) * Real.pi) ^ 2 * |cosineCoeffs f k|
        ≤ ((k : ℝ) * Real.pi) ^ 2 * (2 * B₂ / ((k : ℝ) * Real.pi) ^ 4) :=
          mul_le_mul_of_nonneg_left (hdecay k hk1) (by positivity)
      _ = 2 * B₂ / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) := by
          rw [mul_pow]
          have hk2 : (k : ℝ) ^ 2 ≠ 0 := by positivity
          have hpi2 : Real.pi ^ 2 ≠ 0 := by positivity
          field_simp; try ring

end ShenWork.IntervalSourceDecayQuantitative
