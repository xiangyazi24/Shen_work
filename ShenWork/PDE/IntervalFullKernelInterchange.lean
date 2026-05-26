/-
# Discharging `FullKernelIntegralInterchange`: the `∑'_{m∈ℤ}` ↔ `∫_{[0,1]}` interchange

This file closes the last named hypothesis of `IntervalNeumannFullKernel.lean`.  We prove

  `fullKernelIntegralInterchange_holds`

— a genuine instance of `FullKernelIntegralInterchange` for any **continuous** `f` —
and use it to discharge Theorem 3 (`intervalFullSemigroupOperator_eq_cosineHeatValue`)
and the spatial `C²` corollary (`intervalFullSemigroupOperator_contDiff_two`)
**unconditionally** (no remaining hypothesis on the interchange).

## Proof outline (no `sorry`/`admit`/axiom)

Write `μ = intervalMeasure 1 = volume.restrict (Icc 0 1)`, `E m = exp(-t (mπ)²)`,
`Iint m = ∫ y in 0..1, cos(mπ y) · f y` (a real interval integral), and the per-`m`
summand `F m y = E m · cos(mπ x) · (cos(mπ y) · f y)`.

1. **Pull `f y` inside the `tsum`** (`tsum_mul_right`).
2. **Swap `∫` and `∑'_{m∈ℤ}`** by `integral_tsum_of_summable_integral_norm`:
   each `F m` is integrable on the compact `[0,1]`, and
   `∫ ‖F m‖ ≤ E m · Cf`, summable since `∑_{m∈ℤ} E m < ∞`.
3. **Each term integral** factors: `∫ F m ∂μ = E m · cos(mπ x) · Iint m`.
4. **Even-reflection reindexing** `ℤ → ℕ` via `tsum_int_eq_zero_add_two_mul_tsum_pnat`
   (summand even in `m`), matched against the Neumann-weighted `ℕ`-sum defining
   `cosineCoeffs` (`weight 0 = 1`, `weight (n+1) = 2`).
-/

import ShenWork.PDE.IntervalNeumannFullKernel

open MeasureTheory

noncomputable section

namespace ShenWork.IntervalFullKernelInterchange

open scoped Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

/-! ## Summability of the Gaussian spectral weight over `ℤ` -/

/-- The integer-indexed Gaussian spectral weight `m ↦ exp(-t (mπ)²)` is summable. -/
theorem summable_gaussianWeight (t : ℝ) (ht : 0 < t) :
    Summable (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2)) := by
  set c : ℝ := t * Real.pi ^ 2 with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  have heq : (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2))
      = (fun m : ℤ => Real.exp (-c * ((m : ℝ)) ^ 2)) := by
    funext m; congr 1; rw [hc_def]; ring
  rw [heq]
  apply Summable.of_nat_of_neg
  · have hle : ∀ i : ℕ, (i : ℝ) ≤ (i : ℝ) ^ 2 := by
      intro i
      have : i ≤ i ^ 2 := by nlinarith [Nat.zero_le i]
      calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
        _ ≤ ((i ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
        _ = (i : ℝ) ^ 2 := by push_cast; ring
    have := Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
      (f := fun n : ℕ => (n : ℝ) ^ 2) hle
    simpa using this
  · have hle : ∀ i : ℕ, (i : ℝ) ≤ (i : ℝ) ^ 2 := by
      intro i
      have : i ≤ i ^ 2 := by nlinarith [Nat.zero_le i]
      calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
        _ ≤ ((i ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
        _ = (i : ℝ) ^ 2 := by push_cast; ring
    have := Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
      (f := fun n : ℕ => (n : ℝ) ^ 2) hle
    have heq2 : (fun n : ℕ => Real.exp (-c * (((-(n : ℤ) : ℤ) : ℝ)) ^ 2))
        = (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2)) := by
      funext n; congr 1; push_cast; ring
    rw [heq2]
    simpa using this

/-! ## The interchange, for continuous `f` -/

/-- **`FullKernelIntegralInterchange` holds** for every continuous `f`. -/
theorem fullKernelIntegralInterchange_holds
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    FullKernelIntegralInterchange t f x := by
  classical
  set μ : Measure ℝ := intervalMeasure 1 with hμ
  set E : ℤ → ℝ := fun m => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) with hE
  have hE_pos : ∀ m : ℤ, 0 < E m := fun m => Real.exp_pos _
  have hsummE : Summable E := summable_gaussianWeight t ht
  -- bound for `|f|` on `[0,1]`
  obtain ⟨Cf, hCf⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hf.continuousOn (s := Set.Icc (0 : ℝ) 1))
  -- `Cf ≥ 0`
  have hCf_nonneg : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hCf 0 ⟨le_refl 0, by norm_num⟩)
  -- per-`m` integrand
  set F : ℤ → ℝ → ℝ :=
    fun m y => E m * Real.cos ((m : ℝ) * Real.pi * x) *
      (Real.cos ((m : ℝ) * Real.pi * y) * f y) with hF
  -- continuity of each `F m`
  have hFcont : ∀ m : ℤ, Continuous (F m) := by
    intro m
    rw [hF]
    fun_prop
  -- integrability of each `F m` against `μ`
  have hFint : ∀ m : ℤ, Integrable (F m) μ := by
    intro m
    rw [hμ]
    have : IntegrableOn (F m) (Set.Icc (0 : ℝ) 1) volume :=
      (hFcont m).continuousOn.integrableOn_compact isCompact_Icc
    -- `intervalMeasure 1 = volume.restrict (intervalSet 1) = volume.restrict (Icc 0 1)`
    simpa [intervalMeasure, intervalSet, IntegrableOn] using this
  -- pointwise bound `‖F m y‖ ≤ E m * Cf` on `[0,1]`
  have hFbound : ∀ m : ℤ, ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖F m y‖ ≤ E m * Cf := by
    intro m y hy
    have hcosx : |Real.cos ((m : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hcosy : |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
    have hfy : |f y| ≤ Cf := by simpa [Real.norm_eq_abs] using hCf y hy
    rw [hF, Real.norm_eq_abs]
    have hexpand : |E m * Real.cos ((m : ℝ) * Real.pi * x) *
        (Real.cos ((m : ℝ) * Real.pi * y) * f y)|
        = E m * (|Real.cos ((m : ℝ) * Real.pi * x)| *
            (|Real.cos ((m : ℝ) * Real.pi * y)| * |f y|)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (hE_pos m)]; ring
    rw [hexpand]
    have hinner : |Real.cos ((m : ℝ) * Real.pi * x)| *
        (|Real.cos ((m : ℝ) * Real.pi * y)| * |f y|) ≤ Cf := by
      have h := mul_le_mul hcosx (mul_le_mul hcosy hfy (abs_nonneg _) (by norm_num))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num : (0:ℝ) ≤ 1)
      simpa using h
    exact mul_le_mul_of_nonneg_left hinner (hE_pos m).le
  -- `∫ ‖F m‖ ∂μ ≤ E m * Cf`
  have hFnorm_int_le : ∀ m : ℤ, ∫ y, ‖F m y‖ ∂μ ≤ E m * Cf := by
    intro m
    have hμ_meas : μ.real Set.univ = 1 := by
      rw [hμ, intervalMeasure, intervalSet, measureReal_restrict_apply_univ,
        measureReal_def, Real.volume_Icc]
      simp
    have hbound_ae : ∀ᵐ y ∂μ, ‖F m y‖ ≤ E m * Cf := by
      rw [hμ]
      rw [intervalMeasure, intervalSet]
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun y hy => hFbound m y hy)
    calc ∫ y, ‖F m y‖ ∂μ
        ≤ ∫ _y, E m * Cf ∂μ :=
          MeasureTheory.integral_mono_ae
            ((hFint m).norm) (MeasureTheory.integrable_const _) hbound_ae
      _ = E m * Cf := by
          rw [MeasureTheory.integral_const, hμ_meas]; simp
  -- summability of `m ↦ ∫ ‖F m‖ ∂μ`
  have hFsum : Summable (fun m : ℤ => ∫ y, ‖F m y‖ ∂μ) := by
    apply Summable.of_nonneg_of_le
      (fun m => MeasureTheory.integral_nonneg (fun y => norm_nonneg _))
      hFnorm_int_le
    exact hsummE.mul_right Cf
  -- (Step 1) pull `f y` inside the spectral tsum, pointwise in `y`
  have hsummand : ∀ y : ℝ,
      Summable (fun m : ℤ => E m *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) := by
    intro y
    apply Summable.of_norm_bounded (g := E) hsummE
    intro m
    have hcosx : |Real.cos ((m : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hcosy : |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
    have hexpand : |E m * (Real.cos ((m : ℝ) * Real.pi * x) *
        Real.cos ((m : ℝ) * Real.pi * y))|
        = E m * (|Real.cos ((m : ℝ) * Real.pi * x)| * |Real.cos ((m : ℝ) * Real.pi * y)|) := by
      rw [abs_mul, abs_mul, abs_of_pos (hE_pos m)]
    rw [Real.norm_eq_abs, hexpand]
    have hcc : |Real.cos ((m : ℝ) * Real.pi * x)| * |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := by
      calc |Real.cos ((m : ℝ) * Real.pi * x)| * |Real.cos ((m : ℝ) * Real.pi * y)|
          ≤ 1 * 1 := mul_le_mul hcosx hcosy (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc E m * (|Real.cos ((m : ℝ) * Real.pi * x)| * |Real.cos ((m : ℝ) * Real.pi * y)|)
        ≤ E m * 1 := mul_le_mul_of_nonneg_left hcc (hE_pos m).le
      _ = E m := by ring
  -- the integrand of `FullKernelIntegralInterchange` equals `∑'_m F m y`
  have hintegrand : ∀ y : ℝ,
      (∑' m : ℤ, E m *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y
        = ∑' m : ℤ, F m y := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr (fun m => ?_)
    rw [hF]; ring
  -- (Step 2) the interchange of `∫` and `∑'_m`
  have hswap :
      (∫ y, (∑' m : ℤ, F m y) ∂μ) = ∑' m : ℤ, ∫ y, F m y ∂μ :=
    (integral_tsum_of_summable_integral_norm hFint hFsum).symm
  -- (Step 3) factor each term integral
  -- `Iint m := ∫ y in 0..1, cos(mπ y) · f y`
  set Iint : ℤ → ℝ :=
    (fun m => ∫ y in (0 : ℝ)..1, Real.cos ((m : ℝ) * Real.pi * y) * f y) with hIint
  have hterm : ∀ m : ℤ, (∫ y, F m y ∂μ) =
      E m * Real.cos ((m : ℝ) * Real.pi * x) * Iint m := by
    intro m
    rw [hF, hIint]
    -- pull the constant `E m * cos(mπx)` out of the integral
    rw [show (fun y => E m * Real.cos ((m : ℝ) * Real.pi * x) *
          (Real.cos ((m : ℝ) * Real.pi * y) * f y))
        = (fun y => (E m * Real.cos ((m : ℝ) * Real.pi * x)) *
          (Real.cos ((m : ℝ) * Real.pi * y) * f y)) from by funext y; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    -- `∫ ... ∂(volume.restrict (Icc 0 1)) = ∫ y in 0..1, ...`
    rw [hμ, intervalMeasure, intervalSet]
    change (∫ y in Set.Icc (0:ℝ) 1, Real.cos ((m : ℝ) * Real.pi * y) * f y ∂volume)
        = ∫ y in (0:ℝ)..1, Real.cos ((m : ℝ) * Real.pi * y) * f y
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- assemble Steps 1–3:  LHS of the goal = `∑'_m E m · cos(mπx) · Iint m`
  have hLHS :
      (∫ y, (∑' m : ℤ, E m *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y ∂μ)
        = ∑' m : ℤ, E m * Real.cos ((m : ℝ) * Real.pi * x) * Iint m := by
    rw [show (fun y => (∑' m : ℤ, E m *
            (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y)
          = (fun y => ∑' m : ℤ, F m y) from by funext y; rw [hintegrand y]]
    rw [hswap]
    exact tsum_congr hterm
  -- (Step 4) even-reflection reindexing `ℤ → ℕ`
  -- The ℤ-summand `φ m := E m · cos(mπx) · Iint m` is even in `m`.
  set φ : ℤ → ℝ := fun m => E m * Real.cos ((m : ℝ) * Real.pi * x) * Iint m with hφ
  have hEeven : ∀ m : ℤ, E (-m) = E m := by
    intro m
    simp only [hE]
    congr 2
    push_cast; ring
  have hcosxeven : ∀ m : ℤ,
      Real.cos (((-m : ℤ) : ℝ) * Real.pi * x) = Real.cos ((m : ℝ) * Real.pi * x) := by
    intro m
    rw [show (((-m : ℤ) : ℝ) * Real.pi * x) = -((m : ℝ) * Real.pi * x) by push_cast; ring,
      Real.cos_neg]
  have hIinteven : ∀ m : ℤ, Iint (-m) = Iint m := by
    intro m
    rw [hIint]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [show (((-m : ℤ) : ℝ) * Real.pi * y) = -((m : ℝ) * Real.pi * y) by push_cast; ring,
      Real.cos_neg]
  have hφeven : Function.Even φ := by
    intro m
    rw [hφ]
    simp only
    rw [hEeven m, hcosxeven m, hIinteven m]
  -- summability of `φ`
  have hφsumm : Summable φ := by
    apply Summable.of_norm_bounded (g := fun m => E m * Cf)
    · exact hsummE.mul_right Cf
    intro m
    rw [hφ]
    have hcosx : |Real.cos ((m : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    -- `|Iint m| ≤ Cf` from the per-term integral norm bound
    have hIabs : |Iint m| ≤ Cf := by
      have hcont : Continuous (fun y => Real.cos ((m : ℝ) * Real.pi * y) * f y) := by
        fun_prop
      have hintII : IntervalIntegrable
          (fun y => |Real.cos ((m : ℝ) * Real.pi * y) * f y|) volume 0 1 :=
        (hcont.abs).intervalIntegrable 0 1
      have hbd : ∀ y ∈ Set.Icc (0:ℝ) 1,
          |Real.cos ((m : ℝ) * Real.pi * y) * f y| ≤ Cf := by
        intro y hy
        have hcosy : |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
        have hfy : |f y| ≤ Cf := by simpa [Real.norm_eq_abs] using hCf y hy
        rw [abs_mul]
        calc |Real.cos ((m : ℝ) * Real.pi * y)| * |f y|
            ≤ 1 * Cf := mul_le_mul hcosy hfy (abs_nonneg _) (by norm_num)
          _ = Cf := by ring
      calc |Iint m|
          ≤ ∫ y in (0:ℝ)..1, |Real.cos ((m : ℝ) * Real.pi * y) * f y| := by
            rw [hIint]
            exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
        _ ≤ ∫ _y in (0:ℝ)..1, Cf :=
            intervalIntegral.integral_mono_on (by norm_num) hintII
              (intervalIntegrable_const) hbd
        _ = Cf := by rw [intervalIntegral.integral_const]; simp
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hE_pos m)]
    have hcc : |Real.cos ((m : ℝ) * Real.pi * x)| * |Iint m| ≤ Cf := by
      calc |Real.cos ((m : ℝ) * Real.pi * x)| * |Iint m|
          ≤ 1 * Cf := mul_le_mul hcosx hIabs (abs_nonneg _) (by norm_num)
        _ = Cf := by ring
    calc E m * |Real.cos ((m : ℝ) * Real.pi * x)| * |Iint m|
        = E m * (|Real.cos ((m : ℝ) * Real.pi * x)| * |Iint m|) := by ring
      _ ≤ E m * Cf := mul_le_mul_of_nonneg_left hcc (hE_pos m).le
  -- even fold:  `∑'_{m∈ℤ} φ m = φ 0 + 2 • ∑'_{n:ℕ+} φ n`
  have hfold := tsum_int_eq_zero_add_two_mul_tsum_pnat hφeven hφsumm
  -- now relate `φ` to the Neumann-weighted ℕ-sum defining `cosineCoeffs`.
  -- RHS:  `unitIntervalCosineHeatValue t (cosineCoeffs f) x
  --        = ∑'_{n:ℕ} weight n · φ' n` matching φ on ℕ.
  -- `cosineCoeffs f n = unitIntervalNeumannCosineCoeff (↑f) n = w n · Iint n`,
  -- where `Iint n = (raw n).re` and `w 0 = 1`, `w (n+1) = 2`.
  -- First: identify `(raw n).re` with the real `Iint n`.
  have hraw_re : ∀ n : ℕ,
      (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
          (fun x => (f x : ℂ)) n).re = Iint (n : ℤ) := by
    intro n
    rw [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff, hIint]
    rw [show (fun y => (Real.cos ((n : ℝ) * Real.pi * y) : ℂ) * (f y : ℂ))
          = (fun y => (((Real.cos ((n : ℝ) * Real.pi * y) * f y) : ℝ) : ℂ)) from by
        funext y; push_cast; ring]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    simp only [Int.cast_natCast]
  -- `cosineCoeffs f n` in terms of `Iint`
  have hcoeff : ∀ n : ℕ, cosineCoeffs f n =
      (if n = 0 then (1 : ℝ) else 2) * Iint (n : ℤ) := by
    intro n
    rw [cosineCoeffs, ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff]
    by_cases hn : n = 0
    · subst hn; simp [hraw_re 0]
    · simp only [hn, if_false]
      rw [hraw_re n]
  -- Expand the RHS `unitIntervalCosineHeatValue` as a ℕ-tsum and split off `n = 0`.
  -- `unitIntervalCosineHeatValue t a x = ∑'_n w_pt n · a n`,
  -- `w_pt n = exp(-t (nπ)²) · cos(nπx) = E n · cos(nπx)` (for `n : ℕ`, cast to ℤ).
  have hweight_pt : ∀ n : ℕ,
      unitIntervalCosineHeatPointWeight t x n
        = E (n : ℤ) * Real.cos ((n : ℝ) * Real.pi * x) := by
    intro n
    rw [unitIntervalCosineHeatPointWeight,
      unitIntervalCosineMode,
      unitIntervalCosineEigenvalue, hE]
    push_cast
    ring
  -- the RHS ℕ-summand:  `ψ n = w_pt n · cosineCoeffs f n`
  set ψ : ℕ → ℝ := fun n =>
    unitIntervalCosineHeatPointWeight t x n * cosineCoeffs f n
    with hψ
  -- `ψ` matches `φ` (on ℕ) up to the Neumann weight:  `ψ 0 = φ 0`, `ψ (n+1) = 2 φ (n+1)`.
  have hψ0 : ψ 0 = φ 0 := by
    simp only [hψ, hφ]
    rw [hweight_pt 0, hcoeff 0]
    simp
  have hψsucc : ∀ n : ℕ, ψ (n + 1) = 2 * φ ((n + 1 : ℕ) : ℤ) := by
    intro n
    simp only [hψ, hφ]
    rw [hweight_pt (n + 1), hcoeff (n + 1)]
    simp only [Nat.succ_ne_zero, if_false]
    push_cast
    ring
  -- summability of `ψ`
  have hψsumm : Summable ψ := by
    have hφnat : Summable (fun n : ℕ => φ (n : ℤ)) :=
      (summable_int_iff_summable_nat_and_neg.mp hφsumm).1
    -- `ψ n` is bounded by `2 * φ (n:ℤ)`-type; build summability via congr on tail.
    apply (summable_nat_add_iff 1).mp
    have : (fun n : ℕ => ψ (n + 1)) = (fun n : ℕ => 2 * φ ((n + 1 : ℕ) : ℤ)) := by
      funext n; exact hψsucc n
    rw [this]
    exact ((summable_nat_add_iff 1).mpr hφnat).mul_left 2
  -- the `ℕ → 0 + ℕ+` split of `ψ`, via succ-reindexing.
  -- `∑'_n ψ n = ψ 0 + ∑'_{n:ℕ} ψ (n+1) = φ 0 + ∑'_n 2 φ (n+1)`.
  have hψtsum : (∑' n : ℕ, ψ n) = φ 0 + ∑' n : ℕ, (2 : ℝ) * φ ((n + 1 : ℕ) : ℤ) := by
    rw [hψsumm.tsum_eq_zero_add, hψ0]
    congr 1
    exact tsum_congr hψsucc
  -- `∑'_{n:ℕ+} φ n = ∑'_n φ (n+1)` (pnat ↔ succ), and `2 • s = 2 * s`.
  have hpnat : (∑' n : ℕ+, φ (n : ℤ)) = ∑' n : ℕ, φ ((n + 1 : ℕ) : ℤ) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => φ (n : ℤ))]
  -- assemble:  `unitIntervalCosineHeatValue = ∑' ψ = φ 0 + 2 • ∑'_{ℕ+} φ = ∑'_{ℤ} φ`.
  have hRHS : unitIntervalCosineHeatValue t (cosineCoeffs f) x
      = ∑' m : ℤ, φ m := by
    rw [unitIntervalCosineHeatValue]
    change (∑' n : ℕ, ψ n) = _
    rw [hψtsum, hfold]
    rw [show (∑' n : ℕ, (2 : ℝ) * φ ((n + 1 : ℕ) : ℤ))
          = 2 * ∑' n : ℕ, φ ((n + 1 : ℕ) : ℤ) from by
        rw [tsum_mul_left]]
    rw [← hpnat]
    rw [two_nsmul]
    ring
  -- conclude
  rw [FullKernelIntegralInterchange, ← hμ]
  rw [hLHS]
  rw [hRHS]

/-! ## Unconditional closure of Theorem 3 and the `C²` corollary -/

/-- **Theorem 3, unconditional** (for continuous `f`).  The full periodised-image
Neumann propagator equals the cosine spectral heat value — no remaining hypothesis. -/
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hkernel : ∀ y, intervalNeumannFullKernel t x y =
      ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x :=
  intervalFullSemigroupOperator_eq_cosineHeatValue t ht f x hx hkernel
    (fullKernelIntegralInterchange_holds t ht f hf x)

/-- **`C²` corollary, unconditional** (for continuous `f`).  Given the pointwise
kernel identity at every `x` (the Poisson/theta content, dischargeable from
`intervalNeumannFullKernel_eq_cosineKernel`) and the coefficient bound, the full
periodised Neumann propagator is `C²` in space.  The interchange hypothesis is
discharged internally by `fullKernelIntegralInterchange_holds`. -/
theorem intervalFullSemigroupOperator_contDiff_two_unconditional
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator t f x) := by
  have hidentity : (fun x => intervalFullSemigroupOperator t f x)
      = fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
    funext x
    rw [intervalFullSemigroupOperator]
    rw [show (fun y => intervalNeumannFullKernel t x y * f y)
          = (fun y => (∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
              (Real.cos ((m : ℝ) * Real.pi * x) *
                Real.cos ((m : ℝ) * Real.pi * y))) * f y) from by
        funext y; rw [hkernel x y]]
    exact fullKernelIntegralInterchange_holds t ht f hf x
  exact intervalFullSemigroupOperator_contDiff_two t ht f hM hidentity

end ShenWork.IntervalFullKernelInterchange
