/-
# C²-Neumann cosine-coefficient decay `|f̂ₙ| ≤ C/n²` and `ℓ¹` summability

This file proves sub-step **(b1)** of the static chemotaxis-gradient control: for a
function `f` that is `C²` on the closed interval `[0,1]` (concretely: closed-`Icc`
`C²` regularity `ContDiffOn ℝ 2 f (Icc 0 1)`, with genuine endpoint Neumann values
`deriv f 0 = deriv f 1 = 0` and one-sided endpoint limits of `deriv f` vanishing),
the cosine coefficient

  `f̂ₙ = ∫₀¹ cos(nπx) · f(x) dx`

satisfies the quadratic decay `|f̂ₙ| ≤ M / (nπ)²` for `n ≥ 1`, with `M` a uniform
bound on `|f''|` over the interval.

## Proof route (the eigenfunction IBP)

The already-proven eigenfunction integration-by-parts identity
`ShenWork.IntervalEllipticCharacterization.intervalCosineLaplacianCoeff_eq_of_contDiffOn`
gives, for every `n`,

  `∫₀¹ cos(nπx) · (deriv (deriv f)) x dx = −(nπ)² · ∫₀¹ cos(nπx) · f(x) dx`.

Hence `f̂ₙ = −(1/(nπ)²) · (Δf)̂ₙ` for `n ≥ 1`, and `(Δf)̂ₙ = ∫₀¹ cos(nπx) · f''`
is bounded by `M` (the second derivative agrees a.e. with the closed-`Icc`
`derivWithin`-second-derivative, continuous on the compact `[0,1]`, hence uniformly
bounded; `|cos| ≤ 1`; the interval has length `1`).  This yields
`|f̂ₙ| ≤ M / (nπ)²`.

## The `ℓ¹` consequence (the actual hypothesis the inversion needs)

Because `|f̂ₙ| ≤ (M/π²) · 1/n²` and `∑ 1/n²` converges, the `ℤ`-indexed
`AddCircle 2` Fourier coefficients `fourierCoeff (reflCircle f) n` (which equal the
real cosine coefficients via `fourierCoeff_reflCircle`/`fco_eq_ofReal`, and are even
in `n` via `fco_neg`) are **absolutely summable**.  This is exactly the hypothesis
`hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n)` consumed by
`intervalCosine_hasSum_pointwise` and `solution_v_eq_resolver_pointwise` — closing
the VALUE-reconstruction gap (A) for any `C²`-Neumann interval datum.

No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.IntervalCosineInversion
import Mathlib.Analysis.PSeries

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.IntervalSolutionCoeffDeriv ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalCosineInversion
open scoped Topology

namespace ShenWork.IntervalCosineCoeffDecay

noncomputable section

/-! ## Uniform bound on the Laplacian cosine coefficient -/

/-- For a closed-`Icc` `C²` function `f`, the Laplacian cosine coefficient
`∫₀¹ cos(nπx) · (deriv (deriv f)) x dx` is bounded, uniformly in `n`, by a single
constant `M ≥ 0` (namely the sup of `|deriv (deriv f)|` over the compact `[0,1]`,
through the a.e.-equal continuous closed-`Icc` second `derivWithin`; `|cos| ≤ 1`
and the interval has length `1`). -/
theorem exists_laplacianCoeff_bound
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      |∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * deriv (deriv f) x| ≤ M := by
  classical
  -- The continuous-on-`Icc` second `derivWithin`.
  set g₂ : ℝ → ℝ := derivWithin (derivWithin f (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1)
    with hg₂
  have hg₂_cont : ContinuousOn g₂ (Set.Icc (0:ℝ) 1) := by
    have hg1 : ContDiffOn ℝ 1 (derivWithin f (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) :=
      hf.derivWithin uniqueDiffOn_Icc01 (by norm_num)
    exact hg1.continuousOn_derivWithin uniqueDiffOn_Icc01 (le_refl 1)
  -- A uniform bound `B ≥ 0` for `|g₂|` on the compact `[0,1]`.
  obtain ⟨B0, hB0mem⟩ :=
    (isCompact_Icc.image_of_continuousOn (hg₂_cont.abs)).bddAbove
  set B : ℝ := max B0 0 with hB
  have hBnonneg : 0 ≤ B := le_max_right _ _
  have hbound_g₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, |g₂ x| ≤ B := by
    intro x hx
    exact (hB0mem ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  -- `deriv (deriv f)` agrees a.e. on `Ioc 0 1` with `g₂`.
  have hae : (deriv (deriv f)) =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] g₂ := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    push_neg at hx
    obtain ⟨hxIoc, hne⟩ := hx
    simp only [Set.mem_singleton_iff]
    by_contra hx1
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx1⟩
    -- on the interior `deriv (deriv f) x = g₂ x`.
    have heq1 : derivWithin f (Set.Icc (0 : ℝ) 1) =ᶠ[𝓝 x] deriv f := by
      filter_upwards [isOpen_Ioo.mem_nhds hxIoo] with y hy
      exact (deriv_eq_derivWithin_interior hy).symm
    have h2 : g₂ x = deriv (deriv f) x := by
      rw [hg₂, deriv_eq_derivWithin_interior hxIoo |>.symm]
      exact Filter.EventuallyEq.deriv_eq heq1
    exact hne h2.symm
  refine ⟨B, hBnonneg, ?_⟩
  intro n
  -- Replace `deriv (deriv f)` by `g₂` in the integral (a.e. equal on `Ioc 0 1`).
  have hrw : (∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * deriv (deriv f) x)
      = ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * g₂ x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hrw]
  -- Bound `|∫ cos · g₂| ≤ B` by `norm_integral_le_of_norm_le_const`.
  have hbnd : ∀ x ∈ Set.uIoc (0:ℝ) 1,
      ‖Real.cos ((n : ℝ) * Real.pi * x) * g₂ x‖ ≤ B := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := Set.Ioc_subset_Icc_self hx
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.cos ((n : ℝ) * Real.pi * x)| * |g₂ x|
        ≤ 1 * B := by
          apply mul_le_mul (Real.abs_cos_le_one _) (hbound_g₂ x hxIcc) (abs_nonneg _)
            (by norm_num)
      _ = B := one_mul B
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rw [Real.norm_eq_abs] at hle
  simpa using hle

/-! ## The decay `|f̂ₙ| ≤ M/(nπ)²` -/

/-- **C²-Neumann cosine-coefficient decay (sub-step b1).**

For `f : ℝ → ℝ` that is `C²` on `[0,1]` (closed-`Icc`), with genuine endpoint
Neumann values `deriv f 0 = deriv f 1 = 0` and vanishing one-sided endpoint limits
of `deriv f`, the cosine coefficient obeys, for `n ≥ 1`,

  `|∫₀¹ cos(nπx) · f(x) dx| ≤ M / (nπ)²`,

where `M` is the uniform Laplacian-coefficient bound from
`exists_laplacianCoeff_bound`.  This is the engine of the absolute-summability of
the cosine series. -/
theorem cosineCoeff_decay
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv f) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv f 0 = 0) (hbc1 : deriv f 1 = 0)
    {M : ℝ} (hMnonneg : 0 ≤ M)
    (hMbound : ∀ n : ℕ,
      |∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * deriv (deriv f) x| ≤ M)
    {n : ℕ} (hn : 1 ≤ n) :
    |∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x| ≤
      M / ((n : ℝ) * Real.pi) ^ 2 := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnpi_pos : (0 : ℝ) < (n : ℝ) * Real.pi := mul_pos hnpos Real.pi_pos
  have hnpi_sq_pos : (0 : ℝ) < ((n : ℝ) * Real.pi) ^ 2 := by positivity
  -- the eigenfunction IBP identity.
  have hIBP := intervalCosineLaplacianCoeff_eq_of_contDiffOn n hf htend0 htend1 hbc0 hbc1
  -- so `∫ cos f = -(1/(nπ)²) · ∫ cos f''`.
  have hsolve : (∫ x in (0:ℝ)..1, Real.cos ((n:ℝ) * Real.pi * x) * f x)
      = -(1 / ((n:ℝ) * Real.pi) ^ 2) *
          (∫ x in (0:ℝ)..1, Real.cos ((n:ℝ) * Real.pi * x) * deriv (deriv f) x) := by
    -- from `hIBP : ∫cos f'' = -(nπ)² ∫cos f`.
    field_simp
    rw [hIBP]; ring
  rw [hsolve, abs_mul]
  have habs1 : |(-(1 / ((n:ℝ) * Real.pi) ^ 2))| = 1 / ((n:ℝ) * Real.pi) ^ 2 := by
    rw [abs_neg, abs_of_pos (by positivity)]
  rw [habs1]
  calc 1 / ((n:ℝ) * Real.pi) ^ 2 *
        |∫ x in (0:ℝ)..1, Real.cos ((n:ℝ) * Real.pi * x) * deriv (deriv f) x|
      ≤ 1 / ((n:ℝ) * Real.pi) ^ 2 * M := by
        apply mul_le_mul_of_nonneg_left (hMbound n) (by positivity)
    _ = M / ((n:ℝ) * Real.pi) ^ 2 := by ring

/-! ## Absolute summability of the `AddCircle 2` Fourier coefficients (gap A) -/

/-- **C²-Neumann ⇒ `ℓ¹` cosine coefficients (sub-step b1, the summable form).**

For a `C²`-on-`[0,1]` function `f` with genuine Neumann endpoints (and vanishing
one-sided derivative limits), the `ℤ`-indexed `AddCircle 2` Fourier coefficients of
the even reflection are absolutely summable:

  `Summable (fun n : ℤ => fourierCoeff (reflCircle f) n)`.

This is the regularity hypothesis (gap A) consumed by `intervalCosine_hasSum_pointwise`
/ `solution_v_eq_resolver_pointwise`; it is now UNCONDITIONAL for `C²`-Neumann data.
Proof: `‖fourierCoeff (reflCircle f) n‖ = |f̂ₙ| ≤ (M/π²)·(1/n²)` for `n ≥ 1` (decay
above), `f̂` even in `n` (`fco_neg`), comparison with `∑ 1/n²`. -/
theorem fourierCoeff_reflCircle_summable
    {f : ℝ → ℝ} (hfcont : Continuous f)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv f) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv f 0 = 0) (hbc1 : deriv f 1 = 0) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle f) n) := by
  classical
  obtain ⟨M, hMnonneg, hMbound⟩ := exists_laplacianCoeff_bound hf
  -- norm form: `‖fourierCoeff (reflCircle f) n‖ = |f̂_|n||`.
  -- It suffices to show summability of the norms (abs convergence ⇒ convergence).
  rw [← summable_norm_iff]
  -- reduce ℤ to nat-and-neg.
  apply Summable.of_nat_of_neg_add_one
  · -- positive part: `n : ℕ`, `‖fourierCoeff (reflCircle f) n‖`.
    -- majorant `(M/π²) · 1/n²` (with a `1` correction at `n=0` and `n` recast).
    -- Use comparison after dropping the `n = 0` term.
    rw [← summable_nat_add_iff 1]
    -- Now indexed by `n` standing for `n+1 ≥ 1`.
    have hmaj : Summable fun n : ℕ =>
        (M / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
      have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
        simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
      exact hp2.mul_left _
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmaj
    intro n
    -- `‖fourierCoeff (reflCircle f) (n+1)‖ = |f̂_{n+1}| ≤ M/((n+1)π)² ≤ (M/π²)/(n+1)²`.
    have hfc : fourierCoeff (reflCircle f) ((n + 1 : ℕ) : ℤ)
        = ((∫ x in (0:ℝ)..1, Real.cos (((n:ℝ)+1) * Real.pi * x) * f x : ℝ) : ℂ) := by
      rw [fourierCoeff_reflCircle, fco_eq_ofReal f hfcont]
      norm_cast
    rw [hfc, Complex.norm_real, Real.norm_eq_abs]
    have hdecay := cosineCoeff_decay hf htend0 htend1 hbc0 hbc1 hMnonneg hMbound
      (n := n + 1) (Nat.le_add_left 1 n)
    have hcast : ((↑(n + 1) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hdecay
    -- `M/((n+1)π)² = (M/π²)·1/(n+1)²`.
    have hsplit : M / (((n:ℝ) + 1) * Real.pi) ^ 2
        = (M / Real.pi ^ 2) * (1 / ((n:ℝ) + 1) ^ 2) := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
      rw [mul_pow]
      field_simp
    rw [hsplit] at hdecay
    exact hdecay
  · -- negative part: `n : ℕ`, `‖fourierCoeff (reflCircle f) (-(n+1))‖`.
    -- evenness: `fco (reflC f) (-(n+1)) = fco (reflC f) (n+1)`.
    have heven : ∀ n : ℕ,
        ‖fourierCoeff (reflCircle f) (-((n : ℤ) + 1))‖
          = ‖fourierCoeff (reflCircle f) ((n : ℤ) + 1)‖ := by
      intro n
      have hneg : fourierCoeff (reflCircle f) (-((n : ℤ) + 1))
          = fourierCoeff (reflCircle f) ((n : ℤ) + 1) := by
        rw [fourierCoeff_reflCircle, fourierCoeff_reflCircle, ← fco_neg f hfcont ((n : ℤ) + 1)]
      rw [hneg]
    -- so the negative part equals the positive (shifted) part, which is summable.
    -- Positive shifted-by-1 summability:
    have hpos1 : Summable fun n : ℕ => ‖fourierCoeff (reflCircle f) ((n : ℤ) + 1)‖ := by
      have hmaj : Summable fun n : ℕ =>
          (M / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
        have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
          have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
          simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
        exact hp2.mul_left _
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmaj
      intro n
      have hfc : fourierCoeff (reflCircle f) ((n : ℤ) + 1)
          = ((∫ x in (0:ℝ)..1, Real.cos (((n:ℝ)+1) * Real.pi * x) * f x : ℝ) : ℂ) := by
        have : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, fourierCoeff_reflCircle, fco_eq_ofReal f hfcont]
        norm_cast
      rw [hfc, Complex.norm_real, Real.norm_eq_abs]
      have hdecay := cosineCoeff_decay hf htend0 htend1 hbc0 hbc1 hMnonneg hMbound
        (n := n + 1) (Nat.le_add_left 1 n)
      have hcast : ((↑(n + 1) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hdecay
      have hsplit : M / (((n:ℝ) + 1) * Real.pi) ^ 2
          = (M / Real.pi ^ 2) * (1 / ((n:ℝ) + 1) ^ 2) := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
        rw [mul_pow]
        field_simp
      rw [hsplit] at hdecay
      exact hdecay
    exact hpos1.congr (fun n => (heven n).symm)

end

end ShenWork.IntervalCosineCoeffDecay
