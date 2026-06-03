/-
  ShenWork/PDE/IntervalWeakCosineIBP.lean

  Weak cosine eigenfunction IBP and L∞-based O(1/k²) decay.

  For a bounded function f on [0,1], if f can be approximated by
  C²-Neumann functions with uniformly bounded Laplacian coefficients,
  then |f̂_k| ≤ C/(kπ)².

  The main application: ν·u^γ for the mild solution satisfies this
  because the Picard iterates are smooth and converge uniformly.
-/
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.IntervalCosineCoeffDecay

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.IntervalWeakCosineIBP

open ShenWork.IntervalCosineCoeffDecay
open ShenWork.IntervalEllipticCharacterization

/-- **Cosine coefficient decay by uniform approximation.**  If `f`
is the uniform limit of functions `f_n` each satisfying the
C²-Neumann cosine coefficient decay `|∫cos·f_n| ≤ C/(kπ)²` with
a UNIFORM constant C, then the same bound holds for `f`.

This bypasses the C² regularity requirement on `f` itself. -/
theorem cosineCoeff_decay_of_uniform_limit
    {f : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hf_int : IntervalIntegrable f volume (0 : ℝ) 1)
    (happrox : ∀ ε > 0, ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume (0 : ℝ) 1 ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, |f x - g x| ≤ ε) ∧
      (∀ k : ℕ, 1 ≤ k →
        |∫ x in (0:ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g x| ≤
          C / ((k:ℝ) * Real.pi) ^ 2)) :
    ∀ k : ℕ, 1 ≤ k →
      |∫ x in (0:ℝ)..1,
        Real.cos ((k:ℝ) * Real.pi * x) * f x| ≤
        C / ((k:ℝ) * Real.pi) ^ 2 := by
  intro k hk
  -- For any ε > 0, approximate f by g with |f-g| ≤ ε and |∫cos·g| ≤ C/(kπ)².
  -- Then |∫cos·f| ≤ |∫cos·g| + |∫cos·(f-g)| ≤ C/(kπ)² + ε.
  -- Since ε is arbitrary, |∫cos·f| ≤ C/(kπ)².
  have hkpi_pos : (0:ℝ) < (k:ℝ) * Real.pi := by positivity
  have hkpi_sq_pos : (0:ℝ) < ((k:ℝ) * Real.pi) ^ 2 := by positivity
  rw [← not_lt]; intro hlt
  set gap := |∫ x in (0:ℝ)..1,
    Real.cos ((k:ℝ) * Real.pi * x) * f x| -
    C / ((k:ℝ) * Real.pi) ^ 2
  have hgap : 0 < gap := by linarith
  obtain ⟨g, hg_int, hclose, hg⟩ := happrox (gap / 2) (by linarith)
  have hcos_cont :
      ContinuousOn (fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x))
        (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hfcos_int :
      IntervalIntegrable
        (fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x) * f x)
        volume (0 : ℝ) 1 :=
    hf_int.continuousOn_mul hcos_cont
  have hgcos_int :
      IntervalIntegrable
        (fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x) * g x)
        volume (0 : ℝ) 1 :=
    hg_int.continuousOn_mul hcos_cont
  have hdiffcos_int :
      IntervalIntegrable
        (fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x))
        volume (0 : ℝ) 1 := by
    refine (hfcos_int.sub hgcos_int).congr (fun x _hx => ?_)
    ring
  have hdiff : |∫ x in (0:ℝ)..1,
      Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x)| ≤ gap / 2 := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := gap / 2)
      (f := fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x))
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
          have hx_uIcc : x ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hx
          rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_uIcc
        calc |Real.cos ((k:ℝ) * Real.pi * x)| * |f x - g x|
            ≤ 1 * |f x - g x| :=
              mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
                (abs_nonneg _)
          _ ≤ gap / 2 := by
              simpa using hclose x hxIcc)
    simpa [Real.norm_eq_abs] using hnorm
  have hsplit : (∫ x in (0:ℝ)..1,
      Real.cos ((k:ℝ) * Real.pi * x) * f x) =
    (∫ x in (0:ℝ)..1,
      Real.cos ((k:ℝ) * Real.pi * x) * g x) +
    (∫ x in (0:ℝ)..1,
      Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x)) := by
    calc
      (∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * f x)
          = ∫ x in (0:ℝ)..1,
              (Real.cos ((k:ℝ) * Real.pi * x) * g x) +
                (Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x)) := by
            apply intervalIntegral.integral_congr
            intro x _hx
            ring
      _ = (∫ x in (0:ℝ)..1,
              Real.cos ((k:ℝ) * Real.pi * x) * g x) +
            (∫ x in (0:ℝ)..1,
              Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x)) := by
            rw [intervalIntegral.integral_add hgcos_int hdiffcos_int]
  have := calc
    |∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * f x|
      = |(∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * g x) +
        (∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x))| := by
        rw [hsplit]
    _ ≤ |∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * g x| +
        |∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * (f x - g x)| :=
        abs_add_le _ _
    _ ≤ C / ((k:ℝ) * Real.pi) ^ 2 + gap / 2 :=
        add_le_add (hg k hk) hdiff
  linarith

end ShenWork.IntervalWeakCosineIBP
